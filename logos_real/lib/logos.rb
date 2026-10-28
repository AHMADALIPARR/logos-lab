# frozen_string_literal: true
require 'json'
require 'digest'
require 'optparse'
require 'rexml/document'
require 'set'

module Logos
  VERSION = '1.0.0'
  class Invalid < StandardError; end
  class Limit < StandardError; end

  module Canon
    module_function
    def text(value)
      value.to_s.unicode_normalize(:nfc)
    end
    def id(*parts)
      Digest::SHA256.hexdigest(parts.map { |x| text(x) }.join("\u001f"))[0, 24]
    end
    def graphemes(value)
      text(value).scan(/\X/)
    end
    def atom(value)
      "'" + text(value).each_char.map { |c|
        case c
        when "'" then "''"
        when "\\" then "\\\\"
        when "\n" then "\\n"
        when "\r" then "\\r"
        else c
        end
      }.join + "'"
    end
    def json(value)
      JSON.generate(value)
    end
  end

  class Store
    attr_reader :entries, :senses, :relations, :slices, :sources
    def initialize
      @entries = {}; @senses = {}; @relations = {}; @slices = {}; @sources = {}; @evidence = {}
    end
    def source(name:, locator:, license: 'unknown', kind: 'dataset')
      raise Invalid, 'empty source locator' if locator.to_s.empty?
      id = Canon.id('source', name, locator)
      @sources[id] = {'id'=>id, 'name'=>name, 'locator'=>locator, 'license'=>license, 'kind'=>kind}
      id
    end
    def evidence_records = @evidence
    def evidence(source_id:, reference:, statement:, confidence: 'reported')
      raise Invalid, 'missing source' unless @sources.key?(source_id)
      raise Invalid, 'empty reference' if reference.to_s.empty?
      raise Invalid, 'empty statement' if statement.to_s.empty?
      id = Canon.id('evidence', source_id, reference, statement)
      @evidence[id] = {'id'=>id, 'source'=>source_id, 'reference'=>reference, 'statement'=>statement, 'confidence'=>confidence}
      id
    end
    def entry(word:, lang:, pos: 'unknown', etymology_number: 0, evidence_id:)
      raise Invalid, 'missing evidence' unless @evidence.key?(evidence_id)
      word = Canon.text(word); lang = Canon.text(lang)
      raise Invalid, 'empty word or language' if word.empty? || lang.empty?
      id = Canon.id('entry', word, lang, pos, etymology_number)
      @entries[id] ||= {'id'=>id, 'word'=>word, 'lang'=>lang, 'pos'=>pos, 'etymology_number'=>etymology_number, 'evidence'=>[]}
      @entries[id]['evidence'] |= [evidence_id]
      id
    end
    def sense(entry_id:, gloss:, index:, evidence_id:)
      validate_entry_evidence(entry_id, evidence_id)
      id = Canon.id('sense', entry_id, index, gloss)
      @senses[id] = {'id'=>id, 'entry'=>entry_id, 'gloss'=>Canon.text(gloss), 'index'=>index, 'evidence'=>evidence_id}
      id
    end
    def relation(from:, to:, type:, evidence_id:, status: 'attested')
      validate_entry_evidence(from, evidence_id)
      raise Invalid, 'missing target' unless @entries.key?(to)
      raise Invalid, 'self-derivation' if from == to && type == 'derived_from'
      allowed = %w[derived_from borrowed_from inherited_from cognate_with variant_of compound_of related_to]
      raise Invalid, "unknown relation #{type}" unless allowed.include?(type)
      id = Canon.id('relation', from, to, type, evidence_id)
      @relations[id] = {'id'=>id, 'from'=>from, 'to'=>to, 'type'=>type, 'evidence'=>evidence_id, 'status'=>status}
      id
    end
    def slice(entry_id:, layer:, index:, value:, evidence_id:, start: nil, stop: nil, label: nil)
      validate_entry_evidence(entry_id, evidence_id)
      allowed = %w[orthographic morphological phonological etymological semantic]
      raise Invalid, "unknown layer #{layer}" unless allowed.include?(layer)
      id = Canon.id('slice', entry_id, layer, index, value, evidence_id)
      @slices[id] = {'id'=>id, 'entry'=>entry_id, 'layer'=>layer, 'index'=>index, 'value'=>Canon.text(value), 'start'=>start, 'stop'=>stop, 'label'=>label, 'evidence'=>evidence_id}
      id
    end
    def orthography(entry_id, evidence_id)
      word = @entries.fetch(entry_id).fetch('word')
      offset = 0
      Canon.graphemes(word).each_with_index do |g, i|
        slice(entry_id: entry_id, layer: 'orthographic', index: i, value: g, start: offset, stop: offset + g.length, evidence_id: evidence_id)
        offset += g.length
      end
    end
    def validate_entry_evidence(entry_id, evidence_id)
      raise Invalid, 'missing entry' unless @entries.key?(entry_id)
      raise Invalid, 'missing evidence' unless @evidence.key?(evidence_id)
    end
    def verify!
      @entries.each_value do |entry|
        gs = @slices.values.select { |s| s['entry'] == entry['id'] && s['layer'] == 'orthographic' }.sort_by { |s| s['index'] }
        raise Invalid, "orthography mismatch: #{entry['word']}" unless gs.map { |s| s['value'] }.join == entry['word']
        raise Invalid, 'noncontiguous slices' unless gs.each_index.all? { |i| gs[i]['index'] == i }
        raise Invalid, 'entry lacks evidence' if entry['evidence'].empty?
      end
      @relations.each_value do |r|
        raise Invalid, 'dangling relation' unless @entries.key?(r['from']) && @entries.key?(r['to']) && @evidence.key?(r['evidence'])
      end
      true
    end
    def counts
      {sources: @sources.size, evidence: @evidence.size, entries: @entries.size, senses: @senses.size, slices: @slices.size, relations: @relations.size}
    end
    def save(path)
      verify!
      data = {'version'=>VERSION, 'sources'=>@sources.values, 'evidence'=>@evidence.values, 'entries'=>@entries.values, 'senses'=>@senses.values, 'slices'=>@slices.values, 'relations'=>@relations.values}
      File.write(path, JSON.pretty_generate(data) + "\n")
    end
    def self.load(path)
      data = JSON.parse(File.read(path)); db = new
      {'sources'=>:sources, 'evidence'=>:evidence, 'entries'=>:entries, 'senses'=>:senses, 'slices'=>:slices, 'relations'=>:relations}.each do |field, attr|
        (data[field] || []).each { |row| (attr == :evidence ? db.evidence_records : db.public_send(attr))[row.fetch('id')] = row }
      end
      db.verify!; db
    end
  end

  class Wiktextract
    def initialize(store, source_id, strict: false)
      @store = store; @source_id = source_id; @strict = strict
    end
    def ingest(io, max: nil)
      processed = 0; rejected = 0
      io.each_line.with_index(1) do |line, number|
        next if line.strip.empty?
        begin
          row = JSON.parse(line)
          ingest_row(row, number)
          processed += 1
          break if max && processed >= max
        rescue JSON::ParserError, KeyError, Invalid, TypeError => e
          raise Invalid, "line #{number}: #{e.message}" if @strict
          rejected += 1
        end
      end
      {processed: processed, rejected: rejected}
    end
    def ingest_row(row, line_number)
      word = row.fetch('word'); lang = row['lang_code'] || row.fetch('lang')
      pos = row['pos'] || 'unknown'; etym = row['etymology_number'] || 0
      reference = "jsonl:#{line_number}:#{lang}:#{word}:#{pos}"
      ev = @store.evidence(source_id: @source_id, reference: reference, statement: 'Wiktextract lexical record')
      id = @store.entry(word: word, lang: lang, pos: pos, etymology_number: etym, evidence_id: ev)
      @store.orthography(id, ev)
      Array(row['senses']).each_with_index do |sense, i|
        next unless sense.is_a?(Hash)
        Array(sense['glosses']).each_with_index do |gloss, j|
          @store.sense(entry_id: id, gloss: gloss, index: "#{i}.#{j}", evidence_id: ev)
        end
      end
      # Only explicit segmentation fields are treated as morphology.
      Array(row['morphemes']).each_with_index do |m, i|
        next unless m.is_a?(Hash) && m['form']
        @store.slice(entry_id: id, layer: 'morphological', index: i, value: m['form'], label: m['type'], evidence_id: ev)
      end
      Array(row['sounds']).each_with_index do |sound, i|
        next unless sound.is_a?(Hash) && sound['ipa']
        @store.slice(entry_id: id, layer: 'phonological', index: i, value: sound['ipa'], label: 'ipa', evidence_id: ev)
      end
      # Preserve raw etymology as a textual claim, not an invented derivation edge.
      if row['etymology_text'].is_a?(String) && !row['etymology_text'].empty?
        @store.slice(entry_id: id, layer: 'etymological', index: 0, value: row['etymology_text'], label: 'unparsed_claim', evidence_id: ev)
      end
      id
    end
  end

  class Perseus
    def initialize(store, source_id)
      @store = store; @source_id = source_id
    end
    def ingest(xml)
      doc = REXML::Document.new(xml)
      count = 0
      REXML::XPath.each(doc, "//*[local-name()='entry' or local-name()='entryFree']") do |node|
        word = node.attributes['key'] || node.attributes['n']
        next unless word && !word.empty?
        lang = node.attributes['xml:lang'] || node.attributes['lang'] || 'und'
        ev = @store.evidence(source_id: @source_id, reference: "tei:#{count}:#{word}", statement: 'TEI lexical entry')
        id = @store.entry(word: word, lang: lang, evidence_id: ev)
        @store.orthography(id, ev)
        idx = 0
        REXML::XPath.each(node, ".//*[local-name()='def']") do |definition|
          gloss = extract_text(definition).strip
          next if gloss.empty?
          @store.sense(entry_id: id, gloss: gloss, index: idx, evidence_id: ev)
          idx += 1
        end
        count += 1
      end
      count
    end
    def extract_text(node)
      node.children.map { |c| c.is_a?(REXML::Text) ? c.value : (c.is_a?(REXML::Element) ? extract_text(c) : '') }.join
    end
  end

  class Relations
    def initialize(store)
      @db = store
      @out = Hash.new { |h,k| h[k] = [] }
      @db.relations.each_value { |r| @out[r['from']] << r }
    end
    def ancestors(id, max_depth: 32, types: %w[derived_from inherited_from borrowed_from])
      raise Invalid, 'unknown entry' unless @db.entries.key?(id)
      result = []; queue = [[id, [], 0]]; visited = Set.new([id])
      until queue.empty?
        node, path, depth = queue.shift
        next if depth >= max_depth
        @out[node].each do |r|
          next unless types.include?(r['type'])
          next if visited.include?(r['to'])
          visited.add(r['to'])
          new_path = path + [r]
          result << {'entry'=>r['to'], 'depth'=>depth+1, 'proof'=>new_path.map { |e| e['id'] }, 'evidence'=>new_path.map { |e| e['evidence'] }}
          queue << [r['to'], new_path, depth+1]
        end
      end
      result
    end
    def shared_ancestors(a,b)
      left = ancestors(a).to_h { |r| [r['entry'], r] }
      right = ancestors(b).to_h { |r| [r['entry'], r] }
      (left.keys & right.keys).map { |id| {'entry'=>id, 'left'=>left[id], 'right'=>right[id]} }
    end
    def by_word(word, lang = nil)
      @db.entries.values.select { |e| e['word'] == Canon.text(word) && (!lang || e['lang'] == lang) }
    end
  end

  class Prolog
    def initialize(store)
      @db = store
    end
    def emit(io)
      @db.sources.values.sort_by { |x| x['id'] }.each { |r| fact(io, 'source', r.values_at('id','name','locator','license','kind')) }
      @db.evidence_records.values.sort_by { |x| x['id'] }.each { |r| fact(io, 'evidence', r.values_at('id','source','reference','statement','confidence')) }
      @db.entries.values.sort_by { |x| x['id'] }.each { |r| fact(io, 'lexeme', r.values_at('id','word','lang','pos','etymology_number')) }
      @db.entries.values.each { |r| r['evidence'].each { |ev| fact(io, 'lexeme_evidence', [r['id'],ev]) } }
      @db.senses.values.sort_by { |x| x['id'] }.each { |r| fact(io, 'sense', r.values_at('id','entry','gloss','index','evidence')) }
      @db.slices.values.sort_by { |x| [x['entry'],x['layer'],x['index']] }.each { |r| fact(io, 'slice', r.values_at('entry','layer','index','value','start','stop','label','evidence')) }
      @db.relations.values.sort_by { |x| x['id'] }.each { |r| fact(io, 'relation', r.values_at('id','from','to','type','evidence','status')) }
      io.puts <<~PL
        ancestry(A,B,Proof) :- ancestry_walk(A,B,[A],Proof).
        ancestry_walk(A,B,_,[E]) :- relation(_,A,B,T,E,'attested'), ancestry_type(T).
        ancestry_walk(A,C,Visited,[E|Proof]) :-
          relation(_,A,B,T,E,'attested'),
          ancestry_type(T),
          \\+ memberchk(B,Visited),
          ancestry_walk(B,C,[B|Visited],Proof).
        ancestry_type('derived_from').
        ancestry_type('inherited_from').
        ancestry_type('borrowed_from').
      PL
    end
    def fact(io, name, values)
      encoded = values.map do |v|
        case v
        when NilClass then 'none'
        when Integer then v.to_s
        else Canon.atom(v)
        end
      end
      io.puts "#{name}(#{encoded.join(',')})."
    end
  end

  module Horn
    Var = Struct.new(:name)
    Fun = Struct.new(:name, :args)
    Clause = Struct.new(:head, :body)
    module_function
    def v(name) = Var.new(name)
    def f(name,*args) = Fun.new(name,args)
    def walk(term, subst)
      seen = Set.new
      while term.is_a?(Var) && subst.key?(term.name)
        raise Invalid, 'cyclic substitution' if seen.include?(term.name)
        seen.add(term.name)
        term = subst.fetch(term.name)
      end
      term
    end
    def occurs?(var, term, subst)
      term = walk(term,subst)
      return var.name == term.name if term.is_a?(Var)
      return term.args.any? { |x| occurs?(var,x,subst) } if term.is_a?(Fun)
      false
    end
    def unify(a,b,subst)
      a = walk(a,subst); b = walk(b,subst)
      return subst if a == b
      if a.is_a?(Var)
        return nil if occurs?(a,b,subst)
        return subst.merge(a.name=>b)
      end
      if b.is_a?(Var)
        return nil if occurs?(b,a,subst)
        return subst.merge(b.name=>a)
      end
      return nil unless a.is_a?(Fun) && b.is_a?(Fun) && a.name == b.name && a.args.length == b.args.length
      a.args.zip(b.args).each do |x,y|
        subst = unify(x,y,subst)
        return nil unless subst
      end
      subst
    end
    def rename(term, suffix)
      return Var.new("#{term.name}@#{suffix}") if term.is_a?(Var)
      return Fun.new(term.name,term.args.map { |x| rename(x,suffix) }) if term.is_a?(Fun)
      term
    end
    def resolve(term,subst)
      term = walk(term,subst)
      return Fun.new(term.name,term.args.map { |x| resolve(x,subst) }) if term.is_a?(Fun)
      term
    end
    class Engine
      def initialize(clauses, max_steps: 100_000, max_depth: 64)
        @max_steps=max_steps; @max_depth=max_depth; @serial=0
        @index=Hash.new { |h,k| h[k]=[] }
        clauses.each { |c| @index[[c.head.name,c.head.args.length]] << c }
      end
      def query(goals, limit: 100)
        @steps=0; results=[]
        dfs(goals,{},0,results,limit)
        results
      end
      def dfs(goals,subst,depth,results,limit)
        return if results.length >= limit
        if goals.empty?
          results << subst; return
        end
        return if depth >= @max_depth
        first,*rest=goals
        @index[[first.name,first.args.length]].each do |clause|
          @steps+=1
          raise Limit,'resolution step budget exhausted' if @steps > @max_steps
          @serial+=1; suffix=@serial
          head=Horn.rename(clause.head,suffix)
          next_subst=Horn.unify(first,head,subst)
          next unless next_subst
          body=clause.body.map { |g| Horn.rename(g,suffix) }
          dfs(body+rest,next_subst,depth+1,results,limit)
          return if results.length >= limit
        end
      end
    end
  end
end
