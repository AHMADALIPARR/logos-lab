require 'minitest/autorun'
require 'stringio'
require_relative '../lib/logos'
class LogosTest < Minitest::Test
  def setup
    @db=Logos::Store.new
    @source=@db.source(name:'test',locator:'test-fixture')
    @ev=@db.evidence(source_id:@source,reference:'row:1',statement:'fixture')
  end
  def add(word)
    id=@db.entry(word:word,lang:'en',evidence_id:@ev)
    @db.orthography(id,@ev)
    id
  end
  def test_graphemes_roundtrip
    %w[café naïve reconstruction].each { |w| add(w) }
    add("a\u0301")
    assert @db.verify!
  end
  def test_inference_proof
    a=add('a');b=add('b');c=add('c')
    @db.relation(from:a,to:b,type:'derived_from',evidence_id:@ev)
    @db.relation(from:b,to:c,type:'borrowed_from',evidence_id:@ev)
    path=Logos::Relations.new(@db).ancestors(a).find { |x| x['entry']==c }
    assert_equal 2,path['depth']; assert_equal 2,path['proof'].length
  end
  def test_provenance_required
    assert_raises(Logos::Invalid) { @db.entry(word:'bad',lang:'en',evidence_id:'fake') }
  end
  def test_cycle_terminates
    a=add('a');b=add('b')
    @db.relation(from:a,to:b,type:'derived_from',evidence_id:@ev)
    @db.relation(from:b,to:a,type:'derived_from',evidence_id:@ev)
    assert_equal 1,Logos::Relations.new(@db).ancestors(a).size
  end
  def test_jsonl_import
    text=File.read(File.expand_path('../examples/sample.jsonl',__dir__))
    assert_equal 2,Logos::Wiktextract.new(@db,@source).ingest(StringIO.new(text.force_encoding('UTF-8')))[:processed]
    assert_equal 2,@db.entries.size
    assert @db.verify!
  end
  def test_horn_unification
    h=Logos::Horn
    x=h.v('X'); y=h.v('Y')
    subst=h.unify(h.f('pair',x,2),h.f('pair',1,y),{})
    assert_equal 1,h.resolve(x,subst)
    assert_equal 2,h.resolve(y,subst)
  end
  def test_horn_occurs_check
    h=Logos::Horn; x=h.v('X')
    assert_nil h.unify(x,h.f('loop',x),{})
  end
  def test_horn_resolution
    h=Logos::Horn
    clauses=[h::Clause.new(h.f('parent','a','b'),[]),h::Clause.new(h.f('parent','b','c'),[]),h::Clause.new(h.f('ancestor',h.v('X'),h.v('Y')),[h.f('parent',h.v('X'),h.v('Y'))]),h::Clause.new(h.f('ancestor',h.v('X'),h.v('Y')),[h.f('parent',h.v('X'),h.v('Z')),h.f('ancestor',h.v('Z'),h.v('Y'))])]
    q=h.v('Q'); answers=h::Engine.new(clauses).query([h.f('ancestor','a',q)])
    assert_equal %w[b c],answers.map { |s| h.resolve(q,s) }.sort
  end
  def test_prolog_export
    add("o'brien")
    output=StringIO.new
    Logos::Prolog.new(@db).emit(output)
    assert_includes output.string, "o''brien"
  end
  def test_save_load
    add('alpha');require 'tempfile'
    Tempfile.create(['logos','.json']) { |f| @db.save(f.path); assert_equal @db.counts,Logos::Store.load(f.path).counts }
  end
end
