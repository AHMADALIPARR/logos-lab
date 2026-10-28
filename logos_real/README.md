# LOGOS

Requires Ruby 3.2+ with standard libraries `json`, `digest`, `rexml`, `csv`, `set`, and `optparse`.

```sh
ruby test/test.rb
bin/logos ingest-jsonl examples/sample.jsonl examples/corpus.json
bin/logos verify examples/corpus.json
bin/logos export-prolog examples/corpus.json examples/corpus.pl
bin/logos query examples/corpus.json logic en
bin/logos ingest-tei examples/sample.xml examples/tei.json
```

Input: Wiktextract JSONL or TEI XML. Output: provenance-bearing JSON knowledge graph and Prolog facts. A source record is not proof that an etymological claim is correct. Explicit morpheme annotations are imported; otherwise no morphological boundaries are guessed. Unparsed etymology prose is retained as text, not converted into unsupported derivation edges. Curated derivations can be added with `bin/add-relations` using the TSV header in `examples/relations.tsv`.

The internal Horn engine implements unification with occurs check and bounded depth-first SLD-style resolution. It is independent of an external Prolog engine. The exported `.pl` facts can be loaded by a Prolog runtime. TEI support targets `entry` and `entryFree` nodes and `def` glosses; it is not a complete TEI lexicon implementation.

No actual historical dictionary corpus is bundled. The sample data are fixtures, not verified historical attestations. The WhyML proof backend and automatic derivation-edge extraction are not implemented.
