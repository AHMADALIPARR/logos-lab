# LOGOS Etymology Compiler — bootstrap v0.1

This is an initial, executable orthographic slicer, a Prolog relational layer, and a small WhyML typed specification. **Not** a completed etymological parser or formally verified compiler.

## Sources
- Kaikki raw Wiktextract: https://kaikki.org/dictionary/rawdata.html
- Wikimedia source dumps: https://dumps.wikimedia.org/enwiktionary/
- Perseus TEI lexica: https://github.com/PerseusDL/lexica
- Skeat historical scan: https://commons.wikimedia.org/wiki/File:An_etymological_dictionary_of_the_English_language_(IA_etymologicaldict00skea_0).pdf

## Run
`awk -f src/ingest.awk data/seed.tsv > examples/seed_facts.pl`

`swipl -q -s src/axioms.pl -s examples/seed_facts.pl`

## Data contract
Input TSV: id, language, word, etymology, source. Identifiers must be alphanumeric/underscore. Each word is sliced into individual characters by POSIX awk; **Unicode codepoint/grapheme correctness is not guaranteed** under all awk implementations. Source `seed_unverified` is deliberately not evidence.

The parser does not infer roots, borrowing paths, cognates or semantic equivalence. Etymology text remains uninterpreted until separately parsed and supported by evidence. No dictionary corpus has yet been ingested into this package.

## Next implementation milestones
1. Streaming JSONL -> normalized TSV adapter (jq or equivalent, no Python).
2. TEI XML parser for Perseus, using an XML-aware parser.
3. Unicode grapheme segmentation and morpheme candidate generation.
4. Provenance-backed derivation edges, ambiguity and competing hypotheses.
5. WhyML contracts and Why3 proof obligations for reconstruction, index uniqueness and provenance.
6. Reproducible source hashes, corpus manifests, and tests.
