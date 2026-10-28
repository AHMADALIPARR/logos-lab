# Logos Etymology

Word tables go in as tab-separated files and come out as Prolog facts. The rules in `src/axioms.pl` then answer questions about where a word came from.

## Tables

| File | Columns | Becomes |
|---|---|---|
| `data/lexemes.tsv` | id, language, word, etymology, source | `lexeme/3`, `etymology_text/3`, `orthographic_slice/3` |
| `data/edges.tsv` | descendant, ancestor, source | `derived_from/3` |
| `data/morphemes.tsv` | id, position, form, kind, source | `morpheme/5` |
| `data/senses.tsv` | id, sense, gloss, source | `sense/4` |
| `data/seed.tsv` | id, language, word, etymology, source | placeholder words, source `seed_unverified` |

A row with no usable source is dropped, and `seed_unverified` never counts as evidence for an edge, a morpheme or a sense.

## Run

```sh
make          # writes the fact files into examples/
make query    # opens SWI-Prolog with the rules and the sourced facts
```

## Questions

```prolog
?- ancestor_via(en_logic, Ancestor, Sources).
?- shared_root(WordA, WordB, Root).
?- shared_ancestor(en_logic, en_logos, Ancestor).
?- segmentation(en_reconstruction, Forms).
?- gloss(grc_logos, Gloss).
?- spelling(en_logos, Letters).
```

## Sources

| Source | Page |
|---|---|
| `wiktionary_logic` | https://en.wiktionary.org/wiki/logic |
| `wiktionary_logos_en` | https://en.wiktionary.org/wiki/logos |
| `wiktionary_logos_grc` | https://en.wiktionary.org/wiki/λόγος |
| `wiktionary_lego_grc` | https://en.wiktionary.org/wiki/λέγω |
| `wiktionary_reconstruction` | https://en.wiktionary.org/wiki/reconstruction |

Other places to pull from: [Kaikki raw Wiktextract](https://kaikki.org/dictionary/rawdata.html), [Wikimedia dumps](https://dumps.wikimedia.org/enwiktionary/), [Perseus TEI lexica](https://github.com/PerseusDL/lexica).
