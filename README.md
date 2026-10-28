# logos-lab

Logic programming, from a unifier to a lexicon. Facts and rules go in, and answers come out by unification and search.

## The engine

[`logos_whyml/Logos.mlw`](logos_whyml/Logos.mlw) is a microKanren-style engine written in WhyML for Why3.

- **Terms:** variables, atoms, pairs and nil.
- **Substitutions:** a list of bindings. `walk` follows a variable through them, and `occurs` is the occurs check.
- **`unify`:** matches two terms and extends the substitution, or fails.
- **Goals:** `Success`, `Failure`, `Eq`, `Conj` (and), `Disj` (or) and `Delay`.
- **`solve`:** runs a goal against a substitution and returns every answer, with a fuel counter so every call ends.

## Five kernels

[`logic_kernels/`](logic_kernels/) shows one small program in each of five logic systems.

| File | System | What it does |
|---|---|---|
| `metagol.pl` | Metagol | Learns `ancestor/2` from `parent/2` and positive and negative examples |
| `twelf.elf` | Twelf | Proves `path a c` by chaining edges `a b` and `b c` |
| `boogie.bpl` | Boogie | Proves a loop sums 1 to n as n(n+1)/2, using loop invariants |
| `logica.l` | Logica | Two-hop reachability over a small graph, compiled to SQL |
| `dlv.dl` | DLV | Assigns each task to the CPU or the GPU, exactly one of the two |

## Etymology

[`logos_etymology/`](logos_etymology/) turns a word table into Prolog facts.

- `ingest.awk` reads `id, language, word, etymology, source` and writes `lexeme/3`, `etymology_text/3` and one `orthographic_slice/3` fact per letter.
- `axioms.pl` holds the rules: `ancestor/2` follows `derived_from/3` without looping, and `shared_root/3` links words that share a root morpheme.
- `LogosLexicon.mlw` is the typed model of a lexeme and its slices.
- Every derivation edge carries its source, so each answer traces back to evidence.

```sh
awk -f src/ingest.awk data/seed.tsv > examples/seed_facts.pl
swipl -q -s src/axioms.pl -s examples/seed_facts.pl
```

## Legacy logic archive

[`legacy-logic-archive/`](legacy-logic-archive/) stores historical Prolog, ALGOL, COBOL II and JOVIAL source by SHA-256 fingerprint. Each file has a record of its address, size, time and rights. `bin/collect.sh` fetches approved sources, `bin/verify.sh` re-hashes everything, and `research/` holds the notes on each phase, from NASA Prolog to the Mark I Perceptron.

```sh
cd legacy-logic-archive && bash bin/verify.sh
```
