# logos-lab

A small workshop for logic programming: a proof-ready port of a logic engine, five tiny example programs in five different logic languages, a word-origins compiler, and a careful archive for collecting old Prolog, ALGOL, COBOL and JOVIAL source.

## What's inside

| Folder | What it is |
|---|---|
| [`logos_whyml/`](logos_whyml/) | `Logos.mlw`, a port of the microKanren unifier and goal interpreter into WhyML, the language the Why3 prover reads. It also sketches a friendlier syntax for relations, queries and weighted facts. |
| [`logic_kernels/`](logic_kernels/) | Five minimal starting programs, one each for Metagol, Twelf, Boogie, Logica and DLV. |
| [`logos_etymology/`](logos_etymology/) | A starter compiler for word origins. An AWK script slices each word into letters, Prolog rules relate the words, and a WhyML file holds the typed specification. A seed list of words is included. |
| [`legacy-logic-archive/`](legacy-logic-archive/) | Scripts and source lists for collecting historical code the right way: every file is stored under its SHA-256 fingerprint, with a record of where it came from and what its rights are. |

## The pieces

**Logos** takes the heart of a small logic engine, the part that matches terms and searches for answers, and writes it so a prover can check it. Run it with `why3 prove Logos.mlw`.

**The five kernels** are the same idea, a few lines each, in five systems: Metagol learns programs from examples, Twelf searches for proofs, Boogie checks programs, Logica turns rules into SQL, and DLV solves choice problems. Each file says how to run it.

**The etymology compiler** reads a table of words with their origins and turns it into Prolog facts: `awk -f src/ingest.awk data/seed.tsv > examples/seed_facts.pl`, then `swipl -q -s src/axioms.pl -s examples/seed_facts.pl`.

**The archive** only collects sources that have been approved, and records a fingerprint, the web address, the size, the time and the rights for each one. `bin/verify.sh` re-checks every stored file. The research notes cover ALGOL, COBOL II, Prolog, NASA Prolog work, VHDL and BASIC magazines, Ada aerospace code, and the Mark I Perceptron.

## Try it

```sh
cd legacy-logic-archive
bash bin/verify.sh          # re-hash everything stored
bash bin/ingest.sh ALGOL https://example.org/source ./downloaded-file
```

Each folder has its own README with the details.
