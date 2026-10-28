# logos-lab

A logic-programming prediction bot. It reasons with rules and facts, and uses logic engines and proof tools to work out what follows from what it knows.

## What's inside

| Folder | What it is |
|---|---|
| [`logos_whyml/`](logos_whyml/) | `Logos.mlw`, the bot's core: a microKanren-style unifier and goal interpreter written in WhyML for Why3. |
| [`logic_kernels/`](logic_kernels/) | Five small reasoning kernels, one each for Metagol, Twelf, Boogie, Logica and DLV. |
| [`logos_etymology/`](logos_etymology/) | Word-origins compiler: AWK slices words into letters, Prolog rules relate them, WhyML holds the typed specification. |
| [`legacy-logic-archive/`](legacy-logic-archive/) | Scripts and source lists for collecting historical Prolog, ALGOL, COBOL and JOVIAL code, stored by SHA-256 fingerprint with its origin and rights. |

## How it works

Facts and rules go in. The engine matches terms, searches for answers, and the bot predicts what follows. The kernels give it five different ways to reason: learning programs from examples (Metagol), proof search (Twelf), program checking (Boogie), rules to SQL (Logica), and choice problems (DLV).

## Run it

```sh
why3 prove logos_whyml/Logos.mlw

awk -f logos_etymology/src/ingest.awk logos_etymology/data/seed.tsv > /tmp/seed_facts.pl
swipl -q -s logos_etymology/src/axioms.pl -s /tmp/seed_facts.pl

cd legacy-logic-archive && bash bin/verify.sh
```

Each kernel in `logic_kernels/` is run with its own tool, for example `boogie boogie.bpl` or `dlv -filter=assign dlv.dl`.
