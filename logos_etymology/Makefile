# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr

SEED = examples/seed_facts.pl
FACTS = examples/lexeme_facts.pl examples/edge_facts.pl \
        examples/morpheme_facts.pl examples/sense_facts.pl

all: $(SEED) $(FACTS)

examples/seed_facts.pl: data/seed.tsv src/ingest.awk
	awk -f src/ingest.awk $< > $@
examples/lexeme_facts.pl: data/lexemes.tsv src/ingest.awk
	awk -v kind=lexeme -f src/ingest.awk $< > $@
examples/edge_facts.pl: data/edges.tsv src/ingest.awk
	awk -v kind=edge -f src/ingest.awk $< > $@
examples/morpheme_facts.pl: data/morphemes.tsv src/ingest.awk
	awk -v kind=morpheme -f src/ingest.awk $< > $@
examples/sense_facts.pl: data/senses.tsv src/ingest.awk
	awk -v kind=sense -f src/ingest.awk $< > $@

# Open the rules and the sourced fact files in SWI-Prolog. The seed words are placeholders and load on their own.
query: all
	swipl -q -s src/axioms.pl $(foreach f,$(FACTS),-s $(f))

clean:
	rm -f $(SEED) $(FACTS)
