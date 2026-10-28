## SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
## Copyright Ahmad Ali Parr
##
## ingest.awk — The Logos Ingest
##
## Etymology: *leg-* (Proto-Indo-European: to gather) → Greek legein → logos.
## The ingest GATHERS. A row goes in as a fact only if it carries a source.
##
## POSIX awk. One script, four kinds of table, chosen with -v kind=...
## The default kind is lexeme, so the old command still works unchanged.
##
## Usage:
##   $ awk -f src/ingest.awk data/seed.tsv                       > examples/seed_facts.pl
##   $ awk -v kind=lexeme   -f src/ingest.awk data/lexemes.tsv   > examples/lexeme_facts.pl
##   $ awk -v kind=edge     -f src/ingest.awk data/edges.tsv     > examples/edge_facts.pl
##   $ awk -v kind=morpheme -f src/ingest.awk data/morphemes.tsv > examples/morpheme_facts.pl
##   $ awk -v kind=sense    -f src/ingest.awk data/senses.tsv    > examples/sense_facts.pl
##
## ── Tables ────────────────────────────────────────────────────────────────────
##
##   lexeme    id, language, word, etymology, source
##               → lexeme/3, etymology_text/3, one orthographic_slice/3 per letter
##   edge      descendant, ancestor, source
##               → derived_from/3
##   morpheme  id, position, form, kind, source
##               → morpheme/5
##   sense     id, sense, gloss, source
##               → sense/4
##
## ── Evidence rule ─────────────────────────────────────────────────────────────
##
## Identifiers, languages, kinds and sources must be letters, digits or _.
## A row that breaks that is dropped.
## For edge, morpheme and sense the source seed_unverified is not evidence,
## so those rows are dropped too. Only lexeme rows may carry it, because a
## lexeme row asserts a word exists, not where it came from.
## This is an exact orthographic slice, NOT a morphological segmentation.

BEGIN {
 FS="\t"; OFS="\t"
 if (kind == "") kind = "lexeme"
 if (kind != "lexeme" && kind != "edge" && kind != "morpheme" && kind != "sense") {
  print "ingest.awk: unknown kind " kind > "/dev/stderr"; bad = 1; exit 1
 }
 if (kind == "lexeme") print ":- discontiguous lexeme/3, etymology_text/3, orthographic_slice/3."
}

NR==1 { next }

## ── Branch 1: lexeme ──────────────────────────────────────────────────────────
kind=="lexeme" && NF>=5 {
 id=$1; lang=$2; word=$3; etym=$4; source=$5
 if(id !~ /^[A-Za-z0-9_]+$/ || lang !~ /^[A-Za-z0-9_]+$/ || source !~ /^[A-Za-z0-9_]+$/) next
 printf "lexeme(%s,%s,",id,lang; atom(word); printf ").\n"
 printf "etymology_text(%s,",id; atom(etym); printf ",%s).\n",source
 n=length(word)
 for(i=1;i<=n;i++) { printf "orthographic_slice(%s,%d,",id,i; atom(substr(word,i,1)); printf ").\n" }
 next
}

## ── Branch 2: edge ────────────────────────────────────────────────────────────
kind=="edge" && NF>=3 {
 if($1 !~ /^[A-Za-z0-9_]+$/ || $2 !~ /^[A-Za-z0-9_]+$/ || $3 !~ /^[A-Za-z0-9_]+$/) next
 if($3 == "seed_unverified") next
 printf "derived_from(%s,%s,%s).\n",$1,$2,$3
 next
}

## ── Branch 3: morpheme ────────────────────────────────────────────────────────
kind=="morpheme" && NF>=5 {
 if($1 !~ /^[A-Za-z0-9_]+$/ || $2 !~ /^[0-9]+$/ || $4 !~ /^[A-Za-z0-9_]+$/ || $5 !~ /^[A-Za-z0-9_]+$/) next
 if($5 == "seed_unverified") next
 printf "morpheme(%s,%d,",$1,$2; atom($3); printf ",%s,%s).\n",$4,$5
 next
}

## ── Branch 4: sense ───────────────────────────────────────────────────────────
kind=="sense" && NF>=4 {
 if($1 !~ /^[A-Za-z0-9_]+$/ || $2 !~ /^[A-Za-z0-9_]+$/ || $4 !~ /^[A-Za-z0-9_]+$/) next
 if($4 == "seed_unverified") next
 printf "sense(%s,%s,",$1,$2; atom($3); printf ",%s).\n",$4
 next
}

## Quote a value as a Prolog atom: escape backslashes and single quotes.
function atom(s, t) { t=s; gsub(/\\/,"\\\\",t); gsub(/\047/,"\047\047",t); printf "\047%s\047",t }
