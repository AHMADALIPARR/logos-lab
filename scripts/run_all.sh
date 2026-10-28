#!/bin/sh
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr
# Runs every part of logos-lab at the same time, one job per part, and prints
# each part's answers. The parts share no state, so the order does not matter.
#
#   sh scripts/run_all.sh          all parts at once
#   JOBS=2 sh scripts/run_all.sh   at most two at a time
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
OUT=$(mktemp -d)
JOBS=${JOBS:-$(nproc)}
export ROOT OUT


cat > "$OUT/jobs" <<JOBS_EOF
etymology|logos_etymology|make -s clean all && swipl -q -s src/axioms.pl -s examples/lexeme_facts.pl -s examples/edge_facts.pl -s examples/morpheme_facts.pl -s examples/sense_facts.pl -g "forall(ancestor_via(en_logic,A,S),(write(A-S),nl))" -t halt
prolog_lexicon|logos_prolog|swipl -q -g "use_module(logos),logos:logos_selftest" -t halt
prolog_deduction|logos_prolog|swipl -q -g "use_module(logos_deduction),logos_deduction:deduction_tests" -t halt
logic_stack_mini_prolog|logic_stack/mini|swipl -q -g metagol -t halt logicstack.pl
logic_stack_full_prolog|logic_stack/full|swipl -q -g run -t halt logicstack_full.pl
logic_stack_mini_c|logic_stack/mini|sh -c 'gcc -O2 logicstack.c -o /tmp/ls_mini_c -lm && /tmp/ls_mini_c'
logic_stack_full_c|logic_stack/full|sh -c 'gcc -O2 logicstack.c -o /tmp/ls_full_c -lm && /tmp/ls_full_c'
logic_stack_mini_haskell|logic_stack/mini|sh -c 'D=\$(mktemp -d) && ghc -O2 -outputdir \$D -o \$D/ls LogicStack.hs >/dev/null && \$D/ls'
logic_stack_full_haskell|logic_stack/full|sh -c 'D=\$(mktemp -d) && ghc -O2 -outputdir \$D -o \$D/ls LogicStack.hs >/dev/null && \$D/ls'
exec_lock|exec_lock|swipl -q -g "use_module(trust_gate),demo" -t halt
boogie_ext|logic_kernels/boogie_ext|sh -c '. ./env.sh && make verify | tail -3 && git checkout -q VERIFY.log'
legacy_archive|legacy-logic-archive|sh bin/verify.sh
logic_stack_mini_ocaml|logic_stack/mini|sh -c 'D=\$(mktemp -d) && cp logicstack.ml \$D && (cd \$D && ocamlopt logicstack.ml -o ls >/dev/null 2>\&1 ) && \$D/ls'
logic_stack_full_ocaml|logic_stack/full|sh -c 'D=\$(mktemp -d) && cp logicstack.ml \$D && (cd \$D && ocamlopt logicstack.ml -o ls >/dev/null 2>\&1 ) && \$D/ls'
logos_real|logos_real|ruby test/test.rb
JOBS_EOF

while IFS='|' read -r name dir cmd; do
  printf '%s\0%s\0%s\0' "$name" "$dir" "$cmd"
done < "$OUT/jobs" | xargs -0 -n 3 -P "$JOBS" sh -c '
  ( cd "$ROOT/$1" && sh -c "$2" ) > "$OUT/$0.out" 2>&1; echo $? > "$OUT/$0.rc"'

for rc in "$OUT"/*.rc; do
  n=$(basename "$rc" .rc)
  echo "=== $n (exit $(cat "$rc"))"
  cat "$OUT/$n.out"
done
echo "outputs kept in $OUT"
