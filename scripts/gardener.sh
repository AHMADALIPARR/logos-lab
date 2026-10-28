#!/bin/sh
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr
#
# SWI-Prolog gardener -- production runner for the Prolog parts of logos-lab.
#
# What it does, one pass, no daemon, no restart loop:
#   * checks that swipl is present and records its version
#   * prunes stale WAM build output only (wam runs are rebuilt by make)
#   * runs each SWI-Prolog job from scripts/run_all.sh, one at a time,
#     with a 120-second timeout, capturing full output per job
#   * writes logs/<job>.log, logs/summary.txt and logs/status.txt
#   * prints a PASS/FAIL table and exits 1 if any job fails, 0 if all pass
#   * never hides a failure and never edits source files
#
# Deliberate gardener rule -- etymology facts are NOT regenerated here:
#   `make clean all` in logos_etymology re-runs ingest.awk, which in a
#   C locale splits multibyte Greek letters and rewrites
#   examples/lexeme_facts.pl with replacement characters. The gardener
#   therefore queries the committed facts as they are, and leaves
#   regeneration to a UTF-8-aware run by hand. See logs/etymology.log.
#
# Usage:
#   sh scripts/gardener.sh
#   GARDENER_LOGDIR=/var/log/logos-lab sh scripts/gardener.sh
#   Production: run it from cron or systemd on that schedule; read
#   logs/status.txt for the last pass (job, exit code, timestamp).
set -u

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
LOGDIR=${GARDENER_LOGDIR:-"$ROOT/logs/gardener"}
mkdir -p "$LOGDIR"
STAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)

if ! command -v swipl >/dev/null 2>&1; then
  echo "gardener: FAIL swipl not found on PATH" >&2
  echo "gardener: install SWI-Prolog 9.0.4 (Ubuntu noble .debs, see TOOLS note) and re-run" >&2
  exit 1
fi
SWIPL_VERSION=$(swipl --version 2>&1 | head -1)
echo "gardener: $SWIPL_VERSION at $STAMP"

# Prune only stale WAM build output; source and facts are never touched.
rm -f "$ROOT/wam/wam"
rm -rf "$ROOT/wam/runs"

FAIL=0
: > "$LOGDIR/summary.txt"

run_job() {
  name=$1; dir=$2; shift 2
  log="$LOGDIR/$name.log"
  echo "=== gardener job $name ($dir) ===" > "$log"
  ( cd "$ROOT/$dir" && timeout 120 "$@" ) >> "$log" 2>&1
  rc=$?
  if [ $rc -eq 0 ]; then
    echo "PASS $name ($rc)" | tee -a "$LOGDIR/summary.txt"
  else
    echo "FAIL $name ($rc) -- see $log" | tee -a "$LOGDIR/summary.txt"
    FAIL=1
  fi
  return $rc
}

run_job etymology logos_etymology \
  swipl -q -s src/axioms.pl -s examples/lexeme_facts.pl -s examples/edge_facts.pl \
    -s examples/morpheme_facts.pl -s examples/sense_facts.pl \
    -g "forall(ancestor_via(en_logic,A,S),(write(A-S),nl))" -t halt

run_job prolog_lexicon logos_prolog \
  swipl -q -g "use_module(logos),logos:logos_selftest" -t halt

run_job prolog_deduction logos_prolog \
  swipl -q -g "use_module(logos_deduction),logos_deduction:deduction_tests" -t halt

run_job logic_stack_mini logic_stack/mini \
  swipl -q -g metagol -t halt logicstack.pl

run_job logic_stack_full logic_stack/full \
  swipl -q -g run -t halt logicstack_full.pl

run_job exec_lock exec_lock \
  swipl -q -g "use_module(trust_gate),demo" -t halt

run_job wam_compare wam \
  make -s all compare

{
  echo "gardener run $STAMP"
  echo "swipl: $SWIPL_VERSION"
  cat "$LOGDIR/summary.txt"
  if [ $FAIL -eq 0 ]; then echo "overall: PASS"; else echo "overall: FAIL"; fi
} > "$LOGDIR/status.txt"

cat "$LOGDIR/status.txt"
exit $FAIL
