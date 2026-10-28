# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr

# Makefile -- build the WAM engine, run every example, compare with swipl
#
# Etymology: make, Old English macian "to fashion, to construct".
#
# Usage:
#   make            build ./wam
#   make run        run every example, write runs/<name>.txt
#   make compare    check the ISO examples against swipl
#   make clean      remove ./wam and runs/*

CC      = gcc
CFLAGS  = -std=c99 -O2 -Wall -Wextra
EMIT    = swipl -q emit.pl --
TOKS    = $(basename $(notdir $(wildcard examples/*.tok)))
PROGS   = $(basename $(notdir $(wildcard examples/*.pl)))
ISO     = ancestor append member control syntax

.PHONY: all run compare clean

all: wam

wam: wam.c
	$(CC) $(CFLAGS) -o wam wam.c

## ── Run ──────────────────────────────────────────────────────────────────

run: wam
	@mkdir -p runs
	@for n in $(TOKS); do \
	  ./wam -all examples/$$n.tok > runs/$$n.txt; \
	  echo "runs/$$n.txt"; \
	done
	@./wam -trace examples/unify.tok > runs/unify_trace.txt
	@echo runs/unify_trace.txt
	@for n in $(PROGS); do \
	  $(EMIT) examples/$$n.pl > runs/$$n.pl.tok || exit 1; \
	  ./wam -all runs/$$n.pl.tok > runs/$$n.pl.txt; \
	  echo "runs/$$n.pl.tok runs/$$n.pl.txt"; \
	done

## ── Compare with swipl ───────────────────────────────────────────────────

compare: run
	@for n in $(ISO); do \
	  swipl -q answers.pl -- examples/$$n.pl > runs/$$n.swipl.txt; \
	  if diff -u runs/$$n.swipl.txt runs/$$n.pl.txt > /dev/null; \
	  then echo "$$n: swipl and wam agree"; \
	  else echo "$$n: DIFFERENT"; diff -u runs/$$n.swipl.txt runs/$$n.pl.txt; exit 1; fi; \
	done

## ── Clean ────────────────────────────────────────────────────────────────

clean:
	rm -f wam runs/*
