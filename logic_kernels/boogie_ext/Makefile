# Verify every kernel and check that every negative example is rejected.
# Output of the real runs goes to VERIFY.log.
#
#   make verify        run everything, write VERIFY.log
#   make clean         remove VERIFY.log
#
# Boogie needs .NET and a Z3 binary. env.sh sets both for this box;
# override BOOGIE, Z3 and DOTNET_ROOT on the command line elsewhere.

SHELL := /bin/bash
export DOTNET_ROOT ?= $(HOME)/.dotnet
BOOGIE ?= /workspace/.tools/boogie/boogie
Z3 ?= /workspace/.tools/dafny/z3/bin/z3-4.12.1
TIMELIMIT ?= 30

FILES := sums arrays unify reach parity foil

.PHONY: verify clean
verify:
	@{ \
	  echo "Boogie: $$($(BOOGIE) -version 2>&1 | head -1)"; \
	  echo "Z3: $$($(Z3) --version)"; \
	  echo "Date: $$(date -Is)"; \
	  echo; \
	  status=0; \
	  for f in $(FILES); do \
	    echo "=== $$f.bpl ==="; \
	    out=$$($(BOOGIE) -timeLimit:$(TIMELIMIT) -proverOpt:PROVER_PATH=$(Z3) $$f.bpl 2>&1); \
	    echo "$$out"; \
	    if echo "$$out" | grep -Eq "finished with [0-9]+ verified, 0 errors$$"; then \
	      echo "check: verified"; \
	    else echo "check: FAILED"; status=1; fi; \
	    echo; \
	  done; \
	  for f in $(FILES); do \
	    echo "=== negative/$${f}_neg.bpl (must be rejected) ==="; \
	    out=$$($(BOOGIE) -timeLimit:$(TIMELIMIT) -proverOpt:PROVER_PATH=$(Z3) negative/$${f}_neg.bpl 2>&1); \
	    echo "$$out"; \
	    if echo "$$out" | grep -Eq "[1-9][0-9]* errors?$$" && ! echo "$$out" | grep -q "time out"; then \
	      echo "check: rejected"; \
	    else echo "check: NOT REJECTED"; status=1; fi; \
	    echo; \
	  done; \
	  if [ $$status -eq 0 ]; then echo "RESULT: all files verified, all negative examples rejected"; \
	  else echo "RESULT: FAILED"; fi; \
	  exit $$status; \
	} 2>&1 | tee VERIFY.log; exit $${PIPESTATUS[0]}

clean:
	rm -f VERIFY.log
