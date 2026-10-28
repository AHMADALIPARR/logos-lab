# Five logic kernels

These are source-level reference kernels, not yet execution-validated. No native runtimes were detected in this environment.

- `metagol.pl`: Metagol (SWI-Prolog compatible Metagol distribution required). Load with `swipl -s metagol.pl -g run -t halt` after installing the Metagol library. API and module loading can vary by distribution.
- `twelf.elf`: Twelf LF proof search. Run `twelf-server`, load file, and check `%query`; exact CLI depends on installation.
- `boogie.bpl`: Boogie verification. Run `boogie boogie.bpl`; an SMT solver such as Z3 is required.
- `logica.l`: Logica two-hop reachability. Run with the Logica compiler and a configured SQL engine; e.g. `logica logica.l run Reach2` for supported distributions. It deliberately computes at most two edges, not a transitive closure.
- `dlv.dl`: DLV disjunctive ASP. Run `dlv -filter=assign dlv.dl` using the classic DLV engine.

Validation is pending. Kernel sources are intended as minimal starting points and may require version-specific adjustments.
