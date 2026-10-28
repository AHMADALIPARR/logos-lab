# LOGOS WhyML structural port (partial)

`Logos.mlw` contains a bounded structural port of the available microKanren unifier and goal interpreter. It is **not verified** and not claimed to be a semantics-preserving port. It uses a conservative occurs-check cutoff and a bounded search; these can reject valid solutions. `Fresh`, relation declarations, reification, and iterative deepening are not yet implemented.

The supplied Prolog source stops at the beginning of the probabilistic face; full P-log, Dyna, CP-logic and Janus implementations cannot be translated from it.

Run `why3 prove Logos.mlw` after installing Why3 and configured provers. The code has not been compiled or checked in this environment.

Custom surface syntax proposal:

```
relation ancestor(x, y) := parent(x, y) | exists z { parent(x, z) & ancestor(z, y) }
query ancestor(alice, ?who) depth 20
random weather { sunny @ 0.7 | rainy @ 0.3 }
weight path(a, b) using max_plus
cause alarm when smoke at t + 1
constraint x in 1..9
```

The syntax above is a proposal, **not** an implemented parser or compiler.
