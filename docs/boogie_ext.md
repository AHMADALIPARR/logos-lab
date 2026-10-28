# boogie-ext

Boogie proofs that extend `logic_kernels/boogie.bpl`. Run `make verify`.
It checks every file, checks that each negative example is rejected, and
writes the real output to `VERIFY.log`.

Tested with Boogie 3.5.8 and Z3 4.12.1. `env.sh` sets up .NET and Z3 on
this box.

## What each file proves

- `sums.bpl` closed forms for sums: 1+..+n = n(n+1)/2, squares, cubes,
  odd numbers (= n*n). Also factorial, powers (including fast power by
  squaring), and gcd: the loop computes the gcd, it divides both inputs,
  every common divisor divides it, and it is symmetric.
- `arrays.bpl` linear search, binary search, max, min, copy, in-place
  reverse, insertion sort and bubble sort. The sorts end sorted and are
  a permutation of the input.
- `unify.bpl` the unifier from `Logos.mlw` (fuel-bounded walk, occurs
  check, unify). Proves that unifying only adds bindings, that bindings
  made earlier survive, that walking stops on settled terms, how a Pair
  unifies head then tail, and that the occurs check stops `X = f(X)`.
- `reach.bpl` reachability. Paths and Reach are defined, Reach is
  reflexive and transitive, and the `succ` graph reaches exactly the
  larger numbers. Also the Twelf `path` graph (a to c, no way back) and
  the Logica `Reach2` table for ada, bob, cy, dee.
- `parity.bpl` 4-bit odd parity: the xor fold gives the parity, an n-bit
  loop does the same, and a full decision tree over the 4 bits classifies
  all 16 inputs the same way.
- `foil.bpl` the FOIL scoring facts: gain is non-negative when the ratio
  of positives does not drop, dropping negatives helps, same counts give
  no gain, and entropy is between 0 and 1 for a two-class split.

`negative/` has one wrong file per area (wrong invariant or wrong claim).
Boogie rejects each one and `VERIFY.log` has the output.

## Things to know

- Integer division is `div` and `mod`. In Boogie 3.x a bare `/` on ints
  is real division, so the original `boogie.bpl` does not typecheck on
  3.5.8. `sums.bpl` uses `div`.
- Axioms. No `assume` is used. The axioms are the recursive definitions
  (fact, pow, gcd, lookup, walk, occurs, unify, Eval, SumN), the facts
  `len >= 0` and `Size >= 1` (Boogie has no structural induction), and
  for `foil.bpl` the properties of `log2`: log2(1)=0, log2(2)=1,
  increasing, log2(x*y)=log2 x+log2 y, log2(x) <= L*(x-1) for some L > 0.
- Boogie does not check that recursion terminates. Recursive lemmas
  assert that their measure drops, and loops use `measure`.
- Unify: walk equality after a successful unify is proved only for
  settled ends that are not two different pairs. The Pair case is
  proved as head step then tail step. Preservation of lookups is stated
  as a suffix relation (`Ext`) because a walk that runs out of fuel can
  hide a binding. The occurs-check theorem is for the empty substitution.
- Arrays: the permutation is a witness map (injective, in range,
  b[k] == a[p[k]]), not a multiset count.
- Reach: completeness is for explicit path witnesses and Reach is an
  existential. There is no fixpoint algorithm.
- Parity: the repo has no fixed learned rule, so the proof uses a full
  16-case decision tree as a stand-in.
- Foil: gain is proved for counts with p0, p1 > 0. Entropy is over
  ratios in (0,1); pure sets are defined as 0.
