// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Boogie kernel: 4-bit odd parity.
//
// 1. The parity of four bits (sum mod 2) equals the XOR fold over the bits,
//    and the same holds for any number of bits (a loop with an invariant).
// 2. A decision tree over the bits, one split per bit, classifies all 16
//    vectors as odd or even correctly. The tree is the shape the Logic Stack
//    reaches for the odd-parity target: a path of bit tests, one per position.
//    The repo has no fixed learned rule to copy, so this is the full tree
//    that any correct rule must agree with on the 16 vectors.
//
// A bit vector is a map from position to 0 or 1.

function Xor(x: int, y: int): int {
  if x == y then 0 else 1
}

function Bit4(v: [int]int): bool {
  (forall i: int :: 0 <= i && i < 4 ==> v[i] == 0 || v[i] == 1)
}

function Parity4(v: [int]int): int {
  (v[0] + v[1] + v[2] + v[3]) mod 2
}

function Fold4(v: [int]int): int {
  Xor(Xor(Xor(Xor(0, v[0]), v[1]), v[2]), v[3])
}

// ---- parity equals the XOR fold ----

procedure ParityIsFold4(v: [int]int)
  requires Bit4(v);
  ensures Parity4(v) == Fold4(v);
{ }

// Sum of the first n entries.
function SumN(v: [int]int, n: int): int;
axiom (forall v: [int]int, n: int :: { SumN(v, n) }
  SumN(v, n) == (if n <= 0 then 0 else SumN(v, n - 1) + v[n - 1]));

// For any length: folding with Xor gives the sum mod 2.
procedure ParityIsFoldN(v: [int]int, n: int) returns (acc: int)
  requires n >= 0;
  requires (forall i: int :: 0 <= i && i < n ==> v[i] == 0 || v[i] == 1);
  ensures acc == SumN(v, n) mod 2;
{
  var i: int;
  i := 0;
  acc := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant acc == SumN(v, i) mod 2;
    measure n - i;
  {
    acc := Xor(acc, v[i]);
    i := i + 1;
  }
}

// ---- decision tree over bits ----

datatype DT { Leaf(lv: bool), Node(nb: int, lo: DT, hi: DT) }

function Eval(t: DT, v: [int]int): bool;
axiom (forall t: DT, v: [int]int :: { Eval(t, v) }
  Eval(t, v) == (if t is Leaf then t->lv
                 else if v[t->nb] == 0 then Eval(t->lo, v) else Eval(t->hi, v)));

// OddK: the subtree once k bits are tested and the ones seen so far are even.
// EvenK: the same where the ones seen so far are odd.
function Odd3(): DT { Node(3, Leaf(false), Leaf(true)) }
function Even3(): DT { Node(3, Leaf(true), Leaf(false)) }
function Odd2(): DT { Node(2, Odd3(), Even3()) }
function Even2(): DT { Node(2, Even3(), Odd3()) }
function Odd1(): DT { Node(1, Odd2(), Even2()) }
function Even1(): DT { Node(1, Even2(), Odd2()) }
function OddTree(): DT { Node(0, Odd1(), Even1()) }

// Over every 4-bit vector the tree answers true exactly when the parity is 1.
procedure TreeClassifies(v: [int]int)
  requires Bit4(v);
  ensures Eval(OddTree(), v) <==> Parity4(v) == 1;
  ensures Eval(OddTree(), v) <==> Fold4(v) == 1;
{ }

// The same, checked one vector at a time on all 16 vectors.
procedure TreeExhaustive()
{
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 0 else 0)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 0 else 0)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 0 else 0)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 0 else 0)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 0 else 0)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 0 else 0)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 0 else 0)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 0 else 0)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 1 else 0)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 1 else 0)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 1 else 0)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 1 else 0)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 1 else 0)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 1 else 0)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 1 else 0)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 1 else 0)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 0 else 1)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 0 else 1)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 0 else 1)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 0 else 1)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 0 else 1)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 0 else 1)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 0 else 1)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 0 else 1)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 1 else 1)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 0 else if i == 2 then 1 else 1)) == 0;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 1 else 1)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 0 else if i == 2 then 1 else 1)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 1 else 1)) == true;
  assert Fold4((lambda i: int :: if i == 0 then 0 else if i == 1 then 1 else if i == 2 then 1 else 1)) == 1;
  assert Eval(OddTree(), (lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 1 else 1)) == false;
  assert Fold4((lambda i: int :: if i == 0 then 1 else if i == 1 then 1 else if i == 2 then 1 else 1)) == 0;
}
