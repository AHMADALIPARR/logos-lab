// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Boogie kernel: FOIL information gain and entropy over counts.
//
// A rule covers p positive and n negative examples. Adding a literal gives
// counts p1 and n1, and t is the number of positives covered by both.
//   gain = t * (log2(p1 / (p1 + n1)) - log2(p0 / (p0 + n0)))
//
// log2 is not built into Boogie, so it is a function with these axioms,
// all standard facts about the base-2 logarithm:
//   log2(1) = 0, log2(2) = 1;
//   log2 is strictly increasing on positive reals;
//   log2(x * y) = log2(x) + log2(y) for positive x and y;
//   log2(x) <= L * (x - 1) for positive x, where L = 1 / ln 2.
// These are the only axioms in this file.

function log2(x: real): real;
const L: real;
axiom L > 0.0;
axiom log2(1.0) == 0.0;
axiom log2(2.0) == 1.0;
axiom (forall x: real, y: real :: { log2(x), log2(y) } 0.0 < x && x < y ==> log2(x) < log2(y));
axiom (forall x: real, y: real :: { log2(x * y) } 0.0 < x && 0.0 < y ==> log2(x * y) == log2(x) + log2(y));
axiom (forall x: real :: { log2(x) } 0.0 < x ==> log2(x) <= L * (x - 1.0));

function Ratio(p: int, n: int): real {
  real(p) / real(p + n)
}

function Gain(t: int, p0: int, n0: int, p1: int, n1: int): real {
  real(t) * (log2(Ratio(p1, n1)) - log2(Ratio(p0, n0)))
}

// ---- counts: the ratio of positives, compared without division ----

procedure RatioCompare(p0: int, n0: int, p1: int, n1: int)
  requires p0 > 0 && p1 > 0 && n0 >= 0 && n1 >= 0;
  ensures Ratio(p1, n1) >= Ratio(p0, n0) <==> p1 * n0 >= p0 * n1;
  ensures Ratio(p1, n1) > Ratio(p0, n0) <==> p1 * n0 > p0 * n1;
  ensures 0.0 < Ratio(p0, n0) && Ratio(p0, n0) <= 1.0;
  ensures 0.0 < Ratio(p1, n1) && Ratio(p1, n1) <= 1.0;
{
  var r0: real;
  var r1: real;
  var d0: real;
  var d1: real;
  r0 := Ratio(p0, n0);
  r1 := Ratio(p1, n1);
  d0 := real(p0 + n0);
  d1 := real(p1 + n1);
  assert d0 > 0.0 && d1 > 0.0;
  assert r0 * d0 == real(p0);
  assert r1 * d1 == real(p1);
  assert r0 > 0.0 && r1 > 0.0;
  assert r0 <= 1.0 && r1 <= 1.0;
  // r1 >= r0 exactly when r1*d1*d0 >= r0*d0*d1, that is p1*d0 >= p0*d1
  assert (r1 >= r0) <==> (real(p1) * d0 >= real(p0) * d1);
  assert (r1 > r0) <==> (real(p1) * d0 > real(p0) * d1);
  assert real(p1) * d0 - real(p0) * d1 == real(p1 * n0 - p0 * n1);
}

// ---- gain is non-negative when the ratio of positives does not drop ----

procedure GainNonNegative(t: int, p0: int, n0: int, p1: int, n1: int)
  requires t >= 0 && p0 > 0 && p1 > 0 && n0 >= 0 && n1 >= 0;
  requires p1 * n0 >= p0 * n1;
  ensures Gain(t, p0, n0, p1, n1) >= 0.0;
{
  call RatioCompare(p0, n0, p1, n1);
  assert log2(Ratio(p1, n1)) >= log2(Ratio(p0, n0));
}

procedure GainPositive(t: int, p0: int, n0: int, p1: int, n1: int)
  requires t > 0 && p0 > 0 && p1 > 0 && n0 >= 0 && n1 >= 0;
  requires p1 * n0 > p0 * n1;
  ensures Gain(t, p0, n0, p1, n1) > 0.0;
{
  call RatioCompare(p0, n0, p1, n1);
  assert log2(Ratio(p1, n1)) > log2(Ratio(p0, n0));
}

// The sign of the gain is the sign of p1*n0 - p0*n1.
procedure GainNegative(t: int, p0: int, n0: int, p1: int, n1: int)
  requires t > 0 && p0 > 0 && p1 > 0 && n0 >= 0 && n1 >= 0;
  requires p1 * n0 < p0 * n1;
  ensures Gain(t, p0, n0, p1, n1) < 0.0;
{
  call RatioCompare(p0, n0, p1, n1);
  assert Ratio(p1, n1) < Ratio(p0, n0);
  assert log2(Ratio(p1, n1)) < log2(Ratio(p0, n0));
}

// A literal that keeps every positive and drops negatives never loses gain.
procedure DroppingNegatives(t: int, p: int, n0: int, n1: int)
  requires t >= 0 && p > 0 && 0 <= n1 && n1 <= n0;
  ensures Gain(t, p, n0, p, n1) >= 0.0;
  ensures t > 0 && n1 < n0 ==> Gain(t, p, n0, p, n1) > 0.0;
{
  call GainNonNegative(t, p, n0, p, n1);
  if (t > 0 && n1 < n0) {
    call GainPositive(t, p, n0, p, n1);
  }
}

// A literal that covers nothing new (same counts) has gain zero.
procedure SameCountsNoGain(t: int, p: int, n: int)
  requires p > 0 && n >= 0;
  ensures Gain(t, p, n, p, n) == 0.0;
{ }

// ---- entropy ----

function Ent(q: real): real {
  -(q * log2(q)) - ((1.0 - q) * log2(1.0 - q))
}

// Entropy of a set with p positives and n negatives. A pure set has entropy 0.
function EntCounts(p: int, n: int): real {
  if p <= 0 || n <= 0 then 0.0 else Ent(Ratio(p, n))
}

procedure LogBelowZero(q: real)
  requires 0.0 < q && q <= 1.0;
  ensures log2(q) <= 0.0;
  ensures q < 1.0 ==> log2(q) < 0.0;
{ }

procedure EntNonNegative(q: real)
  requires 0.0 < q && q < 1.0;
  ensures Ent(q) >= 0.0;
{
  assert log2(q) < 0.0;
  assert log2(1.0 - q) < 0.0;
  assert q * log2(q) < 0.0;
  assert (1.0 - q) * log2(1.0 - q) < 0.0;
}

// The Gibbs step: for one probability q, q*log2(1/(2q)) <= L*(1/2 - q).
procedure GibbsTerm(q: real)
  requires 0.0 < q && q < 1.0;
  ensures q * (-1.0 - log2(q)) <= L * (0.5 - q);
{
  var a: real;
  a := 1.0 / (2.0 * q);
  assert a * (2.0 * q) == 1.0;
  assert a > 0.0;
  assert log2(a * (2.0 * q)) == log2(a) + log2(2.0 * q);
  assert log2(2.0 * q) == 1.0 + log2(q);
  assert log2(a) == -1.0 - log2(q);
  assert log2(a) <= L * (a - 1.0);
  assert q * log2(a) <= q * (L * (a - 1.0));
  assert q * (L * (a - 1.0)) == L * (q * a - q);
  assert q * a == 0.5;
}

procedure EntAtMostOne(q: real)
  requires 0.0 < q && q < 1.0;
  ensures Ent(q) <= 1.0;
{
  call GibbsTerm(q);
  call GibbsTerm(1.0 - q);
  assert q * (-1.0 - log2(q)) + (1.0 - q) * (-1.0 - log2(1.0 - q)) <= L * (0.5 - q) + L * (0.5 - (1.0 - q));
  assert L * (0.5 - q) + L * (0.5 - (1.0 - q)) == 0.0;
}

// Reciprocals have opposite logs. Stated on variables so the product axiom applies.
procedure LogRecip(x: real, y: real)
  requires 0.0 < x && 0.0 < y && x * y == 1.0;
  ensures log2(x) + log2(y) == 0.0;
{
  assert log2(x * y) == log2(x) + log2(y);
}

// log2 of one half is -1.
procedure LogHalf(h: real)
  requires h == 0.5;
  ensures log2(h) == -1.0;
{
  call LogRecip(0.5, 2.0);
}

// Entropy of a half-and-half set is exactly 1.
procedure EntHalf(h: real)
  requires h == 0.5;
  ensures Ent(h) == 1.0;
{
  call LogHalf(h);
  assert 1.0 - h == h;
}

// Entropy bounds for counts of positives and negatives.
procedure EntCountsBounds(p: int, n: int)
  requires p >= 0 && n >= 0;
  ensures 0.0 <= EntCounts(p, n) && EntCounts(p, n) <= 1.0;
  ensures (p == 0 || n == 0) ==> EntCounts(p, n) == 0.0;
  ensures (p > 0 && p == n) ==> EntCounts(p, n) == 1.0;
{
  if (p > 0 && n > 0) {
    call RatioCompare(p, n, p, n);
    assert Ratio(p, n) < 1.0;
    call EntNonNegative(Ratio(p, n));
    call EntAtMostOne(Ratio(p, n));
    if (p == n) {
      assert Ratio(p, n) == 0.5;
      call EntHalf(Ratio(p, n));
    }
  }
}
