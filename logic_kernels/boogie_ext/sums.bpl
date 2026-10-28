// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Boogie kernel: summation loops, factorial, power, gcd.
//
// `div` and `mod` are integer division and remainder. In Boogie 3.x a bare `/`
// on ints is real division, so the closed forms below use `div`.
//
// fact, pow, gcd are mathematical functions given by their defining equations
// (recursion on the natural numbers). Each axiom is one defining equation.
// Induction facts are proved as lemma procedures with loops and used by
// calling them. Loops that must terminate carry a `measure`.

// ---------------------------------------------------------------- sums

procedure SumTo(n: int) returns (s: int)
  requires 0 <= n;
  ensures s == n * (n + 1) div 2;
{
  var i: int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant 2 * s == i * (i + 1);
  {
    i := i + 1;
    s := s + i;
  }
}

procedure SumSquares(n: int) returns (s: int)
  requires 0 <= n;
  ensures 6 * s == n * (n + 1) * (2 * n + 1);
{
  var i: int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant 6 * s == i * (i + 1) * (2 * i + 1);
  {
    i := i + 1;
    s := s + i * i;
  }
}

procedure SumCubes(n: int) returns (s: int)
  requires 0 <= n;
  ensures 4 * s == n * n * (n + 1) * (n + 1);
{
  var i: int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant 4 * s == i * i * (i + 1) * (i + 1);
  {
    i := i + 1;
    s := s + i * i * i;
  }
}

// The sum of the first n odd numbers is n squared.
procedure SumOdd(n: int) returns (s: int)
  requires 0 <= n;
  ensures s == n * n;
{
  var i: int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant s == i * i;
  {
    s := s + (2 * i + 1);
    i := i + 1;
  }
}

// ----------------------------------------------------------- factorial

function fact(n: int): int;
axiom fact(0) == 1;
axiom (forall n: int :: { fact(n) } n > 0 ==> fact(n) == n * fact(n - 1));

// fact is positive, by induction on n.
procedure FactPositive(m: int)
  requires 0 <= m;
  ensures fact(m) >= 1;
{
  var i: int;
  i := 0;
  while (i < m)
    invariant 0 <= i && i <= m;
    invariant fact(i) >= 1;
  {
    i := i + 1;
    assert fact(i) == i * fact(i - 1);
    assert fact(i) >= 1;
  }
}

procedure Factorial(n: int) returns (r: int)
  requires 0 <= n;
  ensures r == fact(n);
{
  var i: int;
  i := 0;
  r := 1;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant r == fact(i);
  {
    i := i + 1;
    r := r * i;
  }
}

// Recursive form. Boogie checks calls against the contract and does not check
// termination, so the measure n is asserted to drop before the call.
procedure FactRec(n: int) returns (r: int)
  requires 0 <= n;
  ensures r == fact(n);
{
  var r1: int;
  if (n == 0) {
    r := 1;
  } else {
    assert 0 <= n - 1 && n - 1 < n;
    call r1 := FactRec(n - 1);
    r := n * r1;
  }
}

// ---------------------------------------------------------------- power

function pow(b: int, e: int): int;
axiom (forall b: int :: { pow(b, 0) } pow(b, 0) == 1);
axiom (forall b: int, e: int :: { pow(b, e) } e > 0 ==> pow(b, e) == b * pow(b, e - 1));

// pow(x*x, k) == pow(x, 2k), by induction on k.
procedure PowSquare(x: int, k: int)
  requires 0 <= k;
  ensures pow(x * x, k) == pow(x, 2 * k);
{
  var i: int;
  i := 0;
  while (i < k)
    invariant 0 <= i && i <= k;
    invariant pow(x * x, i) == pow(x, 2 * i);
  {
    i := i + 1;
    assert pow(x * x, i) == x * x * pow(x * x, i - 1);
    assert pow(x, 2 * i) == x * pow(x, 2 * i - 1);
    assert pow(x, 2 * i - 1) == x * pow(x, 2 * i - 2);
  }
}

procedure PowLoop(b: int, n: int) returns (r: int)
  requires 0 <= n;
  ensures r == pow(b, n);
{
  var i: int;
  i := 0;
  r := 1;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant r == pow(b, i);
  {
    i := i + 1;
    r := r * b;
  }
}

// Square and multiply. The measure e halves or drops by one each round.
procedure FastPow(b: int, n: int) returns (r: int)
  requires 0 <= n;
  ensures r == pow(b, n);
{
  var x, e: int;
  x := b;
  e := n;
  r := 1;
  while (e > 0)
    invariant 0 <= e;
    invariant r * pow(x, e) == pow(b, n);
    measure e;
  {
    if (e mod 2 == 1) {
      r := r * x;
      e := e - 1;
    } else {
      call PowSquare(x, e div 2);
      x := x * x;
      e := e div 2;
    }
  }
  assert pow(x, 0) == 1;
}

// ------------------------------------------------------------------ gcd

function gcd(a: int, b: int): int;
axiom (forall a: int :: { gcd(a, 0) } gcd(a, 0) == a);
// The trigger is the right-hand side so the equation unfolds only where a
// term gcd(b, a mod b) already occurs, which keeps the prover from unfolding forever.
axiom (forall a: int, b: int :: { gcd(b, a mod b) } b > 0 ==> gcd(a, b) == gcd(b, a mod b));

// One Euclid step in terms of the quotient q and remainder z (x == q*y + z).
// Bezout coefficients of (y, z) from those of (x, y):
procedure BezoutStep(x: int, y: int, q: int, z: int, a: int, b: int,
                     s1: int, t1: int, s2: int, t2: int)
  requires x == q * y + z;
  requires x == a * s1 + b * t1 && y == a * s2 + b * t2;
  ensures z == a * (s1 - q * s2) + b * (t1 - q * t2);
{
}

// Divisor witnesses: if c == x*p1 + y*p2 then c == y*(q*p1 + p2) + z*p1.
procedure WitnessStep(c: int, x: int, y: int, q: int, z: int, p1: int, p2: int)
  requires x == q * y + z;
  requires c == x * p1 + y * p2;
  ensures c == y * (q * p1 + p2) + z * p1;
{
}

// Euclid's algorithm. The measure y is nonnegative and strictly drops each
// round (the remainder is below the divisor).
procedure GcdLoop(a: int, b: int) returns (g: int)
  requires 0 <= a && 0 <= b;
  ensures g == gcd(a, b) && g >= 0;
{
  var x, y, q, z: int;
  x := a; y := b;
  while (y != 0)
    invariant 0 <= x && 0 <= y;
    invariant gcd(x, y) == gcd(a, b);
    measure y;
  {
    q := x div y;
    z := x mod y;
    x := y;
    y := z;
  }
  g := x;
  assert gcd(x, 0) == x;
}

// Bezout: the result is a combination of a and b, so every common divisor
// of a and b divides it.
procedure GcdBezout(a: int, b: int) returns (g: int, s: int, t: int)
  requires 0 <= a && 0 <= b;
  ensures g == gcd(a, b) && g >= 0;
  ensures g == a * s + b * t;
{
  var x, y, q, z, s1, t1, s2, t2, ns, nt: int;
  x := a; y := b;
  s1 := 1; t1 := 0; s2 := 0; t2 := 1;
  while (y != 0)
    invariant 0 <= x && 0 <= y;
    invariant gcd(x, y) == gcd(a, b);
    invariant x == a * s1 + b * t1;
    invariant y == a * s2 + b * t2;
    measure y;
  {
    q := x div y;
    z := x mod y;
    assert x == q * y + z;
    call BezoutStep(x, y, q, z, a, b, s1, t1, s2, t2);
    ns := s1 - q * s2;
    nt := t1 - q * t2;
    s1 := s2; t1 := t2; s2 := ns; t2 := nt;
    x := y;
    y := z;
  }
  g := x; s := s1; t := t1;
  assert gcd(x, 0) == x;
}

// The result divides a and b, with witnesses p and r.
procedure GcdDivides(a: int, b: int) returns (g: int, p: int, r: int)
  requires 0 <= a && 0 <= b;
  ensures g == gcd(a, b) && g >= 0;
  ensures a == g * p && b == g * r;
{
  var x, y, q, z, p1, p2, r1, r2, np, nr: int;
  x := a; y := b;
  p1 := 1; p2 := 0; r1 := 0; r2 := 1;
  while (y != 0)
    invariant 0 <= x && 0 <= y;
    invariant gcd(x, y) == gcd(a, b);
    invariant a == x * p1 + y * p2;
    invariant b == x * r1 + y * r2;
    measure y;
  {
    q := x div y;
    z := x mod y;
    assert x == q * y + z;
    call WitnessStep(a, x, y, q, z, p1, p2);
    call WitnessStep(b, x, y, q, z, r1, r2);
    np := q * p1 + p2;
    nr := q * r1 + r2;
    p2 := p1; r2 := r1;
    p1 := np; r1 := nr;
    x := y;
    y := z;
  }
  g := x; p := p1; r := r1;
  assert gcd(x, 0) == x;
}

// Any common divisor of a and b, given with witnesses, divides the Bezout sum.
procedure CommonDivisorDividesGcd(a: int, b: int, g: int, s: int, t: int, d: int, a1: int, b1: int)
  requires g == a * s + b * t;
  requires a == d * a1 && b == d * b1;
  ensures g == d * (a1 * s + b1 * t);
{
}

// The greatest common divisor is the largest common divisor of positive inputs.
procedure GcdGreatest(a: int, b: int, d: int, a1: int, b1: int)
  requires 0 < a && 0 <= b && d > 0;
  requires a == d * a1 && b == d * b1;
  ensures d <= gcd(a, b);
{
  var g, s, t, g2, p, r, c: int;
  call g, s, t := GcdBezout(a, b);
  call g2, p, r := GcdDivides(a, b);
  call CommonDivisorDividesGcd(a, b, g, s, t, d, a1, b1);
  c := a1 * s + b1 * t;
  assert g == d * c;
  assert g2 == g;
  assert a == g * p;
  assert g > 0;
  assert c >= 1;
  assert g >= d;
}

// Recursive form; the measure b is asserted to drop before the call.
procedure GcdRec(a: int, b: int) returns (g: int)
  requires 0 <= a && 0 <= b;
  ensures g == gcd(a, b);
{
  if (b == 0) {
    g := a;
  } else {
    assert 0 <= a mod b && a mod b < b;
    call g := GcdRec(b, a mod b);
  }
}

procedure GcdSymmetric(a: int, b: int)
  requires 0 <= a && 0 <= b;
  ensures gcd(a, b) == gcd(b, a);
{
  if (a < b) {
    assert a mod b == a;
  } else if (b < a) {
    assert b mod a == b;
  }
}
