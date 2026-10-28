// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Negative example. The claim is wrong, so Boogie must reject this file.
// If the ratio of positives drops (p1*n0 < p0*n1) the gain is not non-negative.

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

procedure GainNonNegativeWrong(t: int, p0: int, n0: int, p1: int, n1: int)
  requires t > 0 && p0 > 0 && p1 > 0 && n0 >= 0 && n1 >= 0;
  requires p1 * n0 <= p0 * n1;
  ensures Gain(t, p0, n0, p1, n1) >= 0.0;
{
}
