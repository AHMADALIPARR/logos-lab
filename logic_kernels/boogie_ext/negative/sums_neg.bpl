// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Negative example. The invariant is wrong, so Boogie must reject this file.
// The sum of 1..i is i*(i+1)/2, not i*i/2.

procedure SumToWrong(n: int) returns (s: int)
  requires n >= 0;
  ensures s == n * (n + 1) div 2;
{
  var i: int;
  s := 0;
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant s == i * i div 2;
  {
    i := i + 1;
    s := s + i;
  }
}
