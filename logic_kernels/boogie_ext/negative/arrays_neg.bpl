// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Negative example. The invariant is wrong, so Boogie must reject this file.
// It claims a[i] != x before a[i] has been looked at.

procedure LinearSearchWrong(a: [int]int, n: int, x: int) returns (idx: int)
  requires n >= 0;
  ensures idx == -1 ==> (forall k: int :: 0 <= k && k < n ==> a[k] != x);
{
  var i: int;
  i := 0;
  idx := -1;
  while (i < n && idx == -1)
    invariant 0 <= i && i <= n;
    invariant idx == -1 ==> (forall k: int :: 0 <= k && k <= i && k < n ==> a[k] != x);
  {
    if (a[i] == x) {
      idx := i;
    } else {
      i := i + 1;
    }
  }
}
