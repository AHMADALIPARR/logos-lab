// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Negative example. The invariant is wrong, so Boogie must reject this file.
// The path entries are a + j, not a + j + 1.

function PathW(g: [int,int]bool, w: [int]int, k: int): bool {
  (forall i: int :: 0 <= i && i < k ==> g[w[i], w[i + 1]])
}

function IsPath(g: [int,int]bool, a: int, c: int, w: [int]int, k: int): bool {
  0 <= k && w[0] == a && w[k] == c && PathW(g, w, k)
}

function Reach(g: [int,int]bool, a: int, c: int): bool {
  (exists w: [int]int, k: int :: { PathW(g, w, k) } IsPath(g, a, c, w, k))
}

function SuccG(): [int,int]bool {
  (lambda x: int, y: int :: y == x + 1)
}

procedure SuccPathWrong(a: int, c: int) returns (w: [int]int, k: int)
  requires a <= c;
  ensures IsPath(SuccG(), a, c, w, k);
{
  var i: int;
  k := c - a;
  i := 0;
  w := (lambda j: int :: 0);
  w[0] := a;
  while (i < k)
    invariant 0 <= i && i <= k;
    invariant (forall j: int :: 0 <= j && j <= i ==> w[j] == a + j + 1);
  {
    w[i + 1] := a + i + 1;
    i := i + 1;
  }
}
