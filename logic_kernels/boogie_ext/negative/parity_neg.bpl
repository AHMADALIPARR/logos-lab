// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Negative example. The invariant is wrong, so Boogie must reject this file.
// The running fold is the sum mod 2, not always 0.

function Xor(x: int, y: int): int {
  if x == y then 0 else 1
}

// Sum of the first n entries.
function SumN(v: [int]int, n: int): int;
axiom (forall v: [int]int, n: int :: { SumN(v, n) }
  SumN(v, n) == (if n <= 0 then 0 else SumN(v, n - 1) + v[n - 1]));

procedure FoldWrong(v: [int]int, n: int) returns (acc: int)
  requires n >= 0;
  requires (forall i: int :: 0 <= i && i < n ==> v[i] == 0 || v[i] == 1);
  ensures acc == SumN(v, n) mod 2;
{
  var i: int;
  i := 0;
  acc := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant acc == 0;
  {
    acc := Xor(acc, v[i]);
    i := i + 1;
  }
}
