// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Boogie kernel: arrays. Search, max/min, copy, reverse, binary search, sorting.
//
// An array is a value of type [int]int and its length is the integer n.
// Procedures that change an array return the new one.
//
// Permutation is stated with a witness map p. The array b is a permutation
// of a when p sends [0,n) into [0,n), p is one-to-one, and b[k] == a[p[k]].
// That is multiset equality: every value occurs in b as often as in a.

// ---- predicates ----

function Sorted(a: [int]int, n: int): bool {
  (forall i: int, j: int :: 0 <= i && i <= j && j < n ==> a[i] <= a[j])
}

function IsPerm(a: [int]int, b: [int]int, p: [int]int, n: int): bool {
  (forall k: int :: 0 <= k && k < n ==> 0 <= p[k] && p[k] < n)
  && (forall k: int, l: int :: 0 <= k && k < n && 0 <= l && l < n && p[k] == p[l] ==> k == l)
  && (forall k: int :: 0 <= k && k < n ==> b[k] == a[p[k]])
}

// ---- linear search ----

procedure LinearSearch(a: [int]int, n: int, x: int) returns (idx: int)
  requires n >= 0;
  ensures idx == -1 ==> (forall k: int :: 0 <= k && k < n ==> a[k] != x);
  ensures idx != -1 ==> 0 <= idx && idx < n && a[idx] == x;
{
  var i: int;
  i := 0;
  idx := -1;
  while (i < n && idx == -1)
    invariant 0 <= i && i <= n;
    invariant idx == -1 ==> (forall k: int :: 0 <= k && k < i ==> a[k] != x);
    invariant idx != -1 ==> 0 <= idx && idx < n && a[idx] == x;
    measure if idx == -1 then n - i else 0;
  {
    if (a[i] == x) {
      idx := i;
    } else {
      i := i + 1;
    }
  }
}

// ---- maximum and minimum ----

procedure MaxArray(a: [int]int, n: int) returns (m: int, im: int)
  requires n > 0;
  ensures 0 <= im && im < n && a[im] == m;
  ensures (forall k: int :: 0 <= k && k < n ==> a[k] <= m);
{
  var i: int;
  m := a[0];
  im := 0;
  i := 1;
  while (i < n)
    invariant 1 <= i && i <= n;
    invariant 0 <= im && im < i && a[im] == m;
    invariant (forall k: int :: 0 <= k && k < i ==> a[k] <= m);
    measure n - i;
  {
    if (a[i] > m) {
      m := a[i];
      im := i;
    }
    i := i + 1;
  }
}

procedure MinArray(a: [int]int, n: int) returns (m: int, im: int)
  requires n > 0;
  ensures 0 <= im && im < n && a[im] == m;
  ensures (forall k: int :: 0 <= k && k < n ==> m <= a[k]);
{
  var i: int;
  m := a[0];
  im := 0;
  i := 1;
  while (i < n)
    invariant 1 <= i && i <= n;
    invariant 0 <= im && im < i && a[im] == m;
    invariant (forall k: int :: 0 <= k && k < i ==> m <= a[k]);
    measure n - i;
  {
    if (a[i] < m) {
      m := a[i];
      im := i;
    }
    i := i + 1;
  }
}

// ---- copy ----

procedure CopyArray(a: [int]int, n: int) returns (b: [int]int)
  requires n >= 0;
  ensures (forall k: int :: 0 <= k && k < n ==> b[k] == a[k]);
{
  var i: int;
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant (forall k: int :: 0 <= k && k < i ==> b[k] == a[k]);
    measure n - i;
  {
    b[i] := a[i];
    i := i + 1;
  }
}

// ---- swap with permutation witness ----

procedure SwapPerm(a: [int]int, b: [int]int, p: [int]int, n: int, i: int, j: int)
  returns (b2: [int]int, p2: [int]int)
  requires IsPerm(a, b, p, n);
  requires 0 <= i && i < n && 0 <= j && j < n;
  ensures IsPerm(a, b2, p2, n);
  ensures b2[i] == b[j] && b2[j] == b[i];
  ensures (forall k: int :: k != i && k != j ==> b2[k] == b[k]);
{
  b2 := b[i := b[j]][j := b[i]];
  p2 := p[i := p[j]][j := p[i]];
}

// ---- reverse ----

procedure ReverseInPlace(a: [int]int, n: int) returns (b: [int]int, p: [int]int)
  requires n >= 0;
  ensures (forall k: int :: 0 <= k && k < n ==> b[k] == a[n - 1 - k]);
  ensures IsPerm(a, b, p, n);
{
  var i: int;
  var j: int;
  b := a;
  p := (lambda k: int :: k);
  i := 0;
  j := n - 1;
  while (i < j)
    invariant 0 <= i && j == n - 1 - i && j < n;
    invariant i <= j + 1;
    invariant (forall k: int :: 0 <= k && k < i ==> b[k] == a[n - 1 - k]);
    invariant (forall k: int :: j < k && k < n ==> b[k] == a[n - 1 - k]);
    invariant (forall k: int :: i <= k && k <= j ==> b[k] == a[k]);
    invariant IsPerm(a, b, p, n);
    measure j - i + 1;
  {
    call b, p := SwapPerm(a, b, p, n, i, j);
    i := i + 1;
    j := j - 1;
  }
}

// ---- binary search on a sorted array ----

procedure BinarySearch(a: [int]int, n: int, x: int) returns (idx: int)
  requires n >= 0;
  requires Sorted(a, n);
  ensures idx == -1 ==> (forall k: int :: 0 <= k && k < n ==> a[k] != x);
  ensures idx != -1 ==> 0 <= idx && idx < n && a[idx] == x;
{
  var lo: int;
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  idx := -1;
  while (idx == -1 && lo < hi)
    invariant 0 <= lo && lo <= hi && hi <= n;
    invariant (forall k: int :: 0 <= k && k < lo ==> a[k] < x);
    invariant (forall k: int :: hi <= k && k < n ==> a[k] > x);
    invariant idx != -1 ==> 0 <= idx && idx < n && a[idx] == x;
    measure if idx == -1 then hi - lo else 0;
  {
    mid := lo + (hi - lo) div 2;
    if (a[mid] < x) {
      lo := mid + 1;
    } else if (a[mid] > x) {
      hi := mid;
    } else {
      idx := mid;
    }
  }
}

// ---- insertion sort ----

procedure InsertionSort(a: [int]int, n: int) returns (b: [int]int, p: [int]int)
  requires n >= 0;
  ensures Sorted(b, n);
  ensures IsPerm(a, b, p, n);
{
  var i: int;
  var j: int;
  b := a;
  p := (lambda k: int :: k);
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant Sorted(b, i);
    invariant IsPerm(a, b, p, n);
    measure n - i;
  {
    j := i;
    while (j > 0 && b[j - 1] > b[j])
      invariant 0 <= j && j <= i;
      invariant IsPerm(a, b, p, n);
      invariant (forall k: int, l: int :: 0 <= k && k < l && l <= i && k != j && l != j ==> b[k] <= b[l]);
      invariant j < i ==> b[j] <= b[j + 1];
      invariant 0 < j && j < i ==> b[j - 1] <= b[j + 1];
      measure j;
    {
      call b, p := SwapPerm(a, b, p, n, j - 1, j);
      j := j - 1;
    }
    i := i + 1;
  }
}

// ---- bubble sort ----

procedure BubbleSort(a: [int]int, n: int) returns (b: [int]int, p: [int]int)
  requires n >= 0;
  ensures Sorted(b, n);
  ensures IsPerm(a, b, p, n);
{
  var m: int;
  var j: int;
  b := a;
  p := (lambda k: int :: k);
  m := n;
  while (m > 1)
    invariant 0 <= m && m <= n;
    invariant IsPerm(a, b, p, n);
    invariant (forall k: int, l: int :: m <= k && k < l && l < n ==> b[k] <= b[l]);
    invariant (forall k: int, l: int :: 0 <= k && k < m && m <= l && l < n ==> b[k] <= b[l]);
    measure m;
  {
    j := 0;
    while (j < m - 1)
      invariant 0 <= j && j <= m - 1;
      invariant IsPerm(a, b, p, n);
      invariant (forall k: int :: 0 <= k && k <= j ==> b[k] <= b[j]);
      invariant (forall k: int, l: int :: m <= k && k < l && l < n ==> b[k] <= b[l]);
      invariant (forall k: int, l: int :: 0 <= k && k < m && m <= l && l < n ==> b[k] <= b[l]);
      measure m - 1 - j;
    {
      if (b[j] > b[j + 1]) {
        call b, p := SwapPerm(a, b, p, n, j, j + 1);
      }
      j := j + 1;
    }
    m := m - 1;
  }
}
