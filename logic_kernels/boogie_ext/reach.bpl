// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Boogie kernel: reachability. Paths over a graph, the successor graph,
// the Twelf path/edge and path/step rules, and Logica's two-hop Reach2.
//
// A graph is a map g from two integers to bool; g[x,y] means an edge x -> y.
// A path from a to c is a witness: a map w and a length k with w[0] == a,
// w[k] == c and an edge between each w[i] and w[i+1].

function PathW(g: [int,int]bool, w: [int]int, k: int): bool {
  (forall i: int :: 0 <= i && i < k ==> g[w[i], w[i + 1]])
}

function IsPath(g: [int,int]bool, a: int, c: int, w: [int]int, k: int): bool {
  0 <= k && w[0] == a && w[k] == c && PathW(g, w, k)
}

function Reach(g: [int,int]bool, a: int, c: int): bool {
  (exists w: [int]int, k: int :: { PathW(g, w, k) } IsPath(g, a, c, w, k))
}

// ---- building paths ----

procedure ReachRefl(g: [int,int]bool, a: int)
  ensures Reach(g, a, a);
{
  var w: [int]int;
  w := (lambda i: int :: a);
  assert PathW(g, w, 0);
  assert IsPath(g, a, a, w, 0);
}

// Twelf path/edge: an edge is a path.
procedure PathEdge(g: [int,int]bool, a: int, b: int) returns (w: [int]int, k: int)
  requires g[a, b];
  ensures IsPath(g, a, b, w, k) && k == 1;
  ensures Reach(g, a, b);
{
  w := (lambda i: int :: if i == 0 then a else b);
  k := 1;
  assert PathW(g, w, 1);
}

// Twelf path/step: an edge a -> b followed by a path b -> c is a path a -> c.
procedure PathStep(g: [int,int]bool, a: int, b: int, c: int, w: [int]int, k: int)
  returns (w2: [int]int, k2: int)
  requires g[a, b];
  requires IsPath(g, b, c, w, k);
  ensures IsPath(g, a, c, w2, k2) && k2 == k + 1;
  ensures Reach(g, a, c);
{
  w2 := (lambda i: int :: if i <= 0 then a else w[i - 1]);
  k2 := k + 1;
  assert PathW(g, w2, k2);
}

// A path a -> b followed by an edge b -> c is a path a -> c.
procedure PathSnoc(g: [int,int]bool, a: int, b: int, c: int, w: [int]int, k: int)
  returns (w2: [int]int, k2: int)
  requires IsPath(g, a, b, w, k);
  requires g[b, c];
  ensures IsPath(g, a, c, w2, k2) && k2 == k + 1;
  ensures Reach(g, a, c);
{
  w2 := w[k + 1 := c];
  k2 := k + 1;
  assert PathW(g, w2, k2);
}

// Transitivity: a path a -> b and a path b -> c join into a path a -> c.
procedure ReachTrans(g: [int,int]bool, a: int, b: int, c: int,
                     w1: [int]int, k1: int, w2: [int]int, k2: int)
  returns (w3: [int]int, k3: int)
  requires IsPath(g, a, b, w1, k1);
  requires IsPath(g, b, c, w2, k2);
  ensures IsPath(g, a, c, w3, k3) && k3 == k1 + k2;
  ensures Reach(g, a, c);
{
  w3 := (lambda i: int :: if i <= k1 then w1[i] else w2[i - k1]);
  k3 := k1 + k2;
  assert PathW(g, w3, k3);
}

// ---- the successor graph ----

function SuccG(): [int,int]bool {
  (lambda x: int, y: int :: y == x + 1)
}

// A loop builds the path a, a+1, ..., c.
procedure SuccPath(a: int, c: int) returns (w: [int]int, k: int)
  requires a <= c;
  ensures IsPath(SuccG(), a, c, w, k);
  ensures k == c - a;
{
  var i: int;
  k := c - a;
  i := 0;
  w := (lambda j: int :: 0);
  w[0] := a;
  while (i < k)
    invariant 0 <= i && i <= k;
    invariant (forall j: int :: 0 <= j && j <= i ==> w[j] == a + j);
    measure k - i;
  {
    w[i + 1] := a + i + 1;
    i := i + 1;
  }
  assert PathW(SuccG(), w, k);
}

// A path in the successor graph only goes up. A loop along the path
// keeps the invariant a <= w[i].
procedure SuccPathUp(a: int, c: int, w: [int]int, k: int)
  requires IsPath(SuccG(), a, c, w, k);
  ensures a <= c && c - a == k;
{
  var i: int;
  i := 0;
  while (i < k)
    invariant 0 <= i && i <= k;
    invariant w[i] == a + i;
    measure k - i;
  {
    assert SuccG()[w[i], w[i + 1]];
    i := i + 1;
  }
}

procedure SuccReachIff(a: int, c: int)
  ensures a <= c ==> Reach(SuccG(), a, c);
{
  var w: [int]int;
  var k: int;
  if (a <= c) {
    call w, k := SuccPath(a, c);
  }
}

// ---- a closed set contains everything reachable ----
// R is closed when every edge out of a member lands in R. If it holds src,
// it holds the end of every path from src. A loop along the path carries
// the invariant that w[i] is in R.

procedure ClosedContainsPath(g: [int,int]bool, R: [int]bool, src: int, c: int, w: [int]int, k: int)
  requires R[src];
  requires (forall u: int, v: int :: R[u] && g[u, v] ==> R[v]);
  requires IsPath(g, src, c, w, k);
  ensures R[c];
{
  var i: int;
  i := 0;
  while (i < k)
    invariant 0 <= i && i <= k;
    invariant R[w[i]];
    measure k - i;
  {
    assert g[w[i], w[i + 1]];
    i := i + 1;
  }
}

// ---- Twelf: abc : path a c = path/step eab (path/edge ebc) ----
// Nodes a = 0, b = 1, c = 2. Edges eab and ebc.

function TwelfG(): [int,int]bool {
  (lambda x: int, y: int :: (x == 0 && y == 1) || (x == 1 && y == 2))
}

procedure TwelfAbc() returns (w: [int]int, k: int)
  ensures IsPath(TwelfG(), 0, 2, w, k);
  ensures Reach(TwelfG(), 0, 2);
{
  var wbc: [int]int;
  var kbc: int;
  call wbc, kbc := PathEdge(TwelfG(), 1, 2);
  call w, k := PathStep(TwelfG(), 0, 1, 2, wbc, kbc);
}

// There is no path from c back to a.
procedure TwelfNoBack(w: [int]int, k: int)
  requires 0 <= k && w[0] == 2;
  requires PathW(TwelfG(), w, k);
  ensures k == 0;
{
  if (k > 0) {
    assert TwelfG()[w[0], w[1]];
    assert false;
  }
}

// ---- Logica: Reach2 over Edge(ada,bob), Edge(bob,cy), Edge(cy,dee) ----
// ada = 0, bob = 1, cy = 2, dee = 3.

function LogicaEdge(): [int,int]bool {
  (lambda x: int, y: int :: (x == 0 && y == 1) || (x == 1 && y == 2) || (x == 2 && y == 3))
}

// Reach2(x, y) :- Edge(x, y);  Reach2(x, z) :- Edge(x, y), Edge(y, z);
function Reach2(g: [int,int]bool, x: int, z: int): bool {
  g[x, z] || (exists y: int :: g[x, y] && g[y, z])
}

procedure LogicaTable()
  ensures (forall x: int, z: int :: Reach2(LogicaEdge(), x, z) <==>
            ((x == 0 && z == 1) || (x == 1 && z == 2) || (x == 2 && z == 3)
             || (x == 0 && z == 2) || (x == 1 && z == 3)));
{
  assert (forall p: int, q: int :: LogicaEdge()[p, q] <==>
            ((p == 0 && q == 1) || (p == 1 && q == 2) || (p == 2 && q == 3)));
  assert (forall p: int, q: int, y: int :: LogicaEdge()[p, y] && LogicaEdge()[y, q] ==>
            ((p == 0 && q == 2) || (p == 1 && q == 3)));
  assert LogicaEdge()[0, 1] && LogicaEdge()[1, 2] && LogicaEdge()[2, 3];
}

// Reach2 is sound for Reach: a one-hop or two-hop fact has a path.
procedure Reach2Sound(g: [int,int]bool, x: int, y: int, z: int)
  returns (w: [int]int, k: int)
  requires g[x, y] && g[y, z];
  ensures IsPath(g, x, z, w, k) && k == 2;
{
  var w1: [int]int;
  var k1: int;
  var w2: [int]int;
  var k2: int;
  call w1, k1 := PathEdge(g, y, z);
  call w, k := PathStep(g, x, y, z, w1, k1);
}

// Reach2 stops at two hops: ada reaches dee by a path of three edges,
// but Reach2(ada, dee) does not hold.
procedure LogicaThreeHops() returns (w: [int]int, k: int)
  ensures IsPath(LogicaEdge(), 0, 3, w, k) && k == 3;
  ensures Reach(LogicaEdge(), 0, 3);
  ensures !Reach2(LogicaEdge(), 0, 3);
{
  var w1: [int]int;
  var k1: int;
  var w2: [int]int;
  var k2: int;
  call w1, k1 := Reach2Sound(LogicaEdge(), 1, 2, 3);
  call w, k := PathStep(LogicaEdge(), 0, 1, 3, w1, k1);
}
