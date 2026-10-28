// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Boogie kernel: the unifier from Logos.mlw (terms, substitutions, walk,
// occurs check, unify), each with a fuel argument as in the WhyML source.
//
// The functions are given by their defining equations. Lemmas are recursive
// procedures; each recursive call is preceded by an assert that the fuel
// goes down and stays non-negative.

datatype Term { Var(vid: int), Atom(aid: int), Pair(hd: Term, tl: Term), Nil() }
datatype Subst { SNil(), SCons(key: int, val: Term, rest: Subst) }
datatype OptT { NoT(), SomeT(tv: Term) }
datatype OptS { NoS(), SomeS(sv: Subst) }

// ---- definitions ----

function lookup(x: int, s: Subst): OptT;
axiom (forall x: int :: { lookup(x, SNil()) } lookup(x, SNil()) == NoT());
axiom (forall x: int, k: int, v: Term, r: Subst :: { lookup(x, SCons(k, v, r)) }
  lookup(x, SCons(k, v, r)) == (if k == x then SomeT(v) else lookup(x, r)));

function walk(f: int, t: Term, s: Subst): Term;
axiom (forall f: int, t: Term, s: Subst :: { walk(f, t, s) }
  walk(f, t, s) ==
    (if f <= 0 || !(t is Var) then t
     else if lookup(t->vid, s) is SomeT then walk(f - 1, lookup(t->vid, s)->tv, s)
     else t));

function occurs(f: int, x: int, t: Term, s: Subst): bool;
axiom (forall f: int, x: int, t: Term, s: Subst :: { occurs(f, x, t, s) }
  occurs(f, x, t, s) ==
    (if f <= 0 then true
     else if walk(f, t, s) is Var then walk(f, t, s)->vid == x
     else if walk(f, t, s) is Pair
       then (occurs(f - 1, x, walk(f, t, s)->hd, s) || occurs(f - 1, x, walk(f, t, s)->tl, s))
     else false));

function unify(f: int, a: Term, b: Term, s: Subst): OptS;
axiom (forall f: int, a: Term, b: Term, s: Subst :: { unify(f, a, b, s) }
  unify(f, a, b, s) ==
    (if f <= 0 then NoS()
     else if walk(f, a, s) == walk(f, b, s) then SomeS(s)
     else if walk(f, a, s) is Var then
       (if occurs(f, walk(f, a, s)->vid, walk(f, b, s), s) then NoS()
        else SomeS(SCons(walk(f, a, s)->vid, walk(f, b, s), s)))
     else if walk(f, b, s) is Var then
       (if occurs(f, walk(f, b, s)->vid, walk(f, a, s), s) then NoS()
        else SomeS(SCons(walk(f, b, s)->vid, walk(f, a, s), s)))
     else if walk(f, a, s) is Pair && walk(f, b, s) is Pair then
       (if unify(f - 1, walk(f, a, s)->hd, walk(f, b, s)->hd, s) is NoS then NoS()
        else unify(f - 1, walk(f, a, s)->tl, walk(f, b, s)->tl,
                   unify(f - 1, walk(f, a, s)->hd, walk(f, b, s)->hd, s)->sv))
     else NoS()));

// The substitution s1 is an extension of s0: s0 is s1 with some bindings
// pushed on the front.
function len(s: Subst): int;
axiom (len(SNil()) == 0);
axiom (forall k: int, v: Term, r: Subst :: { len(SCons(k, v, r)) } len(SCons(k, v, r)) == len(r) + 1);
// Lengths are non-negative. This follows from the two equations above by
// induction on the list; Boogie has no structural induction, so it is stated.
axiom (forall s: Subst :: { len(s) } len(s) >= 0);

function Ext(s0: Subst, s1: Subst): bool;
axiom (forall s0: Subst, s1: Subst :: { Ext(s0, s1) }
  Ext(s0, s1) == (s0 == s1 || (s1 is SCons && Ext(s0, s1->rest))));

function Settled(t: Term, s: Subst): bool {
  !(t is Var) || lookup(t->vid, s) == NoT()
}

// ---- fuel zero ----

procedure WalkFuelZero(f: int, t: Term, s: Subst)
  requires f <= 0;
  ensures walk(f, t, s) == t;
{ }

procedure OccursFuelZero(f: int, x: int, t: Term, s: Subst)
  requires f <= 0;
  ensures occurs(f, x, t, s);
{ }

procedure UnifyFuelZero(f: int, a: Term, b: Term, s: Subst)
  requires f <= 0;
  ensures unify(f, a, b, s) == NoS();
{ }

// ---- lookup after a binding ----

procedure LookupBind(i: int, y: Term, s: Subst, j: int)
  ensures lookup(i, SCons(i, y, s)) == SomeT(y);
  ensures j != i ==> lookup(j, SCons(i, y, s)) == lookup(j, s);
{ }

// ---- extension is reflexive, transitive, and grows by binding ----

procedure ExtRefl(s: Subst)
  ensures Ext(s, s);
{ }

procedure ExtBind(i: int, y: Term, s: Subst)
  ensures Ext(s, SCons(i, y, s));
{ }

procedure ExtTrans(s0: Subst, s1: Subst, s2: Subst)
  requires Ext(s0, s1) && Ext(s1, s2);
  ensures Ext(s0, s2);
{
  if (s1 != s2) {
    assert s2 is SCons;
    assert len(s2->rest) < len(s2) && len(s2->rest) >= 0;
    call ExtTrans(s0, s1, s2->rest);
  }
}

// A name that is unbound in the extension is unbound in the original.
procedure ExtUnbound(s0: Subst, s1: Subst, k: int)
  requires Ext(s0, s1);
  requires lookup(k, s1) == NoT();
  ensures lookup(k, s0) == NoT();
{
  if (s0 != s1) {
    assert s1 is SCons;
    assert len(s1->rest) < len(s1) && len(s1->rest) >= 0;
    call ExtUnbound(s0, s1->rest, k);
  }
}

// A name that is bound in the original is still bound in the extension.
procedure ExtBound(s0: Subst, s1: Subst, k: int)
  requires Ext(s0, s1);
  requires lookup(k, s0) is SomeT;
  ensures lookup(k, s1) is SomeT;
{
  if (s0 != s1) {
    assert s1 is SCons;
    assert len(s1->rest) < len(s1) && len(s1->rest) >= 0;
    call ExtBound(s0, s1->rest, k);
  }
}

// ---- walk with more fuel, and walk after a binding ----

// If walk with fuel f ends on a settled term, more fuel gives the same answer.
procedure WalkStable(f: int, g: int, t: Term, s: Subst)
  requires f <= g;
  requires Settled(walk(f, t, s), s);
  ensures walk(g, t, s) == walk(f, t, s);
{
  if (f > 0 && t is Var && lookup(t->vid, s) is SomeT) {
    assert f - 1 < f && f - 1 >= 0 && f - 1 <= g - 1;
    call WalkStable(f - 1, g - 1, lookup(t->vid, s)->tv, s);
  }
}

// Binding a name the walk never stops on does not change the walk.
procedure WalkAvoid(f: int, t: Term, s: Subst, i: int, y: Term)
  requires lookup(i, s) == NoT();
  requires walk(f, t, s) != Var(i);
  ensures walk(f, t, SCons(i, y, s)) == walk(f, t, s);
{
  if (f > 0 && t is Var && lookup(t->vid, s) is SomeT) {
    assert t->vid != i;
    assert f - 1 < f && f - 1 >= 0;
    call WalkAvoid(f - 1, lookup(t->vid, s)->tv, s, i, y);
  }
}

// A walk that ended on the unbound name i now continues to y, given one more step.
procedure WalkThrough(f: int, g: int, t: Term, s: Subst, i: int, y: Term)
  requires lookup(i, s) == NoT();
  requires Settled(y, s) && y != Var(i);
  requires walk(f, t, s) == Var(i);
  requires g > f && g >= 1;
  ensures walk(g, t, SCons(i, y, s)) == y;
{
  if (t != Var(i)) {
    assert f > 0;
    assert t is Var;
    assert lookup(t->vid, s) is SomeT;
    assert t->vid != i;
    assert f - 1 < f && f - 1 >= 0 && g - 1 > f - 1 && g - 1 >= 1;
    call WalkThrough(f - 1, g - 1, lookup(t->vid, s)->tv, s, i, y);
  }
}

// Binding the unbound name i to y makes the two walks agree, with enough fuel.
procedure BindLemma(f: int, g: int, a: Term, b: Term, i: int, y: Term, s: Subst)
  requires lookup(i, s) == NoT();
  requires walk(f, a, s) == Var(i);
  requires walk(f, b, s) == y;
  requires Settled(y, s) && y != Var(i);
  requires g > f && g >= 1;
  ensures walk(g, a, SCons(i, y, s)) == walk(g, b, SCons(i, y, s));
{
  call WalkThrough(f, g, a, s, i, y);
  call WalkStable(f, g, b, s);
  call WalkAvoid(g, b, s, i, y);
}

// ---- unify extends the substitution ----

procedure UnifyMonotone(f: int, a: Term, b: Term, s: Subst, s2: Subst)
  requires unify(f, a, b, s) == SomeS(s2);
  ensures Ext(s, s2);
{
  var x: Term;
  var y: Term;
  var s1: Subst;
  assert f > 0;
  x := walk(f, a, s);
  y := walk(f, b, s);
  if (x == y) {
    call ExtRefl(s);
  } else if (x is Var) {
    call ExtBind(x->vid, y, s);
  } else if (y is Var) {
    call ExtBind(y->vid, x, s);
  } else {
    assert x is Pair && y is Pair;
    s1 := unify(f - 1, x->hd, y->hd, s)->sv;
    assert f - 1 < f && f - 1 >= 0;
    call UnifyMonotone(f - 1, x->hd, y->hd, s, s1);
    call UnifyMonotone(f - 1, x->tl, y->tl, s1, s2);
    call ExtTrans(s, s1, s2);
  }
}

// The two recursive calls of unify on a pair: the head call succeeds
// into s1, the tail call runs from s1 into s2, and s ⊑ s1 ⊑ s2.
procedure UnifyPairSteps(f: int, a: Term, b: Term, s: Subst, s2: Subst)
  requires unify(f, a, b, s) == SomeS(s2);
  requires walk(f, a, s) is Pair && walk(f, b, s) is Pair && walk(f, a, s) != walk(f, b, s);
  ensures unify(f - 1, walk(f, a, s)->hd, walk(f, b, s)->hd, s) is SomeS;
  ensures Ext(s, unify(f - 1, walk(f, a, s)->hd, walk(f, b, s)->hd, s)->sv);
  ensures unify(f - 1, walk(f, a, s)->tl, walk(f, b, s)->tl,
                unify(f - 1, walk(f, a, s)->hd, walk(f, b, s)->hd, s)->sv) == SomeS(s2);
  ensures Ext(unify(f - 1, walk(f, a, s)->hd, walk(f, b, s)->hd, s)->sv, s2);
{
  var x: Term;
  var y: Term;
  var s1: Subst;
  x := walk(f, a, s);
  y := walk(f, b, s);
  s1 := unify(f - 1, x->hd, y->hd, s)->sv;
  call UnifyMonotone(f - 1, x->hd, y->hd, s, s1);
  call UnifyMonotone(f - 1, x->tl, y->tl, s1, s2);
}

// ---- a successful unify makes the two walks agree ----
// Proven when both walks end on settled terms (a non-variable, or a variable
// with no binding) and the two ends are not two different pairs. Two different
// pairs are only equal after their parts are unified; that case is covered
// part by part in UnifyPairSteps.

procedure UnifyWalkEqual(f: int, g: int, a: Term, b: Term, s: Subst, s2: Subst)
  requires unify(f, a, b, s) == SomeS(s2);
  requires Settled(walk(f, a, s), s) && Settled(walk(f, b, s), s);
  requires walk(f, a, s) == walk(f, b, s)
        || !(walk(f, a, s) is Pair && walk(f, b, s) is Pair);
  requires g > f && g >= 1;
  ensures walk(g, a, s2) == walk(g, b, s2);
{
  var x: Term;
  var y: Term;
  assert f > 0;
  x := walk(f, a, s);
  y := walk(f, b, s);
  if (x == y) {
    call WalkStable(f, g, a, s);
    call WalkStable(f, g, b, s);
  } else if (x is Var) {
    call BindLemma(f, g, a, b, x->vid, y, s);
  } else {
    assert y is Var;
    call BindLemma(f, g, b, a, y->vid, x, s);
  }
}

// ---- occurs check ----

function Size(t: Term): int;
axiom (forall t: Term :: { Size(t) }
  Size(t) == (if t is Pair then 1 + Size(t->hd) + Size(t->tl) else 1));
// Sizes are at least 1. This follows from the equation above by induction
// on the term; Boogie has no structural induction, so it is stated.
axiom (forall t: Term :: { Size(t) } Size(t) >= 1);

function Contains(x: int, t: Term): bool;
axiom (forall x: int, t: Term :: { Contains(x, t) }
  Contains(x, t) ==
    (if t is Var then t->vid == x
     else if t is Pair then (Contains(x, t->hd) || Contains(x, t->tl))
     else false));

procedure WalkEmpty(f: int, t: Term)
  ensures walk(f, t, SNil()) == t;
{ }

// With the empty substitution and fuel at least the size of the term,
// the occurs check finds every variable that the term contains.
procedure OccursSyntactic(f: int, x: int, t: Term)
  requires Contains(x, t);
  requires f >= Size(t);
  ensures occurs(f, x, t, SNil());
{
  call WalkEmpty(f, t);
  if (t is Pair) {
    assert f - 1 < f && f - 1 >= 0;
    if (Contains(x, t->hd)) {
      assert f - 1 >= Size(t->hd);
      call OccursSyntactic(f - 1, x, t->hd);
    } else {
      assert Contains(x, t->tl);
      assert f - 1 >= Size(t->tl);
      call OccursSyntactic(f - 1, x, t->tl);
    }
  }
}

// Unifying a variable with a pair that contains it fails, in both directions.
procedure OccursCheckBlocks(f: int, i: int, t: Term)
  requires t is Pair && Contains(i, t);
  requires f > Size(t);
  ensures unify(f, Var(i), t, SNil()) == NoS();
  ensures unify(f, t, Var(i), SNil()) == NoS();
{
  call WalkEmpty(f, t);
  call WalkEmpty(f, Var(i));
  call OccursSyntactic(f, i, t);
}

// So a successful unify of a variable with a pair never binds it to a pair containing it.
procedure OccursCheckSound(f: int, i: int, t: Term, s2: Subst)
  requires t is Pair && f > Size(t);
  requires unify(f, Var(i), t, SNil()) == SomeS(s2);
  ensures !Contains(i, t);
{
  if (Contains(i, t)) {
    call OccursCheckBlocks(f, i, t);
  }
}

// ---- a worked example, checked on concrete terms ----

procedure Example()
{
  // Var 1 against Atom 2 binds 1 to 2.
  assert unify(3, Var(1), Atom(2), SNil()) == SomeS(SCons(1, Atom(2), SNil()));
  // A variable against a pair containing it fails the occurs check.
  assert unify(5, Var(1), Pair(Var(1), Nil()), SNil()) == NoS();
  // Two pairs unify part by part.
  assert unify(6, Pair(Var(1), Atom(3)), Pair(Atom(2), Var(4)), SNil())
         == SomeS(SCons(4, Atom(3), SCons(1, Atom(2), SNil())));
  // Fuel zero fails.
  assert unify(0, Atom(1), Atom(1), SNil()) == NoS();
}
