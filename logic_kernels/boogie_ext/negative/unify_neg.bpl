// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
// Negative example. The claim is wrong, so Boogie must reject this file.
// Binding i changes a walk that passes through a bound i. The lemma in
// unify.bpl needs lookup(i, s) == NoT(); this one leaves it out.

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

procedure WalkAvoidWrong(f: int, t: Term, s: Subst, i: int, y: Term)
  requires walk(f, t, s) != Var(i);
  ensures walk(f, t, SCons(i, y, s)) == walk(f, t, s);
{
  if (f > 0 && t is Var && lookup(t->vid, s) is SomeT) {
    assert f - 1 < f && f - 1 >= 0;
    call WalkAvoidWrong(f - 1, lookup(t->vid, s)->tv, s, i, y);
  }
}
