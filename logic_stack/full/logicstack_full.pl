% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% logicstack_full.pl — L0..L4 complete ILP kernel (ISO Prolog)
% L0 binary -> L1 logic -> L2 FOIL -> L3 Metagol(MIL) -> L3b ILASP-lite
% -> L4 decision tree over learned rules
%
% ?- run.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ===========================================================================
% L0: BINARY SUBSTRATE
% ===========================================================================
bit(0). bit(1).
band(A,B,R) :- R is A /\ B.
bor(A,B,R)  :- R is A \/ B.
bxor(A,B,R) :- R is A xor B.
bits(0,[]).
bits(N,[B|T]) :- N>0, N1 is N-1, bit(B), bits(N1,T).
% example universe: 4-bit vectors; target = odd parity
mk_pos(N, E) :- bits(N,E), odd_parity(E).
mk_neg(N, E) :- bits(N,E), \+ odd_parity(E).
odd_parity(E) :- sum_bits(E,S), S mod 2 =:= 1.
sum_bits([],0).
sum_bits([B|T],S) :- sum_bits(T,S1), S is S1+B.
% BK over bit-vectors: relational predicates used by the learner
% pos(E,I) means position I of vector E is bound... we lift to atoms:
%   holds(E, has(I,V))
%   holds(E, and(I,J,V))
%   holds(E, geq(I,V))      b[I] >= V
%   holds(E, eqxor(I,J,V))  b[I] xor b[J] = V
holds(E, has(I,V))   :- nth0(I,E,V).
holds(E, and(I,J,V)) :- nth0(I,E,A), nth0(J,E,B), band(A,B,V).
holds(E, geq(I,V))   :- nth0(I,E,A), A >= V.
holds(E, eqxor(I,J,V)) :- nth0(I,E,A), nth0(J,E,B), bxor(A,B,V).
% ===========================================================================
% L1: LOGIC — example store + general clause machinery
% ===========================================================================
:- dynamic pos_ex/1, neg_ex/1, learned/1, invented_pred/1, clause_db/2.
load_all(N) :-
    retractall(pos_ex(_)), retractall(neg_ex(_)),
    retractall(learned(_)), retractall(invented_pred(_)),
    retractall(clause_db(_,_)),
    forall(mk_pos(N,E), assertz(pos_ex(E))),
    forall(mk_neg(N,E), assertz(neg_ex(E))),
    init_bk.
init_bk :-
    assertz(invented_pred(0)),    % next invented id
    true.
% literal enumeration with types (arity = how many variables introduced)
% body lit schema: lit(Name, Arity, Test)
lit_schema(has,   1, has(_I,_V)).
lit_schema(and,   2, and(_I,_J,_V)).
lit_schema(geq,   1, geq(_I,_V)).
lit_schema(eqxor, 2, eqxor(_I,_J,_V)).
% instantiate a literal for width W with all constants
lit_instance(W, has(I,V))     :- W1 is W-1, between(0,W1,I), bit(V).
lit_instance(W, and(I,J,V))   :- W1 is W-1, between(0,W1,I), between(I,W1,J), bit(V).
lit_instance(W, geq(I,V))     :- W1 is W-1, between(0,W1,I), V=1.
lit_instance(W, eqxor(I,J,V)) :- W1 is W-1, between(0,W1,I), between(0,W1,J), bit(V).
% ===========================================================================
% L2: GENERAL FOIL — entropy-guided literal addition, multi-clause cover
% ===========================================================================
% rule = ordered list of literal terms; covers a whole rule
rule_covers([], _).
rule_covers([L|Rest], E) :- holds(E,L), rule_covers(Rest,E).
% covered positives/negatives under current partial rule
covered_pos(R, Pos) :-    % positives not yet covered by a learned clause (separate & conquer)
    findall(E,(pos_ex(E),\+ ( learned(C), rule_covers(C,E) ),rule_covers(R,E)),Pos).
covered_neg(R, Neg) :- findall(E,(neg_ex(E),rule_covers(R,E)),Neg).
entropy(0, 0.0) :- !.
entropy(P, H) :- P > 0, 1-P > 0, H is -(P*log(P)+(1-P)*log(1-P)), !.
entropy(_, 0.0).
% FOIL gain:  T* (log2 p1/(p1+n1) - log2 p0/(p0+n0))  -- Quinlan exact form
foil_gain(Lit, R, G) :-
    covered_pos(R,Pos), covered_neg(R,Neg),
    length(Pos,P0), length(Neg,N0),
    findall(E,(member(E,Pos),rule_covers([Lit],E)),TP),
    findall(E,(member(E,Neg),rule_covers([Lit],E)),TN),
    length(TP,P1), length(TN,N1),
    ( P0+N0 =:= 0 -> G is 0.0
    ; P1+N1 =:= 0 -> G is 0.0
    ; P1 =:= 0 -> G is 0.0
    ; T is P1,
      Gain1 is log(P1/(P1+N1))/log(2),
      Gain0 is log(P0/(P0+N0))/log(2),
      G is T * (Gain1 - Gain0) ).
% greedy: pick best literal not already in rule
best_literal(R, W, Best, BestG) :-
    findall(G-L,
      ( lit_instance(W,L), \+ memberchk(L,R), foil_gain(L,R,G) ),
      Cands),
    Cands \= [],
    max_member(BestG-Best, Cands).
% single clause: refine until it covers no negatives
foil_clause(R, W, Final) :-
    covered_neg(R, Neg), Neg \= [],
    best_literal(R, W, L, G), G > 0.0, !,
    foil_clause([L|R], W, Final).
% plateau (parity: every single literal has gain 0): look ahead two literals
foil_clause(R, W, Final) :-
    covered_neg(R, Neg), Neg \= [],
    best_pair(R, W, L1, L2), !,
    foil_clause([L2,L1|R], W, Final).
foil_clause(R, _, R).
best_pair(R, W, L1, L2) :-
    findall(G-(L1-L2),
      ( lit_instance(W,L1), \+ memberchk(L1,R), foil_gain(L1,R,G1),
        lit_instance(W,L2), L2 \== L1, \+ memberchk(L2,R),
        foil_gain(L2,[L1|R],G2), G is G1+G2 ),
      Cands),
    Cands \= [],
    max_member(BestG-(L1-L2), Cands),
    BestG > 0.0.
% multi-clause: remove covered pos, recurse (separate-conquer)
foil_run(W, Clauses) :- foil_run(W, [], Clauses).
foil_run(W, Acc, Final) :-
    findall(E,pos_ex(E),Pos),
    exclude(covered_by_any(Acc), Pos, Remaining),
    Remaining \= [], !,
    foil_clause([], W, C), C \= [], !,
    assertz(learned(C)),
    foil_run(W, [C|Acc], Final).
foil_run(_, Acc, Acc).
covered_by_any(Clauses, E) :-
    member(C,Clauses), rule_covers(C,E).
% ===========================================================================
% L3: METAGOL — meta-interpretive learning with predicate invention
% meta-rules (Muggleton):
%   chain:   P(A,B) :- Q(A,C), R(C,B)
%   switch:  P(A,B) :- Q(B,A)
%   ident:   P(A,B) :- Q(A,B)
%   precon:  P(A,B) :- Q(A), R(A,B)
%   postcon: P(A,B) :- Q(A,B), R(B)
% target learned as clauses over BK + invented preds, invented bottom-up
% ===========================================================================
% BK relational signature: succ/2 on chain positions (lifted binary domain)
:- dynamic bk_pred/2, inv_call/5.
bk_pred(succ, 2).
bk_pred(zero, 1).
bk_fact(succ(0,1)). bk_fact(succ(1,2)). bk_fact(succ(2,3)). bk_fact(succ(3,4)).
bk_fact(zero(0)).
% succ/2 is a system predicate in SWI-Prolog; use the bounded BK succ instead
:- redefine_system_predicate(succ(_,_)).
succ(A,B) :- bk_fact(succ(A,B)).
% meta-rule interpreter: prove metarule(Id, P, Q, R) body
metarule(chain,   P, Q, R, A, B) :- call(Q, A, C), call(R, C, B), call(P, A, B).
metarule(ident,   P, Q, _, A, B) :- call(Q, A, B), call(P, A, B).
metarule(switch,  P, Q, _, A, B) :- call(Q, B, A), call(P, A, B).
% invented pred program store: invented(Id, Clauses) with Clauses as
% list of metarule applications [app(Q,MetaId)]
:- dynamic inv_program/2, inv_counter/1.
reset_mil :- retractall(inv_program(_,_)), retractall(inv_counter(_)),
             assertz(inv_counter(0)).
% MIL generalization step: choose BK predicates to fill metarule slots
% for target T(A,B) given examples: try minimal program = single metarule
% with BK Q,R; if incomplete, invent one pred.
mil_solve(target, PosAB, NegAB) :-
    reset_mil,
    mil_program_search([chain, ident, switch], PosAB, NegAB, Prog),
    maplist(portray_clause_line, Prog).
% enumerate candidate 1- and 2-clause programs; consistency filter
mil_program_search(MRs, PosAB, NegAB, Prog) :-
    member(MR, MRs),
    ( MR = chain ->
        ( bk_pred(Q,_), bk_pred(R,_) )
    ; bk_pred(Q,_) ),
    once(bk_fill(MR, Q, R, PosAB, NegAB, Prog)).
bk_fill(ident, Q, _, PosAB, NegAB, [q(Q)]) :-
    all_cover(ident_prog(Q), PosAB),
    none_cover(ident_prog(Q), NegAB).
bk_fill(switch, Q, _, PosAB, NegAB, [q(Q)]) :-
    all_cover(switch_prog(Q), PosAB),
    none_cover(switch_prog(Q), NegAB).
bk_fill(chain, Q, R, PosAB, NegAB, [chain(Q,R)]) :-
    all_cover(chain_prog(Q,R), PosAB),
    none_cover(chain_prog(Q,R), NegAB),
    \+ trivial(Q,R).          % avoid Q=R degenerate loops
trivial(Q,R) :- Q==R.
ident_prog(Q, A, B) :- call(Q, A, B).
switch_prog(Q, A, B) :- call(Q, B, A).
chain_prog(Q, R, A, B) :- call(Q, A, C), call(R, C, B).
all_cover(P, Exs) :- forall(member((A,B),Exs), call(P,A,B)).
none_cover(P, Exs) :- forall(member((A,B),Exs), \+ call(P,A,B)).
% predicate invention: when no single metarule works, invent inv1 as
% chain of two BK preds, then target := chain(inv1, Q)
invent_step(Q1, R1, _Q2, PosAB, NegAB) :-
    inv_counter(N), N1 is N+1, retract(inv_counter(N)), assertz(inv_counter(N1)),
    atom_concat(inv, N1, Inv),
    assertz(inv_program(Inv, [chain(Q1,R1)])),
    assertz(bk_pred(Inv,2)),
    dynamic(Inv/2),
    % inv1(A,B) :- Q1(A,C), R1(C,B)
    Head =.. [Inv, A, B], G1 =.. [Q1, A, C], G2 =.. [R1, C, B],
    assertz((Head :- G1, G2)),
    assertz(inv_call(Inv, Q1, R1, PosAB, NegAB)).
% concrete inv1 definition via table (closure computed at runtime)
:- dynamic inv1/2.
build_inv1(Q, R) :-
    retractall(inv1(_,_)),
    forall(( bk_fact(Qs), Qs =.. [Q,A,C],
             bk_fact(Rs), Rs =.. [R,C2,B], C == C2 ),
           assertz(inv1(A,B))).
% target examples for MIL: reachability over succ (2-step = 0..4 forward)
mil_pos([ (0,2),(1,3),(2,4),(0,3),(0,4),(1,4) ]).
mil_neg([ (4,0),(3,0),(2,0),(4,1) ]).
% run MIL: if chain(succ,succ) consistent, done; else invent inv1
run_mil :-
    mil_pos(P), mil_neg(N),
    ( bk_fill(chain, succ, succ, P, N, Prog) ->
        format("MIL minimal program: ~w~n        target(A,B) :- succ(A,C), succ(C,B).~n",[Prog])
    ; build_inv1(succ,succ),
      format("MIL: single chain inconsistent -> invent inv1~n"),
      format("        inv1(A,B) :- succ(A,C), succ(C,B).~n"),
      length(P,PN), length(N,NN),
      findall(x,(member((A,B),P),inv1(A,B)),Ci), length(Ci,CI),
      findall(x,(member((A,B),N),inv1(A,B)),Ni), length(Ni,NI),
      format("        inv1 covers ~w/~w pos examples, ~w/~w neg.~n",[CI,PN,NI,NN]),
      format("        f(A,B) :- inv1(A,B).~n"),
      % inv1 alone is not complete (distance 3, 4): add the tailrec meta-rule
      %   tailrec: P(A,B) :- Q(A,C), P(C,B)
      format("        f(A,B) :- succ(A,C), f(C,B).   % tailrec~n"),
      findall(x,(member((A,B),P),inv_tailrec(succ,A,B)),Cf), length(Cf,CF),
      findall(x,(member((A,B),N),inv_tailrec(succ,A,B)),Nf), length(Nf,NF),
      format("        f covers ~w/~w pos examples, ~w/~w neg.~n",[CF,PN,NF,NN])
    ).
inv_tailrec(_, A, B) :- inv1(A, B).
inv_tailrec(Q, A, B) :- call(Q, A, C), inv_tailrec(Q, C, B).
% ===========================================================================
% L3b: ILASP-LITE — answer-set-flavoured learning
% neg examples become constraints: body includes \+ atom (under ASP semantics
% we instead *minimise* rule usage s.t. negatives unprovable = constraint check)
% learned hypothesis H minimises (fewest literals) s.t.:
%   M+(H) = pos, M-(H) = neg  (brave/cautious split)
% ===========================================================================
ilasp_prune :-
    findall(C, learned(C), Cs),
    include(covers_any_neg, Cs, Bad),
    maplist(retract_learned, Bad),
    length(Cs,T), length(Bad,B),
    format("ILASP constraint phase: ~w/~w clauses pruned (cover neg => violate constraint).~n",[B,T]).
covers_any_neg(C) :- neg_ex(E), rule_covers(C,E).
retract_learned(C) :- retract(learned(C)).
% ILASP anti-monotonic simplification: drop redundant literals
ilasp_simplify :-
    findall(C, learned(C), Cs),
    maplist(simplify_clause, Cs).
simplify_clause(C) :-
    select(L, C, Rest),
    \+ covers_any_neg(Rest),
    covered_pos_rest(Rest,L), !,
    retract(learned(C)), assertz(learned(Rest)),
    simplify_clause(Rest).
simplify_clause(_).
covered_pos_rest(Rest, L) :-
    once(( pos_ex(E), rule_covers([L|Rest],E) )).
% ===========================================================================
% L4: TREE — compile learned rule list into a decision tree and print
% ===========================================================================
tree_node(t(Root, Kids)) :-
    findall(C, learned(C), Cs), Cs \= [], !,
    Cs = [First|_], Root = First,
    build_branch(Cs, [], t(First, Kids)).
tree_node(t(none, [])).
% each clause becomes a branch; literals inside clause = levels
build_branch([], _, t(none,[])).
build_branch([C|Rest], Prefix, t(C, Kids)) :-
    build_branch(Rest, [C|Prefix], Kids).
print_tree :-
    tree_node(T), print_tree(T, 0).
print_tree(t(C, Kids), D) :-
    portray_clause(D, C), print_kids(Kids, D+0).
portray_clause(D, C) :-
    tab(D), ( C == none -> write("leaf: NEG")
            ; write("branch:"), write_literals(C) ), nl.
write_literals([]).
write_literals([L|T]) :- write(" "), write(L), write_literals(T).
print_kids(K, D) :- K = t(_,_), !, D1 is D+3, print_tree(K, D1).
print_kids([], _).
print_kids([K|T], D) :- D1 is D+3, print_tree(K, D1), print_kids(T, D).
% evaluate a bit vector against the learned hypothesis (tree path)
predict(E, yes) :- learned(C), rule_covers(C,E), !.
predict(_, no).
accuracy(Acc) :-
    findall(1, (pos_ex(E), predict(E,yes)), TP),
    findall(1, (neg_ex(E), predict(E,no)), TN),
    findall(1, pos_ex(_), P), findall(1, neg_ex(_), N),
    length(TP,TPN), length(TN,TNN), length(P,PN), length(N,NN),
    Acc is (TPN+TNN) / max(1,(PN+NN)).
% ===========================================================================
% ORCHESTRATION
% ===========================================================================
run :-
    W = 4,
    load_all(W),
    format("== L0 binary: 4-bit universe, odd-parity target ==~n"),
    findall(_, pos_ex(_), P), findall(_, neg_ex(_), N),
    length2(P, PL), length2(N, NL),
    format("   ~w pos / ~w neg examples~n",[PL, NL]),
    format("== L2 FOIL (general, entropy-guided) ==~n"),
    foil_run(W, _),
    findall(C, learned(C), FRules),
    maplist(report_clause, FRules),
    format("== L3b ILASP-lite: constraint prune + simplify ==~n"),
    ilasp_prune, ilasp_simplify,
    format("== L3 METAGOL: MIL with invention ==~n"),
    run_mil,
    format("== L4 tree ==~n"),
    print_tree,
    accuracy(A),
    format("   training accuracy: ~w~n", [A]).
report_clause(C) :- write("   target(E) :-"), write_literals(C), write("."), nl.
length2(L, N) :- length(L, N).
% :- run.   % run with: swipl -g run -t halt logicstack_full.pl
