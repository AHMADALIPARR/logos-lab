% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr
% logicstack.pl — FOIL + Metagol + Tree in pure ISO Prolog
% ============================================================
% L0: BINARY SUBSTRATE
% ============================================================
bit(0). bit(1).
band(A,B,R) :- R is A /\ B.
bor(A,B,R)  :- R is A \/ B.
bxor(A,B,R) :- R is A xor B.
% bits(n, Bits): enumerate all bit vectors of width n
bits(0,[]).
bits(N,[B|T]) :- N>0, N1 is N-1, bit(B), bits(N1,T).
% code facts: classify by XOR parity + AND mask
mk_examples(N, Pos, Neg) :-
    findall(E,(bits(N,E),parity_good(E)),Pos),
    findall(E,(bits(N,E),\+ parity_good(E)),Neg).
parity_good(E) :- parity_good(E,0).
parity_good([0|T],A) :- parity_good(T,A).
parity_good([1|T],A) :- A1 is 1-A, parity_good(T,A1).
parity_good([],1).   % odd number of 1s
% ============================================================
% L1: KNOWLEDGE BASE / unification is built in
% ============================================================
:- dynamic invented/2, bk_/2.
bk_(even,[]).
bk_(odd,[1]).
% example protocol: ex(E) means target holds on bit-vector E
:- dynamic ex/1.
load_kb :-
    retractall(ex(_)), retractall(invented(_,_)),
    mk_examples(4, Pos, _),
    maplist(assert_ex, Pos).
assert_ex(E) :- assertz(ex(E)).
% ============================================================
% L2: FOIL — literal-by-literal, information gain
% ============================================================
% candidate body literals: chains over successor on positions
succ_lit(p0,E, T) :- nth0(0,E,T).
succ_lit(p1,E, T) :- nth0(1,E,T).
succ_lit(p2,E, T) :- nth0(2,E,T).
succ_lit(p3,E, T) :- nth0(3,E,T).
succ_lit(and01, E, T) :- nth0(0,E,A), nth0(1,E,B), T is A/\B.
succ_lit(and23, E, T) :- nth0(2,E,A), nth0(3,E,B), T is A/\B.
succ_lit(xor01, E, T) :- nth0(0,E,A), nth0(1,E,B), T is A xor B.
succ_lit(xor23, E, T) :- nth0(2,E,A), nth0(3,E,B), T is A xor B.
% covers(Rule, E): rule = list of (Literal, Value) constraints
covers([], _).
covers([L-V|Rest], E) :- succ_lit(L,E,V), covers(Rest,E).
% entropy / gain
p_pos([], _, _, 0) :- !.
p_pos(Es, Pos, _Neg, P) :-
    length(Es,Len),
    include(covers_rule(Pos), Es, TP),
    length(TP, TPN),
    P is TPN / Len.
covers_rule(Rule, E) :- covers(Rule,E).
entropy(P,E) :- P =< 0.0000001, !, E is 0.0.
entropy(P,E) :- P >= 0.9999999, !, E is 0.0.
entropy(P,E) :- E is -(P*log(P) + (1-P)*log(1-P)).
gain(Rule, Pos, Neg, G) :-
    length(Pos, PN), length(Neg, NN), Tot is PN+NN,
    Tot > 0, P0 is PN/Tot, entropy(P0,E0),
    append(Pos,Neg,All),
    include(covers_rule(Rule),All,Sub),
    length(Sub,SN),
    (  SN =:= 0 -> G is 0.0
    ;  include(in_pos(Pos),Sub,SP), length(SP,SPN),
       length(Pos,PN0),
       length(Neg,NN0), PN0>0, NN0>0,
       P1 is SPN/SN, entropy(P1,E1),
       (  P1 > P0 -> G is E0 - (SN/Tot)*E1   % only literals that raise precision
       ;  G is 0.0 ) ).
in_pos(Pos, E) :- memberchk(E,Pos).
% FOIL loop: greedy add best literal until no negatives covered
foil(Rule) :- load_kb, foil_body([], Rule).
foil_body(Body, Body) :-
    covered_neg(Body,Neg),
    Neg = [], !.
foil_body(Body, Final) :-
    covered_neg(Body,Neg), Neg \= [],
    best_literal(Body, L-V), !,
    foil_body([L-V|Body], Final).
% plateau (parity: no single literal raises precision): look ahead two literals
foil_body(Body, Final) :-
    covered_neg(Body,Neg), Neg \= [],
    best_pair(Body, P1, P2), !,
    foil_body([P2,P1|Body], Final).
foil_body(B, B).
% separate & conquer: learn clauses until every positive is covered
:- dynamic done/1.
foil_all(Rules) :- load_kb, retractall(done(_)), foil_all_(Rules).
foil_all_([R|Rs]) :-
    ex(E0), \+ done(E0), !,
    foil_body([], R),
    findall(E,(ex(E),\+ done(E),covers(R,E)),New), New \== [],
    forall(member(E,New), assertz(done(E))),
    foil_all_(Rs).
foil_all_([]).
covered_pos(Body, Pos) :- findall(E,(ex(E),\+ done(E),covers(Body,E)),Pos).
covered_neg(Body, Neg) :-
    findall(E,(mk_examples(4,_,NegAll),member(E,NegAll),covers(Body,E)),Neg).
best_literal(Body, Best) :-
    covered_pos(Body,Pos), covered_neg(Body,Neg),
    findall(G-(L-V),
            ( cand_literal(Body, L-V),
              gain([L-V|Body],Pos,Neg,G), G > 0 ),
            Cands),
    Cands \= [],
    max_key(Cands, _-Best).
best_pair(Body, L1-V1, L2-V2) :-
    covered_pos(Body,Pos), covered_neg(Body,Neg),
    findall((G-S)-(L1-V1,L2-V2),
            ( cand_literal(Body, L1-V1),
              cand_literal([L1-V1|Body], L2-V2),
              gain([L2-V2,L1-V1|Body],Pos,Neg,G), G > 0,
              findall(E,(member(E,Pos),covers([L2-V2,L1-V1|Body],E)),Sx), length(Sx,S) ),
            Cands),
    Cands \= [],
    max_key(Cands, _-(L1-V1,L2-V2)).   % ties: more positives covered
cand_literal(Body, L-V) :-
    succ_member(L), member(V,[0,1]), \+ member(L-_,Body).
succ_member(p0). succ_member(p1). succ_member(p2). succ_member(p3).
succ_member(and01). succ_member(and23). succ_member(xor01). succ_member(xor23).
max_key([K-V|T], MK-MV) :- max_key(T,K-V,MK-MV).
max_key([],K-V,K-V).
max_key([K1-V1|T],K-V,MK-MV) :-
    ( K1 @>= K -> max_key(T,K1-V1,MK-MV)
    ; max_key(T,K-V,MK-MV) ).
% ============================================================
% L3: METAGOL — meta-interpretive learning
% meta-rules: chain P(A,B) :- Q(A,C), R(C,B)
%             ident P(A,B) :- Q(A,B)
%             proj  P(A)   :- Q(A,B)
% invented predicates are proven by invented/2 clauses
% ============================================================
meta_chain(P,Q,R) :-
    findall(A-B,(call(Q,A,C),call(R,C,B)),L0), sort(L0,L),
    retractall(invented(P,_)), assertz(invented(P,L)).
assertz_body(P,A,B) :- invented(P,Cls), !, member(A-B,Cls).
assertz_body(P,A,B) :- call(P,A,B).
% BK relations over positions: next(A,B)
next(0,1). next(1,2). next(2,3).
value(pos(E,0), V) :- nth0(0,E,V).
value(pos(E,1), V) :- nth0(1,E,V).
value(pos(E,2), V) :- nth0(2,E,V).
value(pos(E,3), V) :- nth0(3,E,V).
% examples for the target f(A,B) (reachability over next)
mil_pos(0,1). mil_pos(1,2). mil_pos(2,3). mil_pos(0,2). mil_pos(0,3). mil_pos(1,3).
mil_neg(3,0). mil_neg(2,0). mil_neg(3,1).
mil_prove(Prog,A,B) :- member(Cl,Prog), clause_holds(Cl,A,B).
clause_holds(ident(Q),A,B) :- assertz_body(Q,A,B).
clause_holds(chain(Q,R),A,B) :- assertz_body(Q,A,C), assertz_body(R,C,B).
mil_ok(Prog) :-
    forall(mil_pos(A,B), mil_prove(Prog,A,B)),
    \+ ( mil_neg(A,B), mil_prove(Prog,A,B) ).
mil_cover(Prog, NP, NN) :-
    findall(x,(mil_pos(A,B),mil_prove(Prog,A,B)),Ps), length(Ps,NP),
    findall(x,(mil_neg(A,B),mil_prove(Prog,A,B)),Ns), length(Ns,NN).
% search: single metarule first; if inconsistent, invent inv1 by chaining and retry
mil_learn(Prog) :-
    (  member(Prog,[[ident(next)],[chain(next,next)]]), mil_ok(Prog) -> true
    ;  meta_chain(inv1,next,next),
       member(Prog,[[ident(next),ident(inv1)],
                    [ident(next),ident(inv1),chain(next,inv1)]]), mil_ok(Prog) ), !.
% metagol(Target, MetaRuleIds, Clauses) — invent by SLD failure
metagol :-
    foil_all(Rules),
    forall(member(R,Rules),
           ( reverse(R,RR), format("FOIL rule: ~w~n", [RR]) )),
    mil_learn(Prog),
    mil_cover(Prog,NP,NN),
    ( invented(inv1,Inv) -> format("MIL: invented inv1 = next;next  ~w~n",[Inv]) ; true ),
    format("MIL program: ~w   (covers ~w/6 pos, ~w/3 neg)~n",[Prog,NP,NN]),
    write_tree(Rules),
    accuracy(Rules, Acc),
    format("training accuracy: ~w~n",[Acc]).
accuracy(Rules, Acc) :-
    mk_examples(4,Pos,Neg),
    include(any_covers(Rules),Pos,TP), length(TP,A),
    exclude(any_covers(Rules),Neg,TN), length(TN,B),
    length(Pos,PN), length(Neg,NN),
    Acc is (A+B)/(PN+NN).
any_covers(Rules,E) :- member(R,Rules), covers(R,E), !.
% ============================================================
% L4: TREE — turn rules into a decision tree
% ============================================================
% node(label, children): literal splits data like a tree
tree(Rules, node(target, Kids)) :-
    findall(node(clause(N),Sub),
            ( nth1(N,Rules,R), reverse(R,RR), split_on(RR, Sub) ),
            Kids).
split_on([], []).
split_on([L-V|Rest], [leaf(L,V,Sub)|Kids]) :-
    findall(E,(ex(E),covers([L-V|Rest],E)),Sub),
    split_on(Rest, Kids).
write_tree(Rules) :-
    tree(Rules, T), portray_tree(T, 0).
portray_tree(node(R,_), D) :-
    tab(D), format("node ~w~n",[R]), fail.
portray_tree(node(_,Kids), D) :- portray_kids(Kids, D).
portray_tree(leaf(L,V,_), D) :-
    tab(D), format("leaf ~w=~w~n",[L,V]).
portray_kids([], _).
portray_kids([K|T], D) :- D1 is D+2, portray_tree(K,D1), portray_kids(T,D).
