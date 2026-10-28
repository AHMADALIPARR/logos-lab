% Metagol kernel: induce ancestor/2 from parent/2.
% Requires Metagol loaded as metagol.pl in the Prolog search path.
:- use_module('metagol').
:- metagol:max_clauses(2).
:- metagol:body_pred(parent/2).
:- metagol:body_pred(ancestor/2).

metarule(identity,[P,Q],([P,A,B] :- [[Q,A,B]])).
metarule(chain,[P,Q,R],([P,A,B] :- [[Q,A,C],[R,C,B]])).

parent(ada,bob).
parent(bob,cy).
parent(cy,dee).

positive([ancestor(ada,bob),ancestor(ada,cy),ancestor(ada,dee),ancestor(bob,dee)]).
negative([ancestor(bob,ada),ancestor(dee,ada),ancestor(cy,bob)]).

run :- positive(Pos), negative(Neg), learn(Pos,Neg,H), pprint(H).
