:- module(logos_deduction, [
    derive/4,
    derive_with_provenance/5,
    fixed_point/4,
    query_fact/3,
    query_pattern/4,
    reachable/4,
    shortest_path/5,
    transitive_closure/3,
    stratified_evaluate/4,
    temporal_holds/4,
    temporal_always/3,
    temporal_eventually/3,
    temporal_until/4,
    transition_trace/5,
    validate_rules/1,
    deduction_tests/0
]).

% ============================================================
% EXPLICIT LOGIC PROGRAM
% ============================================================
%
% Rules:
%
% rule(Head, Body)
%
% Body literals:
%
% pos(Atom)
% neg(Atom)
% eq(A,B)
% neq(A,B)
% compare(Op,A,B)
%
% Facts:
%
% fact(Atom, Provenance)
%
% The program is a list of rules.
% The database is a list of facts.
% No assert/retract operations are used.
%
% ============================================================

valid_literal(pos(A)) :-
    callable(A).

valid_literal(neg(A)) :-
    callable(A).

valid_literal(eq(_,_)).

valid_literal(neq(_,_)).

valid_literal(compare(Op,_,_)) :-
    valid_comparison(Op).

valid_comparison(lt).
valid_comparison(le).
valid_comparison(gt).
valid_comparison(ge).
valid_comparison(eq).
valid_comparison(ne).

valid_body([]).

valid_body([L|Ls]) :-
    valid_literal(L),
    valid_body(Ls).

validate_rules([]).

validate_rules([rule(Head,Body)|Rest]) :-
    callable(Head),
    valid_body(Body),
    validate_rules(Rest).

% ============================================================
% LIST OPERATIONS
% ============================================================

d_member(X,[Y|_]) :-
    X = Y.

d_member(X,[_|Rest]) :-
    d_member(X,Rest).

d_member_variant(X,[Y|_]) :-
    X =@= Y,
    !.

d_member_variant(X,[_|Rest]) :-
    d_member_variant(X,Rest).

d_append([],B,B).

d_append([X|Xs],B,[X|Ys]) :-
    d_append(Xs,B,Ys).

d_reverse(Xs,Ys) :-
    d_reverse(Xs,[],Ys).

d_reverse([],Acc,Acc).

d_reverse([X|Xs],Acc,Ys) :-
    d_reverse(Xs,[X|Acc],Ys).

d_unique([],[]).

d_unique([X|Xs],Ys) :-
    d_member_variant(X,Xs),
    !,
    d_unique(Xs,Ys).

d_unique([X|Xs],[X|Ys]) :-
    d_unique(Xs,Ys).

d_take(0,_,[]) :-
    !.

d_take(_,[],[]).

d_take(N,[X|Xs],[X|Ys]) :-
    N > 0,
    M is N-1,
    d_take(M,Xs,Ys).

d_length([],0).

d_length([_|Xs],N) :-
    d_length(Xs,M),
    N is M+1.

% ============================================================
% DATABASE QUERIES
% ============================================================

query_fact(Database,Atom,Provenance) :-
    d_member(fact(Stored,Provenance),Database),
    unify_with_occurs_check(Atom,Stored).

query_pattern(Database,Pattern,Limit,Results) :-
    integer(Limit),
    Limit >= 0,
    findall(
        match(Instance,Source),
        (
            copy_term(Pattern,Instance),
            query_fact(Database,Instance,Source)
        ),
        Matches
    ),
    d_take(Limit,Matches,Results).

fact_present(Database,Atom) :-
    query_fact(Database,Atom,_),
    !.

% ============================================================
% POSITIVE HORN CLAUSE EVALUATION
% ============================================================

positive_body([]).

positive_body([pos(_)|Rest]) :-
    positive_body(Rest).

positive_body([eq(_,_)|Rest]) :-
    positive_body(Rest).

positive_body([neq(_,_)|Rest]) :-
    positive_body(Rest).

positive_body([compare(_,_,_)|Rest]) :-
    positive_body(Rest).

positive_rule(rule(_,Body)) :-
    positive_body(Body).

positive_program([]).

positive_program([Rule|Rest]) :-
    positive_rule(Rule),
    positive_program(Rest).

evaluate_comparison(lt,A,B) :-
    number(A),
    number(B),
    A < B.

evaluate_comparison(le,A,B) :-
    number(A),
    number(B),
    A =< B.

evaluate_comparison(gt,A,B) :-
    number(A),
    number(B),
    A > B.

evaluate_comparison(ge,A,B) :-
    number(A),
    number(B),
    A >= B.

evaluate_comparison(eq,A,B) :-
    number(A),
    number(B),
    A =:= B.

evaluate_comparison(ne,A,B) :-
    number(A),
    number(B),
    A =\= B.

evaluate_positive([],_,[]).

evaluate_positive(
    [pos(Atom)|Rest],
    Database,
    [Source|Sources]
) :-
    query_fact(Database,Atom,Source),
    evaluate_positive(Rest,Database,Sources).

evaluate_positive(
    [eq(A,B)|Rest],
    Database,
    Sources
) :-
    unify_with_occurs_check(A,B),
    evaluate_positive(Rest,Database,Sources).

evaluate_positive(
    [neq(A,B)|Rest],
    Database,
    Sources
) :-
    dif(A,B),
    evaluate_positive(Rest,Database,Sources).

evaluate_positive(
    [compare(Op,A,B)|Rest],
    Database,
    Sources
) :-
    evaluate_comparison(Op,A,B),
    evaluate_positive(Rest,Database,Sources).

% ============================================================
% RULE INSTANTIATION
% ============================================================

instantiate_rule(
    rule(Head,Body),
    Database,
    fact(Head,derived(Sources))
) :-
    copy_term(
        rule(Head,Body),
        rule(FreshHead,FreshBody)
    ),
    evaluate_positive(
        FreshBody,
        Database,
        Sources
    ),
    ground(FreshHead),
    Head = FreshHead.

derive(Program,Database,Rule,Fact) :-
    d_member(Rule,Program),
    positive_rule(Rule),
    instantiate_rule(Rule,Database,Fact).

derive_with_provenance(
    Program,
    Database,
    Rule,
    Atom,
    Provenance
) :-
    derive(
        Program,
        Database,
        Rule,
        fact(Atom,Provenance)
    ).

% ============================================================
% LEAST FIXED POINT
% ============================================================

database_atoms([],[]).

database_atoms(
    [fact(Atom,_)|Rest],
    [Atom|Atoms]
) :-
    database_atoms(Rest,Atoms).

atom_present(Database,Atom) :-
    d_member(fact(Stored,_),Database),
    Stored =@= Atom,
    !.

new_facts([],_,[]).

new_facts([fact(Atom,Source)|Rest],Old,Output) :-
    atom_present(Old,Atom),
    !,
    new_facts(Rest,Old,Output).

new_facts([Fact|Rest],Old,[Fact|Output]) :-
    new_facts(Rest,Old,Output).

fixed_point(Program,Initial,Limit,Result) :-
    validate_rules(Program),
    positive_program(Program),
    integer(Limit),
    Limit >= 0,
    fixed_point_loop(
        Program,
        Initial,
        Limit,
        Result
    ).

fixed_point_loop(_,Database,0,Database).

fixed_point_loop(
    Program,
    Database,
    Remaining,
    Result
) :-
    Remaining > 0,
    findall(
        Fact,
        derive(Program,Database,_,Fact),
        Candidates
    ),
    new_facts(Candidates,Database,Added0),
    unique_facts(Added0,Added),
    (
        Added == []
    ->
        Result = Database
    ;
        d_append(Database,Added,Next),
        N is Remaining-1,
        fixed_point_loop(
            Program,
            Next,
            N,
            Result
        )
    ).

unique_facts([],[]).

unique_facts(
    [fact(Atom,_)|Rest],
    Output
) :-
    atom_present(Rest,Atom),
    !,
    unique_facts(Rest,Output).

unique_facts([Fact|Rest],[Fact|Output]) :-
    unique_facts(Rest,Output).

% ============================================================
% STRATIFIED NEGATION
% ============================================================

% The caller supplies strata in dependency order:
%
% [
%   [rule(...),rule(...)],
%   [rule(...)]
% ]
%
% Negative queries are evaluated only against the
% completed database from earlier strata.
%
% This prevents recursive negation within a stratum.

evaluate_literal(pos(Atom),Database,_) :-
    query_fact(Database,Atom,_).

evaluate_literal(neg(Atom),_,Completed) :-
    ground(Atom),
    \+ fact_present(Completed,Atom).

evaluate_literal(eq(A,B),_,_) :-
    unify_with_occurs_check(A,B).

evaluate_literal(neq(A,B),_,_) :-
    dif(A,B).

evaluate_literal(compare(Op,A,B),_,_) :-
    evaluate_comparison(Op,A,B).

evaluate_body([],_,_).

evaluate_body([L|Ls],Current,Completed) :-
    evaluate_literal(L,Current,Completed),
    evaluate_body(Ls,Current,Completed).

derive_stratified(
    Rules,
    Current,
    Completed,
    fact(Head,derived(stratum))
) :-
    d_member(rule(H,B),Rules),
    copy_term(rule(H,B),rule(Head,Body)),
    evaluate_body(Body,Current,Completed),
    ground(Head).

stratum_loop(_,Database,_,0,Database).

stratum_loop(
    Rules,
    Current,
    Completed,
    Remaining,
    Result
) :-
    Remaining > 0,
    findall(
        Fact,
        derive_stratified(
            Rules,
            Current,
            Completed,
            Fact
        ),
        Candidates
    ),
    new_facts(Candidates,Current,Added0),
    unique_facts(Added0,Added),
    (
        Added == []
    ->
        Result = Current
    ;
        d_append(Current,Added,Next),
        N is Remaining-1,
        stratum_loop(
            Rules,
            Next,
            Completed,
            N,
            Result
        )
    ).

stratified_evaluate(
    [],
    Database,
    _,
    Database
).

stratified_evaluate(
    [Rules|Rest],
    Database,
    Limit,
    Result
) :-
    stratum_loop(
        Rules,
        Database,
        Database,
        Limit,
        Next
    ),
    stratified_evaluate(
        Rest,
        Next,
        Limit,
        Result
    ).

% ============================================================
% GRAPH RELATIONS
% ============================================================

% Graph:
% [
%   edge(A,B,Label),
%   ...
% ]

graph_edge(Graph,A,B) :-
    d_member(edge(A,B,_),Graph).

graph_edge(Graph,A,B,Label) :-
    d_member(edge(A,B,Label),Graph).

reachable(Graph,Start,Target,Path) :-
    graph_walk(
        Graph,
        Start,
        Target,
        [Start],
        Reversed
    ),
    d_reverse(Reversed,Path).

graph_walk(_,Node,Node,Visited,Visited).

graph_walk(
    Graph,
    Current,
    Target,
    Visited,
    Path
) :-
    graph_edge(Graph,Current,Next),
    \+ d_member_variant(Next,Visited),
    graph_walk(
        Graph,
        Next,
        Target,
        [Next|Visited],
        Path
    ).

shortest_path(Graph,Start,Target,Path,Length) :-
    bfs(
        Graph,
        [[Start]],
        Target,
        [Start],
        Reversed
    ),
    d_reverse(Reversed,Path),
    d_length(Path,Nodes),
    Length is Nodes-1.

bfs(_,[],_,_,_) :-
    fail.

bfs(
    _,
    [[Target|Rest]|_],
    Target,
    _,
    [Target|Rest]
) :-
    !.

bfs(
    Graph,
    [[Current|Path]|Queue],
    Target,
    Seen,
    Result
) :-
    findall(
        Next,
        (
            graph_edge(Graph,Current,Next),
            \+ d_member_variant(Next,Seen)
        ),
        RawNeighbors
    ),
    d_unique(RawNeighbors,Neighbors),
    extend_paths(
        Neighbors,
        [Current|Path],
        Extensions
    ),
    d_append(Seen,Neighbors,NewSeen),
    d_append(Queue,Extensions,NewQueue),
    bfs(
        Graph,
        NewQueue,
        Target,
        NewSeen,
        Result
    ).

extend_paths([],_,[]).

extend_paths(
    [Next|Rest],
    Path,
    [[Next|Path]|Paths]
) :-
    extend_paths(Rest,Path,Paths).

transitive_closure(Graph,Nodes,Closure) :-
    findall(
        edge(A,B,reachable),
        (
            d_member(A,Nodes),
            d_member(B,Nodes),
            A \== B,
            reachable(Graph,A,B,_)
        ),
        Raw
    ),
    d_unique(Raw,Closure).

% ============================================================
% TEMPORAL LOGIC OVER FINITE TRACES
% ============================================================

% Trace:
%
% [
%   state(0,[ready]),
%   state(1,[ready,running]),
%   state(2,[done])
% ]
%
% Formula:
%
% atom(Fact)
% not(Formula)
% and(A,B)
% or(A,B)
% next(A)
% eventually(A)
% always(A)
% until(A,B)
%
% This is finite-trace semantics.

trace_at([state(T,Facts)|_],T,Facts) :-
    !.

trace_at([_|Rest],T,Facts) :-
    trace_at(Rest,T,Facts).

trace_suffix(
    [state(T,Facts)|Rest],
    T,
    [state(T,Facts)|Rest]
) :-
    !.

trace_suffix([_|Rest],T,Suffix) :-
    trace_suffix(Rest,T,Suffix).

temporal_holds(Trace,Time,Formula,true) :-
    trace_suffix(Trace,Time,Suffix),
    temporal_eval(Suffix,Formula),
    !.

temporal_holds(Trace,Time,Formula,false) :-
    trace_suffix(Trace,Time,_),
    \+ temporal_holds(
        Trace,
        Time,
        Formula,
        true
    ).

temporal_eval(
    [state(_,Facts)|_],
    atom(Fact)
) :-
    d_member_variant(Fact,Facts).

temporal_eval(Trace,not(A)) :-
    \+ temporal_eval(Trace,A).

temporal_eval(Trace,and(A,B)) :-
    temporal_eval(Trace,A),
    temporal_eval(Trace,B).

temporal_eval(Trace,or(A,B)) :-
    (
        temporal_eval(Trace,A)
    ;
        temporal_eval(Trace,B)
    ).

temporal_eval([_|Rest],next(A)) :-
    Rest \== [],
    temporal_eval(Rest,A).

temporal_eval(Trace,eventually(A)) :-
    temporal_eventually(Trace,A,_).

temporal_eval(Trace,always(A)) :-
    temporal_always(Trace,A,_).

temporal_eval(Trace,until(A,B)) :-
    temporal_until(Trace,A,B,_).

temporal_eventually(Trace, Formula, T) :-
    % Note: the head must be Trace itself, not [state(T,_)|_]=Trace --
    % in Prolog that head term is =/2, not a list, so it never matched.
    Trace = [state(T,_)|_],
    temporal_eval(Trace,Formula),
    !.

temporal_eventually(
    [_|Rest],
    Formula,
    Time
) :-
    temporal_eventually(Rest,Formula,Time).

temporal_always(Trace, Formula, T) :-
    % See temporal_eventually: bind Trace in the body, not as a =/2 head term.
    Trace = [state(T,_)|Rest],
    temporal_eval(Trace,Formula),
    temporal_always_rest(Rest,Formula).

temporal_always_rest([],_).

temporal_always_rest(
    [State|Rest],
    Formula
) :-
    temporal_eval([State|Rest],Formula),
    temporal_always_rest(Rest,Formula).

temporal_until(Trace, _, B, T) :-
    % See temporal_eventually: bind Trace in the body, not as a =/2 head term.
    Trace = [state(T,_)|_],
    temporal_eval(Trace,B),
    !.

temporal_until(
    [State|Rest],
    A,
    B,
    T
) :-
    Rest \== [],
    temporal_eval([State|Rest],A),
    temporal_until(Rest,A,B,T).

% ============================================================
% EXPLICIT TRANSITION SYSTEM
% ============================================================

% Transitions:
%
% transition(Current,Action,Next)
%
% States may be ground terms of any shape.

transition_step(
    Transitions,
    Current,
    Action,
    Next
) :-
    d_member(
        transition(Current,Action,Next),
        Transitions
    ).

transition_trace(
    _,
    State,
    [],
    [State],
    State
).

transition_trace(
    Transitions,
    State,
    [Action|Actions],
    [State|Trace],
    Final
) :-
    transition_step(
        Transitions,
        State,
        Action,
        Next
    ),
    transition_trace(
        Transitions,
        Next,
        Actions,
        Trace,
        Final
    ).

% ============================================================
% PROVENANCE QUERIES
% ============================================================

provenance_of(Database,Atom,Source) :-
    query_fact(Database,Atom,Source).

provenance_leaves(
    source(ID),
    [ID]
).

provenance_leaves(
    derived(Sources),
    Leaves
) :-
    provenance_list(Sources,Leaves).

provenance_leaves(
    derived(stratum),
    []
).

provenance_leaves(
    ID,
    [ID]
) :-
    atomic(ID).

provenance_list([],[]).

provenance_list([P|Ps],Leaves) :-
    provenance_leaves(P,First),
    provenance_list(Ps,Rest),
    d_append(First,Rest,All),
    d_unique(All,Leaves).

% ============================================================
% TESTS
% ============================================================

deduction_tests :-
    test_fixed_point,
    test_graph,
    test_temporal,
    test_stratified,
    test_transitions.

test_fixed_point :-
    Rules = [
        rule(
            ancestor(X,Y),
            [pos(parent(X,Y))]
        ),
        rule(
            ancestor(X,Z),
            [
                pos(parent(X,Y)),
                pos(ancestor(Y,Z))
            ]
        )
    ],
    Facts = [
        fact(parent(a,b),source(e1)),
        fact(parent(b,c),source(e2)),
        fact(parent(c,d),source(e3))
    ],
    fixed_point(Rules,Facts,10,Result),
    fact_present(Result,ancestor(a,d)),
    fact_present(Result,ancestor(a,c)),
    fact_present(Result,ancestor(b,d)).

test_graph :-
    Graph = [
        edge(a,b,one),
        edge(b,c,two),
        edge(c,d,three),
        edge(a,d,direct)
    ],
    shortest_path(
        Graph,a,d,[a,d],1
    ),
    reachable(
        Graph,a,c,[a,b,c]
    ).

test_temporal :-
    Trace = [
        state(0,[ready]),
        state(1,[ready,running]),
        state(2,[done])
    ],
    temporal_holds(
        Trace,
        0,
        eventually(atom(done)),
        true
    ),
    temporal_holds(
        Trace,
        0,
        always(atom(ready)),
        false
    ),
    temporal_holds(
        Trace,
        0,
        until(
            atom(ready),
            atom(done)
        ),
        true
    ).

test_stratified :-
    Facts = [
        fact(person(alice),source(p1)),
        fact(person(bob),source(p2)),
        fact(blocked(bob),source(p3))
    ],
    Strata = [
        [
            rule(
                allowed(X),
                [
                    pos(person(X)),
                    neg(blocked(X))
                ]
            )
        ]
    ],
    stratified_evaluate(
        Strata,
        Facts,
        5,
        Result
    ),
    fact_present(Result,allowed(alice)),
    \+ fact_present(Result,allowed(bob)).

test_transitions :-
    Transitions = [
        transition(idle,start,running),
        transition(running,finish,done)
    ],
    transition_trace(
        Transitions,
        idle,
        [start,finish],
        [idle,running,done],
        done
    ).
