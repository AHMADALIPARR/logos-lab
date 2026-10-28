:- module(logos, [
    empty_state/1,
    insert_word/7,
    insert_sense/6,
    insert_evidence/7,
    insert_relation/7,
    insert_segmentation/6,
    lookup_word/3,
    word_slices/3,
    reconstruct/3,
    validate_segmentation/2,
    ancestor/3,
    ancestry_path/4,
    shared_ancestor/4,
    morphological_root/3,
    lexical_facts/2,
    prove/4,
    prove_all/5,
    unify/4,
    reify/3,
    fd_solve/4,
    fd_all/4,
    probability/4,
    world_probability/3,
    semiring_evaluate/5,
    causal_step/4,
    causal_history/5,
    logos_selftest/0
]).

% ============================================================
% DATA MODEL
% ============================================================

empty_state(
    state([], [], [], [], [])
).

% state(
%   Words,
%   Senses,
%   Evidence,
%   Relations,
%   Segmentations
% )

% word(
%   ID,
%   Language,
%   Form,
%   Period,
%   Script,
%   Source
% )

% sense(
%   ID,
%   WordID,
%   Gloss,
%   Category,
%   Source
% )

% evidence(
%   ID,
%   Subject,
%   Predicate,
%   Object,
%   Source,
%   Status
% )

% relation(
%   ID,
%   Child,
%   Parent,
%   Type,
%   Source,
%   Status
% )

% segmentation(
%   ID,
%   WordID,
%   Kind,
%   Parts,
%   Source
% )

% part(
%   Start,
%   End,
%   Form,
%   Role
% )

% ============================================================
% BASIC RELATIONAL OPERATIONS
% ============================================================

logos_member(X, [Y|_]) :-
    X = Y.

logos_member(X, [_|Rest]) :-
    logos_member(X, Rest).

logos_member_eq(X, [Y|_]) :-
    X == Y,
    !.

logos_member_eq(X, [_|Rest]) :-
    logos_member_eq(X, Rest).

logos_append([], B, B).

logos_append([A|Rest], B, [A|Output]) :-
    logos_append(Rest, B, Output).

logos_reverse(Input, Output) :-
    logos_reverse_acc(Input, [], Output).

logos_reverse_acc([], Acc, Acc).

logos_reverse_acc([X|Rest], Acc, Result) :-
    logos_reverse_acc(Rest, [X|Acc], Result).

logos_length([], 0).

logos_length([_|Rest], Length) :-
    logos_length(Rest, Previous),
    Length is Previous + 1.

logos_sum([], 0).

logos_sum([X|Rest], Total) :-
    logos_sum(Rest, Previous),
    Total is Previous + X.

logos_product([], 1).

logos_product([X|Rest], Total) :-
    logos_product(Rest, Previous),
    Total is Previous * X.

logos_take(0, _, []) :-
    !.

logos_take(_, [], []).

logos_take(N, [X|Rest], [X|Output]) :-
    N > 0,
    Next is N - 1,
    logos_take(Next, Rest, Output).

logos_drop(0, List, List) :-
    !.

logos_drop(N, [_|Rest], Result) :-
    N > 0,
    Next is N - 1,
    logos_drop(Next, Rest, Result).

logos_range(Start, End, []) :-
    Start >= End,
    !.

logos_range(Start, End, [Start|Rest]) :-
    Start < End,
    Next is Start + 1,
    logos_range(Next, End, Rest).

logos_unique([], []).

logos_unique([X|Rest], Output) :-
    logos_member_eq(X, Rest),
    !,
    logos_unique(Rest, Output).

logos_unique([X|Rest], [X|Output]) :-
    logos_unique(Rest, Output).

logos_nonempty_atom(X) :-
    atom(X),
    X \== ''.

logos_valid_status(attested).
logos_valid_status(reconstructed).
logos_valid_status(disputed).
logos_valid_status(inferred).

% ============================================================
% LEXICAL STORAGE
% ============================================================

insert_word(
    state(W, S, E, R, M),
    word(ID, Language, Form, Period, Script, Source),
    state(
        [word(ID, Language, Form, Period, Script, Source)|W],
        S, E, R, M
    ),
    ID,
    Language,
    Form,
    Source
) :-
    logos_nonempty_atom(ID),
    logos_nonempty_atom(Language),
    logos_nonempty_atom(Form),
    logos_nonempty_atom(Script),
    logos_nonempty_atom(Source),
    \+ logos_member(
        word(ID, _, _, _, _, _),
        W
    ).

insert_sense(
    state(W, S, E, R, M),
    sense(ID, WordID, Gloss, Category, Source),
    state(
        W,
        [sense(ID, WordID, Gloss, Category, Source)|S],
        E, R, M
    ),
    ID,
    WordID,
    Gloss
) :-
    logos_member(
        word(WordID, _, _, _, _, _),
        W
    ),
    logos_nonempty_atom(ID),
    logos_nonempty_atom(Gloss),
    logos_nonempty_atom(Category),
    logos_nonempty_atom(Source),
    \+ logos_member(
        sense(ID, _, _, _, _),
        S
    ).

insert_evidence(
    state(W, S, E, R, M),
    evidence(ID, Subject, Predicate, Object, Source, Status),
    state(
        W, S,
        [evidence(ID, Subject, Predicate, Object, Source, Status)|E],
        R, M
    ),
    ID,
    Subject,
    Predicate,
    Object
) :-
    logos_nonempty_atom(ID),
    logos_nonempty_atom(Predicate),
    logos_nonempty_atom(Source),
    logos_valid_status(Status),
    \+ logos_member(
        evidence(ID, _, _, _, _, _),
        E
    ).

lookup_word(
    state(W, _, _, _, _),
    ID,
    word(ID, Language, Form, Period, Script, Source)
) :-
    logos_member(
        word(ID, Language, Form, Period, Script, Source),
        W
    ).

lookup_form(
    state(W, _, _, _, _),
    Language,
    Form,
    ID
) :-
    logos_member(
        word(ID, Language, Form, _, _, _),
        W
    ).

lookup_sense(
    state(_, S, _, _, _),
    WordID,
    sense(ID, WordID, Gloss, Category, Source)
) :-
    logos_member(
        sense(ID, WordID, Gloss, Category, Source),
        S
    ).

lookup_evidence(
    state(_, _, E, _, _),
    Subject,
    Predicate,
    evidence(ID, Subject, Predicate, Object, Source, Status)
) :-
    logos_member(
        evidence(ID, Subject, Predicate, Object, Source, Status),
        E
    ).

% ============================================================
% UNICODE CODE-POINT SLICING
% ============================================================

word_slices(State, ID, Slices) :-
    lookup_word(
        State,
        ID,
        word(ID, _, Form, _, _, _)
    ),
    atom_codes(Form, Codes),
    enumerate_codes(Codes, 0, Slices).

enumerate_codes([], _, []).

enumerate_codes(
    [Code|Rest],
    Index,
    [unit(Index, Code, Character)|Output]
) :-
    char_code(Character, Code),
    Next is Index + 1,
    enumerate_codes(Rest, Next, Output).

reconstruct(State, ID, Reconstructed) :-
    word_slices(State, ID, Slices),
    slice_codes(Slices, Codes),
    atom_codes(Reconstructed, Codes).

slice_codes([], []).

slice_codes(
    [unit(_, Code, _)|Rest],
    [Code|Output]
) :-
    slice_codes(Rest, Output).

valid_reconstruction(State, ID) :-
    lookup_word(
        State,
        ID,
        word(ID, _, Original, _, _, _)
    ),
    reconstruct(State, ID, Reconstructed),
    Original == Reconstructed.

utf8_width(Code, 1) :-
    integer(Code),
    Code >= 0,
    Code =< 127,
    !.

utf8_width(Code, 2) :-
    integer(Code),
    Code >= 128,
    Code =< 2047,
    !.

utf8_width(Code, 3) :-
    integer(Code),
    Code >= 2048,
    Code =< 65535,
    (Code < 55296 ; Code > 57343),
    !.

utf8_width(Code, 4) :-
    integer(Code),
    Code >= 65536,
    Code =< 1114111.

utf8_size([], 0).

utf8_size([Code|Rest], Total) :-
    utf8_width(Code, Width),
    utf8_size(Rest, Remaining),
    Total is Width + Remaining.

word_utf8_size(State, ID, Bytes) :-
    lookup_word(
        State,
        ID,
        word(ID, _, Form, _, _, _)
    ),
    atom_codes(Form, Codes),
    utf8_size(Codes, Bytes).

% ============================================================
% MORPHOLOGICAL SEGMENTATION
% ============================================================

insert_segmentation(
    state(W, S, E, R, M),
    segmentation(ID, WordID, Kind, Parts, Source),
    state(
        W, S, E, R,
        [segmentation(ID, WordID, Kind, Parts, Source)|M]
    ),
    ID,
    WordID,
    Parts,
    Source
) :-
    logos_nonempty_atom(ID),
    logos_nonempty_atom(Kind),
    logos_nonempty_atom(Source),
    logos_member(
        word(WordID, _, Form, _, _, _),
        W
    ),
    \+ logos_member(
        segmentation(ID, _, _, _, _),
        M
    ),
    atom_codes(Form, Codes),
    logos_length(Codes, Length),
    validate_parts(Parts, 0, Length).

validate_parts([], End, End).

validate_parts(
    [part(Start, End, Form, Role)|Rest],
    Expected,
    Total
) :-
    integer(Start),
    integer(End),
    Start =:= Expected,
    End > Start,
    End =< Total,
    logos_nonempty_atom(Form),
    logos_nonempty_atom(Role),
    validate_parts(Rest, End, Total).

validate_segmentation(
    state(W, _, _, _, M),
    ID
) :-
    logos_member(
        segmentation(ID, WordID, _, Parts, _),
        M
    ),
    logos_member(
        word(WordID, _, Original, _, _, _),
        W
    ),
    atom_codes(Original, WordCodes),
    logos_length(WordCodes, Length),
    validate_parts(Parts, 0, Length),
    validate_part_contents(Parts, WordCodes).

validate_part_contents([], _).

validate_part_contents(
    [part(Start, End, Form, _)|Rest],
    WordCodes
) :-
    Width is End - Start,
    logos_drop(Start, WordCodes, Tail),
    logos_take(Width, Tail, SegmentCodes),
    atom_codes(Form, SegmentCodes),
    validate_part_contents(Rest, WordCodes).

morphological_root(State, WordID, Root) :-
    State = state(_, _, _, _, Segmentations),
    logos_member(
        segmentation(SegID, WordID, _, Parts, _),
        Segmentations
    ),
    validate_segmentation(State, SegID),
    logos_member(
        part(_, _, Root, root),
        Parts
    ).

morphological_prefix(State, WordID, Prefix) :-
    State = state(_, _, _, _, Segmentations),
    logos_member(
        segmentation(SegID, WordID, _, Parts, _),
        Segmentations
    ),
    validate_segmentation(State, SegID),
    logos_member(
        part(_, _, Prefix, prefix),
        Parts
    ).

morphological_suffix(State, WordID, Suffix) :-
    State = state(_, _, _, _, Segmentations),
    logos_member(
        segmentation(SegID, WordID, _, Parts, _),
        Segmentations
    ),
    validate_segmentation(State, SegID),
    logos_member(
        part(_, _, Suffix, suffix),
        Parts
    ).

shared_morphological_root(State, A, B, Root) :-
    dif(A, B),
    morphological_root(State, A, Root),
    morphological_root(State, B, Root).

% ============================================================
% ETYMOLOGICAL GRAPH
% ============================================================

historical_edge(derived_from).
historical_edge(borrowed_from).
historical_edge(inherited_from).
historical_edge(calqued_from).

lexical_edge(cognate_of).
lexical_edge(related_to).
lexical_edge(translation_of).
lexical_edge(semantic_shift).
lexical_edge(compound_of).

valid_edge_type(derived_from).
valid_edge_type(borrowed_from).
valid_edge_type(inherited_from).
valid_edge_type(calqued_from).
valid_edge_type(cognate_of).
valid_edge_type(related_to).
valid_edge_type(translation_of).
valid_edge_type(semantic_shift).
valid_edge_type(compound_of).

insert_relation(
    state(W, S, E, R, M),
    relation(ID, Child, Parent, Type, Source, Status),
    state(
        W, S, E,
        [relation(ID, Child, Parent, Type, Source, Status)|R],
        M
    ),
    ID,
    Child,
    Parent,
    Type
) :-
    logos_nonempty_atom(ID),
    logos_nonempty_atom(Source),
    logos_valid_status(Status),
    valid_edge_type(Type),
    Child \== Parent,
    logos_member(word(Child, _, _, _, _, _), W),
    logos_member(word(Parent, _, _, _, _, _), W),
    \+ logos_member(relation(ID, _, _, _, _, _), R),
    (
        historical_edge(Type)
    ->
        \+ ancestor(
            state(W, S, E, R, M),
            Parent,
            Child
        )
    ;
        true
    ).

direct_parent(
    state(_, _, _, R, _),
    Child,
    Parent
) :-
    logos_member(
        relation(_, Child, Parent, Type, _, _),
        R
    ),
    historical_edge(Type).

ancestor(State, Child, Parent) :-
    Child \== Parent,
    ancestry_walk(
        State,
        Child,
        Parent,
        [Child],
        _
    ).

ancestry_path(State, Child, Parent, Path) :-
    Child \== Parent,
    ancestry_walk(
        State,
        Child,
        Parent,
        [Child],
        Reverse
    ),
    logos_reverse(Reverse, Path).

ancestry_walk(
    State,
    Current,
    Target,
    Visited,
    Path
) :-
    direct_parent(State, Current, Next),
    \+ logos_member_eq(Next, Visited),
    (
        Next == Target
    ->
        Path = [Next|Visited]
    ;
        ancestry_walk(
            State,
            Next,
            Target,
            [Next|Visited],
            Path
        )
    ).

shared_ancestor(State, A, B, Root) :-
    dif(A, B),
    ancestor(State, A, Root),
    ancestor(State, B, Root).

etymological_sources(
    state(_, _, _, Relations, _),
    Child,
    Parent,
    Sources
) :-
    findall(
        Source,
        (
            logos_member(
                relation(_, Child, Parent, Type, Source, _),
                Relations
            ),
            historical_edge(Type)
        ),
        Sources
    ).

% ============================================================
% PROLOG FACT GENERATION
% ============================================================

lexical_facts(
    state(W, S, E, R, M),
    Facts
) :-
    words_to_facts(W, FW),
    senses_to_facts(S, FS),
    evidence_to_facts(E, FE),
    relations_to_facts(R, FR),
    segments_to_facts(M, FM),
    logos_append(FW, FS, F1),
    logos_append(F1, FE, F2),
    logos_append(F2, FR, F3),
    logos_append(F3, FM, Facts).

words_to_facts([], []).

words_to_facts(
    [word(ID, L, F, P, Script, Source)|Rest],
    [fact(lexeme(ID,L,F,P,Script,Source))|Facts]
) :-
    words_to_facts(Rest, Facts).

senses_to_facts([], []).

senses_to_facts(
    [sense(ID,W,G,C,S)|Rest],
    [fact(sense(ID,W,G,C,S))|Facts]
) :-
    senses_to_facts(Rest, Facts).

evidence_to_facts([], []).

evidence_to_facts(
    [evidence(ID,A,P,B,S,Status)|Rest],
    [fact(evidence(ID,A,P,B,S,Status))|Facts]
) :-
    evidence_to_facts(Rest, Facts).

relations_to_facts([], []).

relations_to_facts(
    [relation(ID,A,B,T,S,Status)|Rest],
    [fact(relation(ID,A,B,T,S,Status))|Facts]
) :-
    relations_to_facts(Rest, Facts).

segments_to_facts([], []).

segments_to_facts(
    [segmentation(ID,W,Kind,Parts,Source)|Rest],
    [fact(segmentation(ID,W,Kind,Parts,Source))|Facts]
) :-
    segments_to_facts(Rest, Facts).

% ============================================================
% SYMBOLIC TERMS AND SUBSTITUTIONS
% ============================================================

% Logic variables: lv(Identifier)
% Structures: node(Functor, Arguments)
% Constants: atom or number
% Substitutions: [binding(ID, Term), ...]

walk(lv(ID), Substitution, Value) :-
    logos_member(
        binding(ID, Bound),
        Substitution
    ),
    !,
    walk(Bound, Substitution, Value).

walk(lv(ID), _, lv(ID)).

walk(node(F, Args), _, node(F, Args)).

walk(Term, _, Term) :-
    atomic(Term).

occurs(ID, Term, Substitution) :-
    walk(Term, Substitution, Value),
    (
        Value = lv(ID)
    ->
        true
    ;
        Value = node(_, Args)
    ->
        occurs_list(ID, Args, Substitution)
    ;
        fail
    ).

occurs_list(ID, [X|_], S) :-
    occurs(ID, X, S),
    !.

occurs_list(ID, [_|Rest], S) :-
    occurs_list(ID, Rest, S).

bind_variable(ID, Term, S0, S1) :-
    \+ occurs(ID, Term, S0),
    S1 = [binding(ID, Term)|S0].

unify(A, B, S0, S1) :-
    walk(A, S0, X),
    walk(B, S0, Y),
    unify_walked(X, Y, S0, S1).

unify_walked(X, Y, S, S) :-
    X == Y,
    !.

unify_walked(lv(ID), Y, S0, S1) :-
    !,
    bind_variable(ID, Y, S0, S1).

unify_walked(X, lv(ID), S0, S1) :-
    !,
    bind_variable(ID, X, S0, S1).

unify_walked(
    node(F, ArgsA),
    node(F, ArgsB),
    S0,
    S1
) :-
    !,
    unify_arguments(ArgsA, ArgsB, S0, S1).

unify_walked(X, Y, S, S) :-
    atomic(X),
    atomic(Y),
    X == Y.

unify_arguments([], [], S, S).

unify_arguments(
    [A|As],
    [B|Bs],
    S0,
    S2
) :-
    unify(A, B, S0, S1),
    unify_arguments(As, Bs, S1, S2).

reify(lv(ID), S, Result) :-
    !,
    walk(lv(ID), S, Value),
    (
        Value == lv(ID)
    ->
        Result = lv(ID)
    ;
        reify(Value, S, Result)
    ).

reify(node(F, Args), S, node(F, Results)) :-
    !,
    reify_list(Args, S, Results).

reify(X, _, X).

reify_list([], _, []).

reify_list([X|Xs], S, [Y|Ys]) :-
    reify(X, S, Y),
    reify_list(Xs, S, Ys).

% ============================================================
% VARIABLE STANDARDIZATION
% ============================================================

% A rule is:
% rule(Head, Body)
%
% Body is a list of symbolic nodes.
% Each application receives a fresh variable namespace.

rename_term(lv(ID), Stamp, lv(Stamp-ID)) :-
    !.

rename_term(
    node(F, Args),
    Stamp,
    node(F, Renamed)
) :-
    !,
    rename_list(Args, Stamp, Renamed).

rename_term(X, _, X).

rename_list([], _, []).

rename_list([X|Xs], Stamp, [Y|Ys]) :-
    rename_term(X, Stamp, Y),
    rename_list(Xs, Stamp, Ys).

rename_rule(
    rule(Head, Body),
    Stamp,
    rule(NewHead, NewBody)
) :-
    rename_term(Head, Stamp, NewHead),
    rename_list(Body, Stamp, NewBody).

% ============================================================
% DEPTH-BOUNDED HORN RESOLUTION
% ============================================================

prove(Program, Query, Depth, Answer) :-
    integer(Depth),
    Depth >= 0,
    solve(
        Program,
        [Query],
        [],
        Depth,
        0,
        FinalSubstitution
    ),
    reify(Query, FinalSubstitution, Answer).

prove_all(Program, Query, Depth, Limit, Answers) :-
    integer(Limit),
    Limit >= 0,
    findall(
        Answer,
        prove(Program, Query, Depth, Answer),
        All
    ),
    logos_take(Limit, All, Answers).

solve(_, [], S, _, _, S).

solve(
    Program,
    [Goal|Rest],
    S0,
    Depth,
    Stamp0,
    Final
) :-
    Depth > 0,
    logos_member(Rule, Program),
    rename_rule(Rule, Stamp0, rule(Head, Body)),
    unify(Goal, Head, S0, S1),
    logos_append(Body, Rest, NextGoals),
    NextDepth is Depth - 1,
    NextStamp is Stamp0 + 1,
    solve(
        Program,
        NextGoals,
        S1,
        NextDepth,
        NextStamp,
        Final
    ).

% ============================================================
% FINITE DOMAIN CONSTRAINTS
% ============================================================

% Domains:
% domain(Name, Low, High)
%
% Constraints:
% eq(X,Y)
% neq(X,Y)
% lt(X,Y)
% le(X,Y)
% add(X,Y,Z)
% all_different([X,Y,...])
%
% Variables are represented by v(Name).
% Constants are numbers.

fd_value(v(Name), Env, Value) :-
    logos_member(Name-Value, Env).

fd_value(Number, _, Number) :-
    number(Number).

fd_check(eq(A,B), Env) :-
    fd_value(A, Env, X),
    fd_value(B, Env, Y),
    X =:= Y.

fd_check(neq(A,B), Env) :-
    fd_value(A, Env, X),
    fd_value(B, Env, Y),
    X =\= Y.

fd_check(lt(A,B), Env) :-
    fd_value(A, Env, X),
    fd_value(B, Env, Y),
    X < Y.

fd_check(le(A,B), Env) :-
    fd_value(A, Env, X),
    fd_value(B, Env, Y),
    X =< Y.

fd_check(add(A,B,C), Env) :-
    fd_value(A, Env, X),
    fd_value(B, Env, Y),
    fd_value(C, Env, Z),
    X + Y =:= Z.

fd_check(all_different(Vars), Env) :-
    fd_values(Vars, Env, Values),
    all_distinct(Values).

fd_values([], _, []).

fd_values([X|Xs], Env, [V|Vs]) :-
    fd_value(X, Env, V),
    fd_values(Xs, Env, Vs).

all_distinct([]).

all_distinct([X|Rest]) :-
    \+ logos_member_eq(X, Rest),
    all_distinct(Rest).

fd_assign([], Env, Env).

fd_assign(
    [domain(Name, Low, High)|Rest],
    Env0,
    Env
) :-
    integer(Low),
    integer(High),
    Low =< High,
    \+ logos_member(Name-_, Env0),
    between(Low, High, Value),
    fd_assign(Rest, [Name-Value|Env0], Env).

fd_constraints([], _).

fd_constraints([Constraint|Rest], Env) :-
    fd_check(Constraint, Env),
    fd_constraints(Rest, Env).

fd_solve(Domains, Constraints, Initial, Answer) :-
    fd_assign(Domains, Initial, Answer),
    fd_constraints(Constraints, Answer).

fd_all(Domains, Constraints, Initial, Answers) :-
    findall(
        Answer,
        fd_solve(Domains, Constraints, Initial, Answer),
        Answers
    ).

% ============================================================
% EXACT FINITE PROBABILISTIC WORLDS
% ============================================================

% Random variable:
%
% random(ID, [
%   choice(Value1, Probability1),
%   choice(Value2, Probability2)
% ])
%
% World:
% [ID-Value, ...]
%
% Probabilities must be nonnegative and normalized.

valid_choices(Choices) :-
    Choices \== [],
    choice_weights(Choices, Weights),
    nonnegative_weights(Weights),
    logos_sum(Weights, Total),
    Difference is abs(Total - 1.0),
    Difference =< 0.000000001.

choice_weights([], []).

choice_weights(
    [choice(_, P)|Rest],
    [P|Weights]
) :-
    number(P),
    choice_weights(Rest, Weights).

nonnegative_weights([]).

nonnegative_weights([P|Rest]) :-
    P >= 0,
    P =< 1,
    nonnegative_weights(Rest).

valid_randoms([]).

valid_randoms([random(ID, Choices)|Rest]) :-
    valid_choices(Choices),
    \+ random_id_member(ID, Rest),
    valid_randoms(Rest).

random_id_member(ID, [random(Other, _)|_]) :-
    ID == Other,
    !.

random_id_member(ID, [_|Rest]) :-
    random_id_member(ID, Rest).

enumerate_world([], [], 1.0).

enumerate_world(
    [random(ID, Choices)|Rest],
    [ID-Value|World],
    Probability
) :-
    logos_member(choice(Value, P), Choices),
    enumerate_world(Rest, World, Remaining),
    Probability is P * Remaining.

world_probability(Randoms, World, Probability) :-
    valid_randoms(Randoms),
    enumerate_world(Randoms, World, Probability).

% A probabilistic query is an expression evaluated
% against a complete assignment.

event_true(has(ID,Value), World) :-
    logos_member(ID-Value, World).

event_true(and(A,B), World) :-
    event_true(A, World),
    event_true(B, World).

event_true(or(A,B), World) :-
    (
        event_true(A, World)
    ;
        event_true(B, World)
    ),
    !.

event_true(not(A), World) :-
    \+ event_true(A, World).

event_true(true, _).

event_true(false, _) :-
    fail.

event_true(implies(A,B), World) :-
    event_true(or(not(A),B), World).

event_true(xor(A,B), World) :-
    event_true(
        or(
            and(A,not(B)),
            and(not(A),B)
        ),
        World
    ).

event_true(equiv(A,B), World) :-
    event_true(
        and(
            implies(A,B),
            implies(B,A)
        ),
        World
    ).

probability(Randoms, Event, Evidence, Probability) :-
    valid_randoms(Randoms),
    findall(
        Weight,
        (
            enumerate_world(Randoms, World, Weight),
            event_true(Evidence, World)
        ),
        EvidenceWeights
    ),
    logos_sum(EvidenceWeights, Denominator),
    Denominator > 0,
    findall(
        Weight,
        (
            enumerate_world(Randoms, World, Weight),
            event_true(Evidence, World),
            event_true(Event, World)
        ),
        JointWeights
    ),
    logos_sum(JointWeights, Numerator),
    Probability is Numerator / Denominator.

% ============================================================
% CONFIGURABLE SEMIRINGS
% ============================================================

semiring_zero(sum_product, 0).
semiring_one(sum_product, 1).

semiring_zero(max_product, 0).
semiring_one(max_product, 1).

semiring_zero(boolean, false).
semiring_one(boolean, true).

semiring_plus(sum_product, A, B, C) :-
    C is A + B.

semiring_times(sum_product, A, B, C) :-
    C is A * B.

semiring_plus(max_product, A, B, C) :-
    C is max(A, B).

semiring_times(max_product, A, B, C) :-
    C is A * B.

semiring_plus(boolean, A, B, C) :-
    bool_or(A, B, C).

semiring_times(boolean, A, B, C) :-
    bool_and(A, B, C).

bool_or(true, _, true).
bool_or(false, X, X).

bool_and(false, _, false).
bool_and(true, X, X).

% Weighted rules:
%
% weighted(Head, [Body1,...], Weight)
%
% Each derivation evaluates to the product of
% its rule weight and the weights of its premises.
%
% Alternative derivations combine with semiring plus.
% A depth bound makes recursive programs finite.

semiring_evaluate(
    Program,
    Query,
    Semiring,
    Depth,
    Value
) :-
    integer(Depth),
    Depth >= 0,
    findall(
        Weight,
        weighted_derivation(
            Program,
            Query,
            Semiring,
            Depth,
            Weight
        ),
        Weights
    ),
    semiring_zero(Semiring, Zero),
    semiring_fold_plus(Semiring, Weights, Zero, Value).

weighted_derivation(
    Program,
    Query,
    Semiring,
    Depth,
    Weight
) :-
    Depth > 0,
    logos_member(
        weighted(Head, Body, RuleWeight),
        Program
    ),
    copy_term(
        Head-Body,
        FreshHead-FreshBody
    ),
    unify_with_occurs_check(Query, FreshHead),
    NextDepth is Depth - 1,
    weighted_body(
        Program,
        FreshBody,
        Semiring,
        NextDepth,
        BodyWeight
    ),
    semiring_times(
        Semiring,
        RuleWeight,
        BodyWeight,
        Weight
    ).

weighted_body(
    _,
    [],
    Semiring,
    _,
    Identity
) :-
    semiring_one(Semiring, Identity).

weighted_body(
    Program,
    [Goal|Rest],
    Semiring,
    Depth,
    Value
) :-
    semiring_evaluate(
        Program,
        Goal,
        Semiring,
        Depth,
        First
    ),
    weighted_body(
        Program,
        Rest,
        Semiring,
        Depth,
        Remaining
    ),
    semiring_times(
        Semiring,
        First,
        Remaining,
        Value
    ).

semiring_fold_plus(_, [], Acc, Acc).

semiring_fold_plus(
    Semiring,
    [X|Rest],
    Acc,
    Result
) :-
    semiring_plus(Semiring, Acc, X, Next),
    semiring_fold_plus(
        Semiring,
        Rest,
        Next,
        Result
    ).

% ============================================================
% CAUSAL TRANSITION SYSTEM
% ============================================================

% Causal rules:
%
% causes(Conditions, Effect)
%
% Conditions are atoms required to hold in the
% current state.
%
% Effects:
% add(Fact)
% remove(Fact)
%
% Intervention:
% do(add(Fact))
% do(remove(Fact))
%
% This is a deterministic causal transition system.
% Probabilistic branches can be enumerated externally
% using the finite-world evaluator above.

all_present([], _).

all_present([Fact|Rest], State) :-
    logos_member_eq(Fact, State),
    all_present(Rest, State).

causal_effects([], _, []).

causal_effects(
    [causes(Conditions, Effect)|Rest],
    State,
    Effects
) :-
    (
        all_present(Conditions, State)
    ->
        Effects = [Effect|Remaining]
    ;
        Effects = Remaining
    ),
    causal_effects(Rest, State, Remaining).

delete_fact(_, [], []).

delete_fact(Fact, [X|Rest], Output) :-
    Fact == X,
    !,
    delete_fact(Fact, Rest, Output).

delete_fact(Fact, [X|Rest], [X|Output]) :-
    delete_fact(Fact, Rest, Output).

apply_effects([], State, State).

apply_effects([add(Fact)|Rest], S0, S2) :-
    (
        logos_member_eq(Fact, S0)
    ->
        S1 = S0
    ;
        S1 = [Fact|S0]
    ),
    apply_effects(Rest, S1, S2).

apply_effects([remove(Fact)|Rest], S0, S2) :-
    delete_fact(Fact, S0, S1),
    apply_effects(Rest, S1, S2).

causal_step(Rules, State, Intervention, Next) :-
    causal_effects(Rules, State, Effects),
    apply_effects(Effects, State, Intermediate),
    apply_effects(Intervention, Intermediate, Next).

causal_history(
    _,
    State,
    [],
    [State],
    State
).

causal_history(
    Rules,
    State,
    [Intervention|Rest],
    [State|History],
    Final
) :-
    causal_step(
        Rules,
        State,
        Intervention,
        Next
    ),
    causal_history(
        Rules,
        Next,
        Rest,
        History,
        Final
    ).

% ============================================================
% LEXICAL AXIOMS
% ============================================================

% Axioms are represented as executable relations.
% Historical ancestry does not imply semantic identity.

lexical_axiom(State, reconstruction(ID)) :-
    valid_reconstruction(State, ID).

lexical_axiom(State, ancestry(A,B)) :-
    ancestor(State, A, B).

lexical_axiom(State, segmentation(ID)) :-
    validate_segmentation(State, ID).

lexical_axiom(State, common_origin(A,B,Root)) :-
    shared_ancestor(State, A, B, Root).

lexical_axiom(
    State,
    supported(Subject,Predicate,Object)
) :-
    lookup_evidence(
        State,
        Subject,
        Predicate,
        evidence(
            _,
            Subject,
            Predicate,
            Object,
            _,
            attested
        )
    ).

% ============================================================
% EXECUTABLE SELF TESTS
% ============================================================

logos_selftest :-
    test_substitution,
    test_resolution,
    test_finite_domains,
    test_probability,
    test_semiring,
    test_causal,
    test_lexicon.

test_substitution :-
    unify(
        node(pair,[lv(x),lv(y)]),
        node(pair,[alpha,beta]),
        [],
        S
    ),
    reify(
        node(pair,[lv(x),lv(y)]),
        S,
        node(pair,[alpha,beta])
    ),
    \+ unify(
        lv(x),
        node(loop,[lv(x)]),
        [],
        _
    ).

test_resolution :-
    Program = [
        rule(
            node(parent,[alice,bob]),
            []
        ),
        rule(
            node(parent,[bob,carol]),
            []
        ),
        rule(
            node(ancestor,[lv(x),lv(y)]),
            [
                node(parent,[lv(x),lv(y)])
            ]
        ),
        rule(
            node(ancestor,[lv(x),lv(y)]),
            [
                node(parent,[lv(x),lv(z)]),
                node(ancestor,[lv(z),lv(y)])
            ]
        )
    ],
    prove(
        Program,
        node(ancestor,[alice,carol]),
        12,
        node(ancestor,[alice,carol])
    ).

test_finite_domains :-
    fd_solve(
        [
            domain(x,1,3),
            domain(y,1,3)
        ],
        [
            neq(v(x),v(y)),
            lt(v(x),v(y))
        ],
        [],
        Solution
    ),
    logos_member(x-1, Solution),
    logos_member(y-2, Solution).

test_probability :-
    Randoms = [
        random(rain, [
            choice(yes,0.3),
            choice(no,0.7)
        ]),
        random(wind, [
            choice(yes,0.4),
            choice(no,0.6)
        ])
    ],
    probability(
        Randoms,
        and(has(rain,yes),has(wind,yes)),
        true,
        P
    ),
    abs(P - 0.12) < 0.000000001.

test_semiring :-
    Program = [
        weighted(node(edge,[a,b]),[],0.5),
        weighted(node(edge,[a,b]),[],0.2)
    ],
    semiring_evaluate(
        Program,
        node(edge,[a,b]),
        sum_product,
        4,
        Value
    ),
    abs(Value - 0.7) < 0.000000001.

test_causal :-
    Rules = [
        causes([spark,fuel],add(fire)),
        causes([fire],add(smoke))
    ],
    causal_history(
        Rules,
        [spark,fuel],
        [[],[]],
        History,
        Final
    ),
    logos_length(History, 3),
    logos_member_eq(fire, Final),
    logos_member_eq(smoke, Final).

test_lexicon :-
    empty_state(S0),

    insert_word(
        S0,
        word(
            w1,
            english,
            rebuild,
            modern,
            latin_script,
            test_source
        ),
        S1,
        w1,
        english,
        rebuild,
        test_source
    ),

    insert_word(
        S1,
        word(
            w2,
            english,
            build,
            modern,
            latin_script,
            test_source
        ),
        S2,
        w2,
        english,
        build,
        test_source
    ),

    insert_segmentation(
        S2,
        segmentation(
            seg1,
            w1,
            morphological,
            [
                part(0,2,re,prefix),
                part(2,7,build,root)
            ],
            test_source
        ),
        S3,
        seg1,
        w1,
        [
            part(0,2,re,prefix),
            part(2,7,build,root)
        ],
        test_source
    ),

    validate_segmentation(S3, seg1),
    morphological_root(S3, w1, build),

    insert_relation(
        S3,
        relation(
            rel1,
            w1,
            w2,
            derived_from,
            test_source,
            attested
        ),
        S4,
        rel1,
        w1,
        w2,
        derived_from
    ),

    ancestor(S4, w1, w2),
    ancestry_path(S4, w1, w2, [w1,w2]),
    valid_reconstruction(S4, w1),
    lexical_facts(S4, Facts),
    Facts \== [].
