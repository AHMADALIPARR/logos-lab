% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% answers.pl -- the same answers, computed by swipl
%
% Etymology: answer, Old English andswaru "a swearing back": the reply to
% a charge, here the reply to a query.
%
% Usage:
%   swipl -q answers.pl -- examples/member.pl
%
% Reads a program with the same reader as emit.pl, loads its clauses into
% swipl and prints every answer of every query in the format of ./wam -all.
% The two outputs can then be compared line by line.

:- module(answers, []).
:- create_prolog_flag(emit_as_library, true, []).
:- use_module(emit).
:- initialization(answers_main, main).

%% ── Load and run ──────────────────────────────────────────────────────────

answers_main :-
    current_prolog_flag(argv, [File|_]),
    read_source(File, Items),
    forall(member(dynamic(_, K), Items), kb:dynamic(K)),
    forall(member(clause(_, H, B), Items), assertz(kb:(H :- B))),
    forall(member(query(_, G, Names), Items), run_query(G, Names)).

run_query(G, Names0) :-
    include(named, Names0, Names),
    (   \+ \+ kb:G
    ->  forall(kb:G, show(Names))
    ;   writeln(false)
    ).

named(Name=_) :- \+ sub_atom(Name, 0, 1, _, '_').

%% ── Printing one answer ───────────────────────────────────────────────────

show(Names) :-
    \+ \+ ( items(Names, [], Items),
            bind_names(Names),
            pairs_vars(Items, Vs), term_variables(Vs, Free),
            maplist(anon, Free),
            print_items(Items, Strs),
            (   Strs == [] -> writeln(true)
            ;   atomic_list_concat(Strs, ', ', Line), writeln(Line)
            ) ).

items([], _, []).
items([N=V|T], Seen, Items) :-
    (   var(V)
    ->  (   member(M-W, Seen), W == V
        ->  Items = [alias(N, M)|Is], Seen1 = Seen
        ;   Items = Is, Seen1 = [N-V|Seen]
        )
    ;   Items = [bind(N, V)|Is], Seen1 = Seen
    ),
    items(T, Seen1, Is).

% the first name given to an unbound variable is what it is printed as
bind_names([]).
bind_names([N=V|T]) :- ( var(V) -> V = '$VAR'(N) ; true ), bind_names(T).

pairs_vars([], []).
pairs_vars([bind(_, V)|T], [V|Vs]) :- !, pairs_vars(T, Vs).
pairs_vars([_|T], Vs) :- pairs_vars(T, Vs).

print_items([], []).
print_items([I|Is], [S|Ss]) :-
    (   I = alias(N, M) -> format(atom(S), "~w = ~w", [N, M])
    ;   I = bind(N, V),
        format(atom(S), "~w = ~W", [N, V, [quoted(true), ignore_ops(true), brace_terms(false), numbervars(true)]])
    ),
    print_items(Is, Ss).

anon('$VAR'('_')).
