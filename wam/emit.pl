% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% emit.pl -- compile ISO Prolog source to WAM tokens
%
% Etymology: emit, Latin emittere "to send out" (e- "out" + mittere "to send"):
% the compiler sends out the tokens the engine reads.
%
% Usage:
%   swipl -q emit.pl -- examples/append.pl > append.tok
%   swipl -q emit.pl -- examples/append.pl | ./wam -all -
%   swipl -q emit.pl -- - < examples/append.pl | ./wam -all -
%
% The input is plain ISO Prolog: facts, rules, conjunction, disjunction,
% if-then-else, negation as failure and cut. Every "?- Goal." and every
% ":- Goal." becomes a query section. swipl only reads the text (read_term),
% in a module that carries the ISO operator table and nothing else.
% Everything after reading is done here.

:- module(emit, [read_source/2]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- if(\+ current_prolog_flag(emit_as_library, true)).
:- initialization(emit_main, main).
:- endif.

:- dynamic seen/1, heapres/1, xloc/2, yloc/2, xnext/1, out/1, forced/1,
           vtot/2, vchunk/2, aux_def/2, called/3, emit_failed/0, aux_count/1, unknown_seen/1,
           maxa/1.

%% ── Reading ISO source ────────────────────────────────────────────────────

iso_op(1200, xfx, ':-').
iso_op(1200, xfx, '-->').
iso_op(1200, fx,  ':-').
iso_op(1200, fx,  '?-').
iso_op(1100, xfy, ';').
iso_op(1100, xfy, '|').
iso_op(1050, xfy, '->').
iso_op(1000, xfy, ',').
iso_op(900,  fy,  '\\+').
iso_op(1150, fx,  dynamic).
iso_op(1150, fx,  discontiguous).
iso_op(1150, fx,  initialization).
iso_op(1150, fx,  multifile).
iso_op(700,  xfx, O) :- member(O, [=, '\\=', ==, '\\==', @<, @>, @=<, @>=, '=..',
                                   is, =:=, '=\\=', <, >, =<, >=]).
iso_op(500,  yfx, O) :- member(O, [+, -, '/\\', '\\/', xor]).
iso_op(400,  yfx, O) :- member(O, [*, /, //, rem, mod, div, <<, >>]).
iso_op(200,  xfx, **).
iso_op(200,  xfy, ^).
iso_op(200,  fy,  O) :- member(O, [-, +, '\\']).

% a private module whose operator table is exactly the ISO one
setup_ops :-
    (   nb_current(emit_ops, true) -> true
    ;   nb_setval(emit_ops, true),
        findall(P-T-N, ( wam_read:current_op(P, T, N),
                         \+ memberchk(N, [',', '|', '[]', '{}']) ), Old),
        forall(( member(P-T-N, Old), \+ iso_op(P, T, N) ),
               op(0, T, wam_read:N)),
        forall(( iso_op(P, T, N), N \== (',') ), op(P, T, wam_read:N))
    ).

open_source(-, S, false) :- !,
    read_string(user_input, _, Text),
    open_string(Text, S).
open_source(File, S, true) :-
    catch(open(File, read, S, [encoding(utf8)]), _, fail), !.
open_source(File, _, _) :-
    format(user_error, "emit: cannot open ~w~n", [File]),
    halt(2).

% read_source(+File, -Items)
% Items are clause(Line,Head,Body), query(Line,Goal,Names), dynamic(Line,Key).
read_source(File, Items) :-
    setup_ops,
    nb_setval(emit_dq, codes),
    open_source(File, S, Close),
    prompt(_, ''),
    read_items(S, File, Items),
    ( Close == true -> close(S) ; true ).

read_items(S, File, Items) :-
    nb_getval(emit_dq, DQ),
    catch(read_term(S, T, [module(wam_read), double_quotes(DQ),
                           variable_names(Names), term_position(Pos)]), E, true),
    (   nonvar(E)
    ->  read_error(E, File),
        read_items(S, File, Items)
    ;   T == end_of_file
    ->  Items = []
    ;   stream_position_data(line_count, Pos, Line),
        handle_term(T, Names, Line, File, New),
        read_items(S, File, Rest),
        append(New, Rest, Items)
    ).

read_error(error(syntax_error(Msg), Ctx), File) :-
    (   Ctx = stream(_, Line, Col, _) ; Ctx = file(_, Line, Col, _) ), !,
    Col1 is Col + 1,
    format(user_error, "~w:~w:~w: syntax error: ~w~n", [File, Line, Col1, Msg]),
    assertz(emit_failed).
read_error(error(syntax_error(Msg), _), File) :- !,
    format(user_error, "~w: syntax error: ~w~n", [File, Msg]),
    assertz(emit_failed).
read_error(E, _) :- throw(E).

emit_error(Line, Fmt, Args) :-
    nb_getval(emit_file, File),
    format(user_error, "~w:~w: ", [File, Line]),
    format(user_error, Fmt, Args), nl(user_error),
    ( emit_failed -> true ; assertz(emit_failed) ).

handle_term((:- D), Names, Line, _, Items) :- !, directive(D, Names, Line, Items).
handle_term((?- G), Names, Line, _, [query(Line, G, Names)]) :- !.
handle_term((_ --> _), _, Line, _, []) :- !,
    emit_error(Line, "grammar rules (-->) are not supported", []).
handle_term((H :- B), _, Line, _, Items) :- !, clause_item(Line, H, B, Items).
handle_term(H, _, Line, _, Items) :- clause_item(Line, H, true, Items).

clause_item(Line, H, _, []) :- var(H), !,
    emit_error(Line, "clause head is a variable", []).
clause_item(Line, H, _, []) :- \+ callable(H), !,
    emit_error(Line, "clause head ~q is not callable", [H]).
clause_item(Line, H, _, []) :-
    functor(H, N, A), memberchk(N/A, [(',')/2, (;)/2, (->)/2, (!)/0, ('|')/2, (\+)/1]), !,
    emit_error(Line, "cannot define the control construct ~q/~w", [N, A]).
clause_item(Line, H, B, [clause(Line, H, B1)]) :- norm_body(B, B1).

% | as a disjunction is read as ';'
norm_body(B, B) :- var(B), !.
norm_body((A,B), (A1,B1)) :- !, norm_body(A, A1), norm_body(B, B1).
norm_body((A;B), (A1;B1)) :- !, norm_body(A, A1), norm_body(B, B1).
norm_body('|'(A,B), (A1;B1)) :- !, norm_body(A, A1), norm_body(B, B1).
norm_body((A->B), (A1->B1)) :- !, norm_body(A, A1), norm_body(B, B1).
norm_body(\+ A, \+ A1) :- !, norm_body(A, A1).
norm_body(B, B).

directive(op(P, T, N), _, Line, []) :- !,
    (   catch(( is_list(N) -> forall(member(X, N), op(P, T, wam_read:X))
                ;  op(P, T, wam_read:N) ), _, fail)
    ->  true
    ;   emit_error(Line, "bad op/3 directive", [])
    ).
directive(set_prolog_flag(double_quotes, F), _, Line, []) :- !,
    (   memberchk(F, [codes, chars, atom]) -> nb_setval(emit_dq, F)
    ;   emit_error(Line, "double_quotes flag must be codes, chars or atom", [])
    ).
directive(set_prolog_flag(_, _), _, _, []) :- !.
directive(dynamic(Spec), _, Line, Items) :- !, spec_keys(Spec, Line, Ks),
    findall(dynamic(Line, K), member(K, Ks), Items).
directive(discontiguous(_), _, _, []) :- !.
directive(multifile(_), _, _, []) :- !.
directive(ensure_loaded(_), _, _, []) :- !.
directive(initialization(G), Names, Line, [query(Line, G, Names)]) :- !.
directive(G, Names, Line, [query(Line, G, Names)]).

spec_keys(V, Line, []) :- var(V), !, emit_error(Line, "dynamic: unbound specification", []).
spec_keys((A,B), Line, Ks) :- !, spec_keys(A, Line, K1), spec_keys(B, Line, K2), append(K1, K2, Ks).
spec_keys([], _, []) :- !.
spec_keys([H|T], Line, Ks) :- !, spec_keys(H, Line, K1), spec_keys(T, Line, K2), append(K1, K2, Ks).
spec_keys(N/A, _, [N/A]) :- atom(N), integer(A), !.
spec_keys(S, Line, []) :- emit_error(Line, "dynamic: expected Name/Arity, found ~q", [S]).

%% ── Control constructs become auxiliary predicates ────────────────────────
%
% A body is a list of items:
%   goal(G)       call G
%   cut_local     a cut that cuts to the clause entry
%   cutv(V)       cut to the barrier held in variable V
%   getlevel(V)   store the barrier in V (first item)
%   fail
%
% (A;B), (C->T;E), \+ G and call(G) turn into a call to a fresh predicate
% whose arguments are the variables the construct shares with the rest of
% the clause. A cut inside the construct must cut the whole clause: the
% barrier travels as one more argument (cutv). A cut in a condition or under
% \+ is local, so that condition gets a predicate of its own.

cut_in(G) :- var(G), !, fail.
cut_in(!).
cut_in((A,B)) :- ( cut_in(A) -> true ; cut_in(B) ).
cut_in((A;B)) :- !,
    (   nonvar(A), A = (_->T) -> ( cut_in(T) -> true ; cut_in(B) )
    ;   ( cut_in(A) -> true ; cut_in(B) )
    ).
cut_in((_->T)) :- cut_in(T).

is_ctl(G) :- nonvar(G), ( G = (_;_) ; G = (_->_) ; G = (\+ _) ; G = call(_) ; G = (_*->_) ), !.

conj_list(V, [V]) :- var(V), !.
conj_list((A,B), L) :- !, conj_list(A, LA), conj_list(B, LB), append(LA, LB, L).
conj_list(true, []) :- !.
conj_list(G, [G]).

new_aux(Tag, Name) :-
    retract(aux_count(N)), N1 is N + 1, assertz(aux_count(N1)),
    format(atom(Name), "$~w~w", [Tag, N1]).

expand_body(Body, Ctx0, Head, Line, Items) :-
    conj_list(Body, Gs),
    (   Ctx0 == local, member(G, Gs), is_ctl(G), cut_in(G)
    ->  Ctx = cb(CB), Items = [getlevel(CB)|Rest]
    ;   Ctx = Ctx0, Items = Rest
    ),
    expand_goals(Gs, [], Ctx, Head, Line, Rest).

expand_goals([], _, _, _, _, []).
expand_goals([G|After], Before, Ctx, Head, Line, Items) :-
    append(Before, After, Others),
    expand_goal(G, Ctx, Head, Others, Line, Its),
    append(Before, [G], Before1),
    expand_goals(After, Before1, Ctx, Head, Line, Rest),
    append(Its, Rest, Items).

expand_goal(G, _, _, _, Line, []) :- var(G), !,
    emit_error(Line, "a variable used as a goal is not supported (call/1 on a variable)", []).
expand_goal(!, local, _, _, _, [cut_local]) :- !.
expand_goal(!, cb(CB), _, _, _, [cutv(CB)]) :- !.
expand_goal('$lcut', _, _, _, _, [cut_local]) :- !.
expand_goal(true, _, _, _, _, []) :- !.
expand_goal(fail, _, _, _, _, [fail]) :- !.
expand_goal(false, _, _, _, _, [fail]) :- !.
expand_goal(G, _, _, _, Line, []) :- G = (_*->_), !,
    emit_error(Line, "soft-cut (*->) is not ISO and is not supported", []).
expand_goal(G, _, _, _, Line, []) :- \+ callable(G), !,
    emit_error(Line, "goal ~q is not callable", [G]).
expand_goal(G, Ctx, Head, Others, Line, [goal(Call)]) :-
    is_ctl(G), !,
    term_variables([Head|Others], RestVs),
    term_variables(G, GVs),
    include(var_in(RestVs), GVs, PV0),
    (   cut_in(G) -> Ctx = cb(CB), append(PV0, [CB], PV), ACtx = Ctx
    ;   PV = PV0, ACtx = local
    ),
    ctl_aux(G, PV, ACtx, Line, Call).
expand_goal(G, _, _, _, _, [goal(G)]).

var_in(Vs, V) :- member(W, Vs), W == V, !.

ctl_aux(G, PV, ACtx, Line, Call) :-
    G = (A;B), !,
    (   nonvar(A), A = (C->T)
    ->  new_aux(ite, Name), Call =.. [Name|PV],
        isolate(C, [Call, T, B], Line, C1),
        add_aux(Call, [(C1, '$lcut', T), B], ACtx, Line)
    ;   new_aux(or, Name), Call =.. [Name|PV],
        add_aux(Call, [A, B], ACtx, Line)
    ).
ctl_aux((C->T), PV, ACtx, Line, Call) :- !,
    new_aux(ite, Name), Call =.. [Name|PV],
    isolate(C, [Call, T], Line, C1),
    add_aux(Call, [(C1, '$lcut', T), fail], ACtx, Line).
ctl_aux(\+ G, PV, ACtx, Line, Call) :- !,
    new_aux(not, Name), Call =.. [Name|PV],
    isolate(G, [Call], Line, G1),
    add_aux(Call, [(G1, '$lcut', fail), true], ACtx, Line).
ctl_aux(call(G), PV, _, Line, Call) :-
    new_aux(call, Name), Call =.. [Name|PV],
    add_aux(Call, [G], local, Line).

% a goal with a cut of its own gets a predicate of its own
isolate(C, RestTerms, Line, C1) :-
    (   cut_in(C)
    ->  term_variables(RestTerms, RVs), term_variables(C, CVs),
        include(var_in(RVs), CVs, PV),
        new_aux(cond, Name), C1 =.. [Name|PV],
        add_aux(C1, [C], local, Line)
    ;   C1 = C
    ).

add_aux(Head, Bodies, Ctx, Line) :-
    findall(cl(Line, Head, Items),
            ( member(B, Bodies), expand_body(B, Ctx, Head, Line, Items) ), Cls),
    functor(Head, N, A),
    assertz(aux_def(N/A, Cls)).

%% ── Compiling one clause ──────────────────────────────────────────────────

% compile_unit(+Mode, +Line, +Head, +Items, +Names, -Instrs); Mode pred or query
compile_unit(Mode, Line, Head, Items0, Names, Instrs) :-
    copy_term(t(Head, Items0, Names), t(H, I1, N1)),
    numbervars(t(H, I1, N1), 0, _, [functor_name('$wv')]),
    retractall(seen(_)), retractall(heapres(_)), retractall(xloc(_, _)),
    retractall(yloc(_, _)), retractall(out(_)), retractall(forced(_)),
    retractall(vtot(_, _)), retractall(vchunk(_, _)),
    normalize_cuts(Mode, I1, Items, Neck),
    force_vars(Mode, Items, N1),
    analyse(H, Items),
    assign_y(H, Items, NY),
    calls_of(Items, Goals, Tail),
    length(Goals, NCalls),
    H =.. [_|HArgs], length(HArgs, HA),
    findall(A, ( member(goal(G), Items), functor(G, _, A) ), As),
    max_list([HA|As], MaxA),
    retractall(maxa(_)), assertz(maxa(MaxA)),
    (   Mode == query -> Env = true
    ;   ( NY > 0 ; NCalls >= 2 ; NCalls =:= 1, Tail \== [] ) -> Env = true
    ;   Env = false
    ),
    reset_x,
    (   Mode == query -> forall(member(Nm=V, N1), emit_name(Nm, V)) ; true ),
    ( Env == true -> emit(allocate(NY)) ; true ),
    ( Items = [getlevel(LV)|_] -> loc(LV, R), emit(get_level(R)), mark(LV) ; true ),
    forall(nth1(I, HArgs, A), head_arg(I, A)),
    ( Neck == true -> emit(neck_cut) ; true ),
    (   append(_, [goal(_)], Items), Mode == pred -> Exec = true ; Exec = false ),
    body(Items, Env, Exec, Mode, Line),
    (   Exec == true -> true
    ;   Mode == query -> emit(halt)
    ;   ( Env == true -> emit(deallocate) ; true ), emit(proceed)
    ),
    findall(X, out(X), Instrs).

emit(I) :- emit_check(I), assertz(out(I)).

normalize_cuts(Mode, Items0, Items, Neck) :-
    include(==(cut_local), Items0, Cs), length(Cs, N),
    (   N =:= 0 -> Items = Items0, Neck = false
    ;   N =:= 1, Mode == pred, Items0 = [cut_local|Rest] -> Items = Rest, Neck = true
    ;   LV = '$wv'(l),
        maplist(cut_to(LV), Items0, Items1),
        ( Items1 = [getlevel(_)|_] -> Items = Items1 ; Items = [getlevel(LV)|Items1] ),
        Neck = false
    ).
cut_to(LV, cut_local, cutv(LV)) :- !.
cut_to(_, I, I).

force_vars(Mode, Items, Names) :-
    forall(( member(It, Items), ( It = getlevel(V) ; It = cutv(V) ) ), assertz(forced(V))),
    (   Mode == query -> forall(member(_=V, Names), assertz(forced(V))) ; true ).

calls_of(Items, Goals, Tail) :-
    include([I]>>(I = goal(_)), Items, Goals),
    (   append(Pre, [goal(_)|T], Items), \+ memberchk(goal(_), T)
    ->  Tail = T, Pre = Pre
    ;   Tail = []
    ).

% occurrence counts and the chunk each occurrence belongs to
analyse(H, Items) :-
    occurrences(H, HOs), forall(member(V, HOs), note(V, 1)),
    walk(Items, 1).

walk([], _).
walk([It|R], C) :-
    (   It = goal(G) -> occurrences(G, Os), forall(member(V, Os), note(V, C)), C1 is C + 1
    ;   ( It = cutv(V) ; It = getlevel(V) ) -> note(V, C), C1 = C
    ;   C1 = C
    ),
    walk(R, C1).

note(V, C) :-
    ( retract(vtot(V, N)) -> N1 is N + 1 ; N1 = 1 ), assertz(vtot(V, N1)),
    ( vchunk(V, C) -> true ; assertz(vchunk(V, C)) ).

occurrences(T, []) :- var(T), !.
occurrences('$wv'(N), ['$wv'(N)]) :- !.
occurrences(T, Os) :- compound(T), !, T =.. [_|As], maplist(occurrences, As, Ls), append(Ls, Os).
occurrences(_, []).

var_order(H, Items, Vs) :-
    findall(V, ( member(T, [H|Items]), item_term(T, X), occurrences(X, Os), member(V, Os) ), L0),
    list_to_set(L0, Vs).
item_term(T, T) :- \+ T = goal(_), \+ T = cutv(_), \+ T = getlevel(_), !.
item_term(goal(G), G) :- !.
item_term(cutv(V), V) :- !.
item_term(getlevel(V), V).

assign_y(H, Items, N) :-
    var_order(H, Items, Vs),
    include(permanent, Vs, Ps),
    length(Ps, N),
    forall(nth1(K, Ps, V), assertz(yloc(V, K))).

permanent(V) :- forced(V), !.
permanent(V) :- findall(C, vchunk(V, C), Cs), Cs = [_,_|_].

singleton(V) :- vtot(V, 1), \+ forced(V).

reset_x :- retractall(xnext(_)), maxa(M), N is M + 1, assertz(xnext(N)).
new_x(x(N)) :- retract(xnext(N)), N1 is N + 1, assertz(xnext(N1)),
    ( N > 1000 -> throw(emit_err("clause needs more than 1000 registers")) ; true ).

loc(V, y(K)) :- yloc(V, K), !.
loc(V, R) :- xloc(V, R), !.
loc(V, R) :- new_x(R), assertz(xloc(V, R)).

emit_name(Nm, V) :- ( vtot(V, _) -> yloc(V, K), emit(name(Nm, y(K))) ; true ).

first(V) :- \+ seen(V).
mark(V) :- ( seen(V) -> true ; assertz(seen(V)) ).
mark_heap(V) :- ( heapres(V) -> true ; assertz(heapres(V)) ).

%% ── Head: get and unify instructions ──────────────────────────────────────

head_arg(I, T) :- T = '$wv'(_), !,
    (   singleton(T) -> true
    ;   first(T) -> loc(T, R), emit(get_variable(R, x(I))), mark(T)
    ;   loc(T, R), emit(get_value(R, x(I)))
    ).
head_arg(I, T) :- atomic(T), !, emit(get_constant(c(T), x(I))).
head_arg(I, T) :- get_term(T, x(I)).

get_term(T, Reg) :-
    (   T = [_|_] -> emit(get_list(Reg)), T = [H|Tl], Args = [H, Tl]
    ;   functor(T, N, A), emit(get_structure(N/A, Reg)), T =.. [_|Args]
    ),
    unify_args(Args, Queue),
    forall(member(X-S, Queue), get_term(S, X)).

unify_args(Args, Queue) :- unify_args(Args, 0, [], Queue).
unify_args([], Voids, Q, Queue) :- flush_voids(Voids), reverse(Q, Queue).
unify_args([A|As], Voids, Q, Queue) :-
    (   A = '$wv'(_), singleton(A) -> V1 is Voids + 1, unify_args(As, V1, Q, Queue)
    ;   flush_voids(Voids),
        (   A = '$wv'(_)
        ->  (   first(A) -> loc(A, R), emit(unify_variable(R)), mark(A), mark_heap(A)
            ;   loc(A, R),
                ( heapres(A) -> emit(unify_value(R)) ; emit(unify_local_value(R)) )
            ),
            Q1 = Q
        ;   atomic(A) -> emit(unify_constant(c(A))), Q1 = Q
        ;   new_x(X), emit(unify_variable(X)), Q1 = [X-A|Q]
        ),
        unify_args(As, 0, Q1, Queue)
    ).
flush_voids(0) :- !.
flush_voids(N) :- emit(unify_void(N)).

%% ── Body: put and set instructions, calls ─────────────────────────────────

body([], _, _, _, _).
body([It|R], Env, Exec, Mode, Line) :-
    body_item(It, R, Env, Exec, Mode, Line),
    body(R, Env, Exec, Mode, Line).

body_item(getlevel(_), _, _, _, _, _) :- !.
body_item(cutv(V), _, _, _, _, _) :- !, loc(V, R), emit(cut(R)).
body_item(fail, _, _, _, _, _) :- !, emit(fail).
body_item(goal(G), Rest, Env, Exec, Mode, Line) :-
    functor(G, N, A), G =.. [_|Args],
    assertz(called(N/A, Line, Mode)),
    (   Exec == true, Rest == [] -> Last = true ; Last = false ),
    forall(nth1(I, Args, Arg), put_arg(I, Arg, Last, Env)),
    (   Last == true
    ->  ( Env == true -> emit(deallocate) ; true ), emit(execute(N/A))
    ;   emit(call(N/A))
    ),
    reset_x.

put_arg(I, T, Last, Env) :- T = '$wv'(_), !,
    (   singleton(T) -> emit(put_variable(x(I), x(I)))
    ;   first(T)
    ->  loc(T, R), emit(put_variable(R, x(I))), mark(T),
        ( R = x(_) -> mark_heap(T) ; true )
    ;   loc(T, R),
        (   R = y(_), Last == true, Env == true, \+ heapres(T)
        ->  emit(put_unsafe_value(R, x(I)))
        ;   emit(put_value(R, x(I)))
        )
    ).
put_arg(I, T, _, _) :- atomic(T), !, emit(put_constant(c(T), x(I))).
put_arg(I, T, _, _) :- build_term(T, x(I)).

% children first, then the structure itself
build_term(T, Dest) :-
    (   T = [H|Tl] -> Args = [H, Tl], Open = put_list(Dest)
    ;   functor(T, N, A), T =.. [_|Args], Open = put_structure(N/A, Dest)
    ),
    maplist(build_child, Args, Regs),
    emit(Open),
    set_args(Args, Regs, 0).

build_child(A, R) :-
    (   compound(A), A \= '$wv'(_) -> new_x(R), build_term(A, R) ; R = none ).

set_args([], [], V) :- flush_set(V).
set_args([A|As], [R|Rs], V) :-
    (   A = '$wv'(_), singleton(A) -> V1 is V + 1, set_args(As, Rs, V1)
    ;   flush_set(V),
        (   A = '$wv'(_)
        ->  (   first(A) -> loc(A, L), emit(set_variable(L)), mark(A), mark_heap(A)
            ;   loc(A, L),
                ( heapres(A) -> emit(set_value(L)) ; emit(set_local_value(L)) )
            )
        ;   atomic(A) -> emit(set_constant(c(A)))
        ;   emit(set_value(R))
        ),
        set_args(As, Rs, 0)
    ).
flush_set(0) :- !.
flush_set(N) :- emit(set_void(N)).

%% ── Printing tokens ───────────────────────────────────────────────────────

atom_text(A, T) :- plain_atom(A), !, T = A.
atom_text(A, T) :-
    atom_codes(A, Cs), quote_codes(Cs, Qs),
    append([[0'\'], Qs, [0'\']], All), atom_codes(T, All).

plain_atom([]) :- !.
plain_atom(A) :- atom(A), atom_codes(A, [C|Cs]), C >= 0'a, C =< 0'z, maplist(word_code, Cs).
word_code(C) :- ( C >= 0'a, C =< 0'z ; C >= 0'A, C =< 0'Z ; C >= 0'0, C =< 0'9 ; C == 0'_ ), !.

quote_codes([], []).
quote_codes([C|Cs], Out) :-
    quote_code(C, Q), quote_codes(Cs, Rest), append(Q, Rest, Out).
quote_code(0'\\, [0'\\, 0'\\]) :- !.
quote_code(0'\', [0'\', 0'\']) :- !.
quote_code(10, [0'\\, 0'n]) :- !.
quote_code(9, [0'\\, 0't]) :- !.
quote_code(C, Q) :- ( C < 32 ; C =:= 127 ), !,
    format(codes(Q), "\\x~16r\\", [C]).
quote_code(C, [C]).

key_text(N/A, T) :- atom_text(N, QN), format(atom(T), "~w/~w", [QN, A]).
label_text(Key, Suffix, T) :- key_text(Key, KT), format(atom(T), "~w#~w", [KT, Suffix]).

const_text(C, T) :- integer(C), !, format(atom(T), "~d", [C]).
const_text(C, T) :- float(C), !, format(atom(T), "~w", [C]).
const_text(C, T) :- atom_text(C, T).

fmt(I) :- I =.. [Op|Args], format("  ~w", [Op]), maplist(fmt_arg, Args), nl.
fmt_arg(x(N)) :- !, format(" X~w", [N]).
fmt_arg(y(N)) :- !, format(" Y~w", [N]).
fmt_arg(c(C)) :- !, const_text(C, T), format(" ~w", [T]).
fmt_arg(raw(T)) :- !, format(" ~w", [T]).
fmt_arg(N/A) :- !, key_text(N/A, T), format(" ~w", [T]).
fmt_arg(A) :- format(" ~w", [A]).

emit_check(I) :-
    (   atom(I) -> true
    ;   arg(_, I, c(C)), integer(C), ( C > 9223372036854775807 ; C < -9223372036854775808 )
    ->  throw(emit_err(format("integer ~w does not fit in 64 bits", [C])))
    ;   arg(_, I, c(C)), float(C), ( C =\= C ; C > 1.0e308 ; C < -1.0e308 )
    ->  throw(emit_err(format("float ~w is not finite", [C])))
    ;   true
    ).

%% ── Predicates ────────────────────────────────────────────────────────────

compile_cl(cl(Line, H, Items), Code) :-
    catch(compile_unit(pred, Line, H, Items, [], Code), emit_err(Msg),
          ( report(Line, Msg), Code = [] )).

report(Line, format(F, A)) :- !, emit_error(Line, F, A).
report(Line, Msg) :- emit_error(Line, "~w", [Msg]).

print_code(Code) :- forall(member(I, Code), fmt(I)).
print_label(T) :- format("~w:~n", [T]).

emit_pred(Key, Cls) :-
    key_text(Key, KT),
    format("~n%% ~w~n", [KT]),
    maplist(compile_cl, Cls, Codes),
    length(Cls, Len),
    (   Len =:= 1 -> Codes = [C1], print_label(KT), print_code(C1)
    ;   indexable(Cls) -> emit_switch(Key, Cls, Codes)
    ;   emit_chain(Key, Codes)
    ).

emit_chain(Key, Codes) :-
    key_text(Key, KT), length(Codes, Len),
    forall(nth1(I, Codes, Code),
           (   ( I =:= 1 -> print_label(KT) ; label_text(Key, I, L), print_label(L) ),
               (   I =:= 1 -> J is I + 1, label_text(Key, J, N), fmt(try_me_else(raw(N)))
               ;   I =:= Len -> fmt(trust_me)
               ;   J is I + 1, label_text(Key, J, N), fmt(retry_me_else(raw(N)))
               ),
               print_code(Code)
           )).

% first-argument classes: v variable, c constant, l list, s structure
arg_class(cl(_, H, _), Cl) :-
    (   H =.. [_, A|_]
    ->  (   var(A) -> Cl = v ; atomic(A) -> Cl = c ; A = [_|_] -> Cl = l ; Cl = s )
    ;   Cl = v
    ).
indexable(Cls) :- maplist(arg_class, Cls, Classes), \+ maplist(==(v), Classes).

emit_switch(Key, Cls, Codes) :-
    key_text(Key, KT),
    maplist(arg_class, Cls, Classes),
    length(Cls, Len), numlist(1, Len, All),
    sub_idx(Classes, [v, c], Sc), sub_idx(Classes, [v, l], Sl), sub_idx(Classes, [v, s], Ss),
    targets([All-v, Sc-c, Sl-l, Ss-s], Key, [], Labels, Seen),
    reverse(Seen, Chains),
    Labels = [Lv, Lc, Ll, Ls],
    print_label(KT),
    fmt(switch_on_term(raw(Lv), raw(Lc), raw(Ll), raw(Ls))),
    forall(member(Idxs-Label, Chains), emit_try_chain(Key, Label, Idxs)),
    forall(nth1(I, Codes, Code),
           ( label_text(Key, I, L), print_label(L), print_code(Code) )).

sub_idx(Classes, Keep, Idx) :-
    findall(I, ( nth1(I, Classes, C), memberchk(C, Keep) ), Idx).

% each distinct subset of clauses gets one label
targets([], _, Seen, [], Seen).
targets([Idxs-Cl|T], Key, Seen, [L|Ls], Out) :-
    (   Idxs == [] -> L = fail, Seen1 = Seen
    ;   Idxs = [I] -> label_text(Key, I, L), Seen1 = Seen
    ;   memberchk(Idxs-L0, Seen) -> L = L0, Seen1 = Seen
    ;   label_text(Key, Cl, L), Seen1 = [Idxs-L|Seen]
    ),
    targets(T, Key, Seen1, Ls, Out).

emit_try_chain(Key, Label, Idxs) :-
    print_label(Label),
    append(Front, [Last], Idxs), Front = [First|Mid],
    label_text(Key, First, LF), fmt(try(raw(LF))),
    forall(member(I, Mid), ( label_text(Key, I, L), fmt(retry(raw(L))) )),
    label_text(Key, Last, LL), fmt(trust(raw(LL))).

%% ── Queries ───────────────────────────────────────────────────────────────

emit_query(query(Line, G, Names0)) :-
    include(named_var, Names0, Names),
    maplist(name_var, Names, Vs),
    retractall(aux_def(_, _)),
    Pseudo =.. ['$q'|Vs],
    expand_body(G, local, Pseudo, Line, Items),
    findall(K-C, aux_def(K, C), Auxs),
    forall(member(K-C, Auxs), emit_pred(K, C)),
    format("~n% ?- "),
    write_term(G, [quoted(true), variable_names(Names0), spacing(next_argument)]),
    format(".~n"),
    catch(compile_unit(query, Line, '$q', Items, Names, Code), emit_err(Msg),
          ( report(Line, Msg), Code = [] )),
    format("query~n"),
    print_code(Code).

named_var(Name=_) :- \+ sub_atom(Name, 0, 1, _, '_').
name_var(_=V, V).

%% ── The whole program ─────────────────────────────────────────────────────

builtin_key(K) :- memberchk(K, [(=)/2, (\=)/2, (==)/2, (\==)/2, var/1, nonvar/1,
                                atom/1, atomic/1, integer/1]).

group_clauses(Items, Groups) :-
    findall(K, ( member(clause(_, H, _), Items), functor(H, N, A), K = N/A ), Ks0),
    list_to_set(Ks0, Ks),
    findall(K-Cs, ( member(K, Ks), K = N/A,
                    findall(clause(L, H, B), ( member(clause(L, H, B), Items), functor(H, N, A) ), Cs) ),
            Groups).

program(Items) :-
    group_clauses(Items, Groups),
    forall(( member(clause(L, H, _), Items), functor(H, N, A), builtin_key(N/A) ),
           emit_error(L, "cannot redefine the built-in ~q/~w", [N, A])),
    findall(K, member(K-_, Groups), Defined0),
    findall(K, member(dynamic(_, K), Items), Dyn),
    append(Defined0, Dyn, Defined1),
    with_output_to(string(Text), emit_all(Items, Groups, Dyn, Defined1)),
    (   emit_failed -> halt(1)
    ;   format("~s", [Text])
    ).

emit_all(Items, Groups, Dyn, Defined) :-
    format("% emitted by emit.pl~n"),
    forall(member(K-Cs, Groups), emit_group(K, Cs)),
    forall(( member(K, Dyn), \+ memberchk(K-_, Groups) ),
           ( key_text(K, KT), format("~n%% ~w~n", [KT]), print_label(KT), fmt(fail) )),
    forall(member(Q, Items), ( Q = query(_, _, _) -> emit_query(Q) ; true )),
    forall(( called(K, Line, _), \+ known(K, Defined) ),
           emit_unknown(K, Line)).

known(K, Defined) :- ( memberchk(K, Defined) ; builtin_key(K) ; aux_key(K) ), !.
aux_key(N/_) :- sub_atom(N, 0, 1, _, '$').

emit_unknown(K, Line) :-
    (   unknown_seen(K) -> true
    ;   assertz(unknown_seen(K)),
        K = N/A, emit_error(Line, "unknown procedure ~q/~w", [N, A])
    ).

emit_group(Key, Cs) :-
    retractall(aux_def(_, _)),
    findall(cl(Line, H, Items),
            ( member(clause(Line, H, B), Cs), expand_body(B, local, H, Line, Items) ),
            Cls),
    findall(K-C, aux_def(K, C), Auxs),
    emit_pred(Key, Cls),
    forall(member(K-C, Auxs), emit_pred(K, C)).

%% ── Entry point ───────────────────────────────────────────────────────────

emit_main :-
    (   catch(emit_run, E, ( print_message(error, E), halt(2) ))
    ->  true
    ;   format(user_error, "emit: internal failure~n", []), halt(2)
    ).

emit_run :-
    current_prolog_flag(argv, Argv),
    (   Argv = [File|_] -> true ; File = (-) ),
    nb_setval(emit_file, File),
    set_stream(user_output, encoding(utf8)),
    assertz(aux_count(0)),
    read_source(File, Items),
    program(Items).
