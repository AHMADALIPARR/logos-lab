% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% control.pl -- cut, if-then-else, negation, disjunction and the built-ins
%
% Etymology: control, from Medieval Latin contrarotulus "a duplicate roll
% kept to check the original" (contra "against" + rotulus "roll").
%
% Usage:
%   swipl -q ../emit.pl -- control.pl | ../wam -all -

%% ── Cut ───────────────────────────────────────────────────────────────────

vowel(a).
vowel(e).
vowel(i).

classify(X, vowel) :- vowel(X), !.
classify(_, consonant).

first([H|_], H) :- !.
first([], none).

%% ── If-then-else and negation ─────────────────────────────────────────────

kind(X, Kind) :-
    (   var(X)  -> Kind = unbound
    ;   atom(X) -> Kind = atom
    ;   Kind = other
    ).

different(X, Y) :- \+ X = Y.

colour(red).
colour(green).
colour(blue).

not_red(C) :- colour(C), C \== red.

%% ── Disjunction and a cut inside it ───────────────────────────────────────

either(X) :- ( X = left ; X = right ).

pick(X, Y) :- ( colour(X), X \= red, ! ; X = none ), Y = X.

%% ── Queries ───────────────────────────────────────────────────────────────

?- classify(e, K).
?- classify(z, K).
?- first([a,b,c], X).
?- first([], X).
?- kind(foo, K).
?- kind(_, K).
?- kind(f(x), K).
?- different(a, b).
?- different(a, a).
?- not_red(C).
?- either(X).
?- pick(X, Y).
?- ( colour(X), X == blue -> Y = found ; Y = missing ).
?- \+ colour(purple).
