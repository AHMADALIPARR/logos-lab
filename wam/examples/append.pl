% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% append.pl -- append/3 joins lists and, run backwards, splits them
%
% Etymology: append, Latin appendere "to hang upon" (ad "to" + pendere "to hang").
%
% Usage:
%   swipl -q ../emit.pl -- append.pl | ../wam -all -

%% ── Rules ─────────────────────────────────────────────────────────────────

append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

%% ── Queries ───────────────────────────────────────────────────────────────

?- append([a,b], [c], X).
?- append(X, Y, [a,b,c]).
?- append(X, [c], [a,b,c]).
?- append([a|T], [z], [a,b,z]).
