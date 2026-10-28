% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% ancestor.pl -- facts, a recursive rule, and backtracking over all answers
%
% Etymology: ancestor, Latin antecessor "one who goes before"
% (ante "before" + cedere "to go").
%
% Usage:
%   swipl -q ../emit.pl -- ancestor.pl | ../wam -all -

%% ── Facts ─────────────────────────────────────────────────────────────────

parent(tom, bob).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).

%% ── Rules ─────────────────────────────────────────────────────────────────

ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).

%% ── Queries ───────────────────────────────────────────────────────────────

?- ancestor(tom, X).
?- ancestor(X, jim).
?- ancestor(A, B).
?- ancestor(ann, X).
