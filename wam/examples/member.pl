% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% member.pl -- member/2 gives every element on backtracking
%
% Etymology: member, Latin membrum "limb, part of a body".
%
% Usage:
%   swipl -q ../emit.pl -- member.pl | ../wam -all -

%% ── Rules ─────────────────────────────────────────────────────────────────

member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

%% ── Queries ───────────────────────────────────────────────────────────────

?- member(X, [a,b,c]).
?- member(b, [a,b,c]).
?- member(z, [a,b,c]).
?- member(X, [a,b,c]), member(X, [c,b]).
