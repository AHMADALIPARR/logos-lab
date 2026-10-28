% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr

% syntax.pl -- the ISO syntax the emitter reads
%
% Etymology: syntax, Greek syntaxis "arrangement" (syn "together" + tassein
% "to put in order").
%
% Usage:
%   swipl -q ../emit.pl -- syntax.pl | ../wam -all -

/* Block comments
   can span lines. */

:- op(700, xfx, ===>).
:- op(200, xfy, &).

%% ── Quoted atoms and character codes ──────────────────────────────────────

name_of('Hello World', greeting).
name_of('it''s', apostrophe).
name_of('tab\there', escape).
name_of([], nil).
name_of({}, braces).

code_of(0'a, letter_a).
code_of(0' , space).
code_of(0'', quote).

%% ── Numbers, strings, curly terms and partial lists ───────────────────────

number_of(42, int).
number_of(-7, negative).
number_of(3.14, float).
number_of(0x1F, hex).
number_of(0b101, binary).

text("hi", codes).
curly({a, b}).
partial([a, b|T], T).

%% ── Operators ─────────────────────────────────────────────────────────────

rule(a ===> b).
rule(x & y & z).
rule(- (1)).
rule(1 - 2 - 3).
rule(2 ** 3).
rule(a = b).

%% ── Queries ───────────────────────────────────────────────────────────────

?- name_of(X, greeting).
?- name_of('it''s', K).
?- name_of(X, escape).
?- name_of(X, braces).
?- code_of(97, K).
?- code_of(X, space).
?- number_of(X, hex).
?- number_of(X, float).
?- text(S, codes).
?- curly(X).
?- partial([a, b, c, d], T).
?- partial(L, [z]).
?- rule(a ===> X).
?- rule(x & Y).
?- rule(1 - 2 - X).
?- rule(X = Y).
