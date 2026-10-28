%% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
%% Copyright Ahmad Ali Parr
%%
%% axioms.pl — The Logos Etymology Rules
%%
%% Etymology: *leg-* (Proto-Indo-European: to gather, to speak) → Greek legein
%%            → logos (word, reason) → logikos → Latin logica → logic.
%% The lexicon GATHERS. Every edge carries its source. Evidence or nothing.
%%
%% This is the canonical logic. ingest.awk writes the facts this file reasons
%% over, and LogosLexicon.mlw states the same shapes for Why3.
%%
%% Usage (SWI-Prolog):
%%   $ awk -f src/ingest.awk data/seed.tsv > examples/seed_facts.pl
%%   $ swipl -q -s src/axioms.pl -s examples/seed_facts.pl
%%   ?- ancestor(Word, Ancestor).
%%   ?- shared_root(WordA, WordB, Root).

%% ── Fact shape ────────────────────────────────────────────────────────────────
%%
%% Every word is a lexeme with an id. Everything else hangs off that id:
%%   lexeme(WordId, Language, Form)
%%   etymology_text(WordId, Text, Source)
%%   orthographic_slice(WordId, Position, Letter)
%%   derived_from(Descendant, Ancestor, Source)
%%   morpheme(WordId, Position, Form, Kind, Source)
%%   sense(WordId, SenseId, Gloss, Source)
%%
%% Source is an atom naming where the edge came from.
%% Kind is 'root' for a root morpheme.

:- dynamic lexeme/3, etymology_text/3, orthographic_slice/3.
:- dynamic derived_from/3, morpheme/5, sense/4.

%% ── Ancestry ──────────────────────────────────────────────────────────────────
%%
%% ancestor(+Word, -Ancestor)
%%
%% A direct derived_from edge is an ancestor. Past that, we walk the chain and
%% remember every word we have stood on, so a loop in the data cannot trap us.

%% Branch 1: direct
%% One recorded derivation, source attached.
ancestor(A,B) :- derived_from(A,B,_).

%% Branch 2: through the chain
%% Follow derived_from edge by edge. Seen holds the words already visited.
ancestor(A,B) :- ancestor_path(A,B,[A]).

ancestor_path(A,B,Seen) :- derived_from(A,C,_), \+ memberchk(C,Seen), (B=C ; ancestor_path(C,B,[C|Seen])).

%% ── Shared roots ──────────────────────────────────────────────────────────────
%%
%% shared_root(?WordA, ?WordB, ?Root)
%%
%% Two different words that carry the same root morpheme.

shared_root(A,B,R) :- morpheme(A,_,R,root,_), morpheme(B,_,R,root,_), dif(A,B).

%% ── Evidence along the chain ──────────────────────────────────────────────────
%%
%% ancestor_via(+Word, ?Ancestor, -Sources)
%%
%% Same walk as ancestor/2, but it hands back the source of every edge it
%% crossed, in order. Every answer traces back to where it came from.

ancestor_via(A,B,Sources) :- via_path(A,B,[A],Sources).

via_path(A,B,_,[S])       :- derived_from(A,B,S).
via_path(A,B,Seen,[S|Ss]) :- derived_from(A,C,S), \+ memberchk(C,Seen), via_path(C,B,[C|Seen],Ss).

%% ── Shared ancestry ───────────────────────────────────────────────────────────
%%
%% shared_ancestor(?WordA, ?WordB, ?Ancestor)
%%
%% Two different words whose recorded chains meet at the same ancestor.
%% Both chains are asserted edges. Nothing is guessed from spelling.

shared_ancestor(A,B,X) :- ancestor(A,X), ancestor(B,X), dif(A,B).

%% ── Roots and segmentation ────────────────────────────────────────────────────
%%
%% root_of(?Word, ?Root): a root morpheme the word carries.
%% segmentation(+Word, -Forms): its morphemes in order of position.

root_of(W,R) :- morpheme(W,_,R,root,_).

segmentation(W,Forms) :-
    findall(P-F, morpheme(W,P,F,_,_), Pairs),
    Pairs \== [],
    msort(Pairs, Sorted),
    findall(F, member(_-F, Sorted), Forms).

%% ── Meaning ───────────────────────────────────────────────────────────────────
%%
%% gloss(?Word, ?Gloss): any recorded sense of the word.

gloss(W,G) :- sense(W,_,G,_).

%% ── Spelling ──────────────────────────────────────────────────────────────────
%%
%% spelling(+Word, -Letters): the word's orthographic slices, in order.

spelling(W,Letters) :-
    findall(P-L, orthographic_slice(W,P,L), Pairs),
    Pairs \== [],
    msort(Pairs, Sorted),
    findall(L, member(_-L, Sorted), Letters).

%% ── What is never inferred ────────────────────────────────────────────────────
%%
%% No rule infers historical derivation from orthographic similarity.
%% A letter slice is just letters. Only an asserted derived_from edge, with its
%% source, makes one word the ancestor of another.
