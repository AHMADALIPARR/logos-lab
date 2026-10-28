% Source-aware relations: only assert evidence-backed edges.
:- dynamic lexeme/3, etymology_text/3, orthographic_slice/3.
:- dynamic derived_from/3, morpheme/5, sense/4.
% derived_from(Descendant,Ancestor,Source).
% morpheme(WordId,Position,Form,Kind,Source).
% sense(WordId,SenseId,Gloss,Source).
ancestor(A,B) :- derived_from(A,B,_).
ancestor(A,B) :- ancestor_path(A,B,[A]).
ancestor_path(A,B,Seen) :- derived_from(A,C,_), \+ memberchk(C,Seen), (B=C ; ancestor_path(C,B,[C|Seen])).
shared_root(A,B,R) :- morpheme(A,_,R,root,_), morpheme(B,_,R,root,_), dif(A,B).
% No rule infers historical derivation from orthographic similarity.
