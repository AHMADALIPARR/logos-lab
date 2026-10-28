source('95700b049613a4cd9da8d15f','Wiktextract','/mnt/data/logos_real/examples/sample.jsonl','unknown','dataset').
evidence('057e1ed9e572fd0dae48dcde','95700b049613a4cd9da8d15f','jsonl:1:en:reconstruction:noun','Wiktextract lexical record','reported').
evidence('ce534ddf246db3d2f3ead7fb','95700b049613a4cd9da8d15f','jsonl:2:en:logic:noun','Wiktextract lexical record','reported').
lexeme('297401a141ee06ca4c099aed','reconstruction','en','noun',0).
lexeme('63b9c225ee5fa268f3891df3','logic','en','noun',0).
lexeme_evidence('297401a141ee06ca4c099aed','057e1ed9e572fd0dae48dcde').
lexeme_evidence('63b9c225ee5fa268f3891df3','ce534ddf246db3d2f3ead7fb').
sense('444fab610c4eb24fe4c1efef','297401a141ee06ca4c099aed','the act of constructing again','0.0','057e1ed9e572fd0dae48dcde').
sense('f5b8c33a338415049e512e72','63b9c225ee5fa268f3891df3','the study of valid inference','0.0','ce534ddf246db3d2f3ead7fb').
slice('297401a141ee06ca4c099aed','etymological',0,'Illustrative record: source claim requires external verification',none,none,'unparsed_claim','057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','morphological',0,'re-',none,none,'prefix','057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','morphological',1,'construct',none,none,'base','057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','morphological',2,'-ion',none,none,'suffix','057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',0,'r',0,1,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',1,'e',1,2,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',2,'c',2,3,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',3,'o',3,4,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',4,'n',4,5,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',5,'s',5,6,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',6,'t',6,7,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',7,'r',7,8,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',8,'u',8,9,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',9,'c',9,10,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',10,'t',10,11,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',11,'i',11,12,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',12,'o',12,13,none,'057e1ed9e572fd0dae48dcde').
slice('297401a141ee06ca4c099aed','orthographic',13,'n',13,14,none,'057e1ed9e572fd0dae48dcde').
slice('63b9c225ee5fa268f3891df3','orthographic',0,'l',0,1,none,'ce534ddf246db3d2f3ead7fb').
slice('63b9c225ee5fa268f3891df3','orthographic',1,'o',1,2,none,'ce534ddf246db3d2f3ead7fb').
slice('63b9c225ee5fa268f3891df3','orthographic',2,'g',2,3,none,'ce534ddf246db3d2f3ead7fb').
slice('63b9c225ee5fa268f3891df3','orthographic',3,'i',3,4,none,'ce534ddf246db3d2f3ead7fb').
slice('63b9c225ee5fa268f3891df3','orthographic',4,'c',4,5,none,'ce534ddf246db3d2f3ead7fb').
slice('63b9c225ee5fa268f3891df3','phonological',0,'/ˈlɒdʒɪk/',none,none,'ipa','ce534ddf246db3d2f3ead7fb').
ancestry(A,B,Proof) :- ancestry_walk(A,B,[A],Proof).
ancestry_walk(A,B,_,[E]) :- relation(_,A,B,T,E,'attested'), ancestry_type(T).
ancestry_walk(A,C,Visited,[E|Proof]) :-
  relation(_,A,B,T,E,'attested'),
  ancestry_type(T),
  \+ memberchk(B,Visited),
  ancestry_walk(B,C,[B|Visited],Proof).
ancestry_type('derived_from').
ancestry_type('inherited_from').
ancestry_type('borrowed_from').
