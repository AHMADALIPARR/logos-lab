/* SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
   Copyright Ahmad Ali Parr */
/* logicstack.c — bit logic, unifier, FOIL, mini-MIL, tree
   cc -O2 -o logicstack logicstack.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define W 4               /* bit-vector width */
#define MAXEX 16          /* 2^W */
#define MAXR 32
/* ============ L0: BINARY ============ */
static int bitand(int a,int b){return a&b;}
static int bitor (int a,int b){return a|b;}
static int bitxor(int a,int b){return a^b;}
typedef struct { int b[W]; } Ex;
static Ex EX[MAXEX]; static int NEX;
static int POS[MAXEX], NPOS, NEG[MAXEX], NNEG;
static void mk_examples(void){
    NEX = 1<<W;
    for(int i=0;i<NEX;i++)
        for(int j=0;j<W;j++) EX[i].b[j] = (i>>(W-1-j))&1;
    NPOS=NNEG=0;
    for(int i=0;i<NEX;i++){
        int s=0; for(int j=0;j<W;j++) s+=EX[i].b[j];
        if(s&1) POS[NPOS++]=i; else NEG[NNEG++]=i;
    }
}
/* ============ L1: LOGIC / unification ============ */
typedef enum { CONST, VAR } TKind;
typedef struct { TKind k; char n[8]; } Term;
typedef struct { char pred[8]; Term t[2]; int n; } Atom;
typedef struct { Atom h; Atom body[4]; int nb; } Clause;
typedef struct { Term v, t; } Bind;
static Term mkc(const char*n){Term t;t.k=CONST;strncpy(t.n,n,7);t.n[7]=0;return t;}
static Term mkv(const char*n){Term t;t.k=VAR;strncpy(t.n,n,7);t.n[7]=0;return t;}
static Term look(Bind*bl,int nb,Term t){
    for(int i=0;i<nb;i++) if(t.k==VAR&&!strcmp(t.n,bl[i].v.n)) return look(bl,nb,bl[i].t);
    return t;
}
static int unify(Term*a,Term*b,int na,int nb,Bind*out,int*no){
    Bind tmp[8]; int n=0;
    for(int i=0;i<na;i++){
        Term x=look(tmp,n,a[i]), y=look(tmp,n,b[i]);
        if(x.k==VAR){ tmp[n].v=x; tmp[n].t=y; n++; }
        else if(y.k==VAR){ tmp[n].v=y; tmp[n].t=x; n++; }
        else if(strcmp(x.n,y.n)) return 0;
    }
    memcpy(out,tmp,n*sizeof(Bind)); *no=n; return 1;
}
/* clause database: BK facts */
static Clause KB[64]; static int NKB=0;
static void fact(const char*p, const char*a, const char*b){
    Clause c; strcpy(c.h.pred,p); c.h.t[0]=mkc(a); c.h.t[1]=mkc(b);
    c.h.n=2; c.nb=0; KB[NKB++]=c;
}
static int FRESH=0;   /* tag used to rename a clause's variables apart on each call */
static Term ren_t(Term t,int tag){
    if(t.k==VAR){ char nm[8]; snprintf(nm,sizeof nm,"%.1s%d",t.n,tag%100000); strcpy(t.n,nm); }
    return t;
}
/* solve a goal list left to right, threading the bindings (backtracks over clauses) */
static int solve(Atom*gs,int ng,Bind*bl,int nbl,int depth){
    if(ng==0) return 1;
    if(depth<=0) return 0;
    Atom g=gs[0]; Term args[2];
    for(int k=0;k<g.n;k++) args[k]=look(bl,nbl,g.t[k]);
    for(int i=0;i<NKB;i++){
        if(strcmp(KB[i].h.pred,g.pred)||KB[i].h.n!=g.n) continue;
        Clause c=KB[i]; int tag=++FRESH;
        for(int k=0;k<c.h.n;k++) c.h.t[k]=ren_t(c.h.t[k],tag);
        for(int j=0;j<c.nb;j++) for(int k=0;k<c.body[j].n;k++) c.body[j].t[k]=ren_t(c.body[j].t[k],tag);
        Bind b2[8]; int n2;
        if(!unify(args,c.h.t,g.n,c.h.n,b2,&n2)) continue;
        Bind merged[128]; int nm=nbl;
        if(nbl+n2>128) continue;
        memcpy(merged,bl,nbl*sizeof(Bind));
        for(int j=0;j<n2;j++) merged[nm++]=b2[j];
        Atom ngs[16]; int nn=0;
        for(int j=0;j<c.nb;j++) ngs[nn++]=c.body[j];
        for(int j=1;j<ng&&nn<16;j++) ngs[nn++]=gs[j];
        if(solve(ngs,nn,merged,nm,depth-1)) return 1;
    }
    return 0;
}
static int prove(const char*p, Term*args, int na, Bind*bl, int nbl, int depth){
    Atom g; strcpy(g.pred,p); g.n=na;
    for(int k=0;k<na;k++) g.t[k]=args[k];
    return solve(&g,1,bl,nbl,depth);
}
/* ============ L2: FOIL ============ */
typedef struct { int kind; int i,j,v; } Lit;  /* 0: has, 1: and, 2: xor */
static int DONE[MAXEX];   /* positives already covered by an earlier clause (separate & conquer) */
static Lit RULE[MAXR]; static int NRULE;
static int litHolds(Lit*l, Ex*e){
    return l->kind==0 ? (e->b[l->i]==l->v)
         : l->kind==1 ? (bitand(e->b[l->i],e->b[l->j])==l->v)
                      : (bitxor(e->b[l->i],e->b[l->j])==l->v);
}
static int covers(Lit*r,int n,Ex*e){
    for(int i=0;i<n;i++) if(!litHolds(&r[i],e)) return 0;
    return 1;
}
static double entropy(double p){
    if(p<=0||p>=1) return 0; return -(p*log(p)+(1-p)*log(1-p));
}
static double foilGain(Lit*newlit, Lit*r,int n){
    int pn=0,nn=NNEG; for(int i=0;i<NPOS;i++) if(!DONE[POS[i]]) pn++;
    int tot=pn+nn; if(!tot) return 0;
    int sp=0,sn=0;
    for(int i=0;i<NPOS;i++) if(!DONE[POS[i]]&&covers(r,n,&EX[POS[i]])&&litHolds(newlit,&EX[POS[i]])) sp++;
    for(int i=0;i<nn;i++) if(covers(r,n,&EX[NEG[i]])&&litHolds(newlit,&EX[NEG[i]])) sn++;
    if(!sn&&!sp) return 0;
    double p0=(double)pn/tot;
    int subn=sp+sn;
    double p1=subn? (double)sp/subn : 0;
    return entropy(p0)-((double)subn/tot)*entropy(p1);
}
/* precision of rule r (n lits) over the still-uncovered positives and all negatives */
static double prec(Lit*r,int n){
    int c=0,m=0;
    for(int i=0;i<NPOS;i++) if(!DONE[POS[i]]&&covers(r,n,&EX[POS[i]])) c++;
    for(int i=0;i<NNEG;i++) if(covers(r,n,&EX[NEG[i]])) m++;
    return c+m? (double)c/(c+m) : 0;
}
static int covpos(Lit*r,int n){
    int c=0; for(int i=0;i<NPOS;i++) if(!DONE[POS[i]]&&covers(r,n,&EX[POS[i]])) c++;
    return c;
}
static int allLits(Lit*out){
    int n=0;
    for(int kind=0;kind<3;kind++)
    for(int i=0;i<W;i++) for(int j=(kind?i+1:0);j<(kind?W:1);j++)
    for(int v=0;v<2;v++){ Lit l={kind,i,j,v}; out[n++]=l; }
    return n;
}
static void foil(void){
    NRULE=0;
    for(;;){
        int anyNeg=0;
        for(int i=0;i<NNEG && !anyNeg;i++) if(covers(RULE,NRULE,&EX[NEG[i]])) anyNeg=1;
        if(!anyNeg) break;
        Lit best; double bg=-1; int found=0;
        for(int kind=0;kind<3;kind++)
        for(int i=0;i<W;i++) for(int j=(kind?i+1:0);j<(kind?W:i+1);j++)
        for(int v=0;v<2;v++){
            Lit l={kind,i,j,v};
            int dup=0;
            for(int k=0;k<NRULE;k++) if(RULE[k].kind==kind&&RULE[k].i==i&&RULE[k].j==j&&RULE[k].v==v) dup=1;
            if(dup) continue;
            double g=foilGain(&l,RULE,NRULE);
            if(g>bg){bg=g;best=l;found=1;}
        }
        if(found && prec(RULE,NRULE) < 1 && NRULE<MAXR) {
            RULE[NRULE]=best;
            if(prec(RULE,NRULE+1) > prec(RULE,NRULE)){ NRULE++; continue; }
        }
        /* plateau (parity: every single literal leaves precision unchanged): look ahead two literals */
        { Lit all[64]; int na=allLits(all); double bp=prec(RULE,NRULE); int got=0,bc=0; Lit b1,b2;
          for(int a=0;a<na;a++) for(int b=0;b<na;b++){
              if(a==b||NRULE+2>MAXR) continue;
              RULE[NRULE]=all[a]; RULE[NRULE+1]=all[b];
              double pp=prec(RULE,NRULE+2);
              int cv=covpos(RULE,NRULE+2);   /* ties: more positives covered */
              if(pp>bp+1e-9 || (got&&pp>bp-1e-9&&cv>bc)){bp=pp;bc=cv;b1=all[a];b2=all[b];got=1;}
          }
          if(!got) break;
          RULE[NRULE++]=b1; RULE[NRULE++]=b2; }
    }
}
/* separate & conquer: learn clauses until every positive is covered */
static Lit RULES[8][MAXR]; static int NRL[8], NRULES;
static void foil_all(void){
    NRULES=0;
    for(;;){
        int left=0; for(int i=0;i<NPOS;i++) if(!DONE[POS[i]]) left++;
        if(!left||NRULES>=8) break;
        foil();
        int newly=0;
        for(int i=0;i<NPOS;i++) if(!DONE[POS[i]]&&covers(RULE,NRULE,&EX[POS[i]])){DONE[POS[i]]=1;newly++;}
        if(!newly) break;
        memcpy(RULES[NRULES],RULE,NRULE*sizeof(Lit)); NRL[NRULES++]=NRULE;
    }
}
/* ============ L3: METAGOL (mini) ============
   meta-rule chain: P(A,B) :- Q(A,C), R(C,B)
   invented inv1 = next;next  (transitive closure) */
static void mkf(const char*q1,const char*q2){
    Clause c; strcpy(c.h.pred,"f");
    c.h.t[0]=mkv("A"); c.h.t[1]=mkv("B"); c.h.n=2;
    strcpy(c.body[0].pred,q1); c.body[0].t[0]=mkv("A"); c.body[0].n=2;
    if(!q2){ c.body[0].t[1]=mkv("B"); c.nb=1; }
    else { c.body[0].t[1]=mkv("C"); c.nb=2;
        strcpy(c.body[1].pred,q2); c.body[1].t[0]=mkv("C"); c.body[1].t[1]=mkv("B"); c.body[1].n=2; }
    KB[NKB++]=c;
}
static void initKB(void){
    NKB=0;
    fact("next","0","1"); fact("next","1","2"); fact("next","2","3");
    /* invented predicate via meta-chain */
    Clause c; strcpy(c.h.pred,"inv1");
    c.h.t[0]=mkv("A"); c.h.t[1]=mkv("B"); c.h.n=2;
    strcpy(c.body[0].pred,"next"); c.body[0].t[0]=mkv("A"); c.body[0].t[1]=mkv("C"); c.body[0].n=2;
    strcpy(c.body[1].pred,"next"); c.body[1].t[0]=mkv("C"); c.body[1].t[1]=mkv("B"); c.body[1].n=2;
    c.nb=2; KB[NKB++]=c;
    /* target f: f(A,B):-next(A,B).  f(A,B):-inv1(A,B).  f(A,B):-next(A,C),inv1(C,B). */
    mkf("next",NULL); mkf("inv1",NULL); mkf("next","inv1");
}
static int milQuery(const char*a,const char*b){
    Term q[2]={mkc(a),mkc(b)}; Bind bl[4];
    return prove("inv1",q,2,bl,0,8);
}
static int nextQuery(const char*a,const char*b){
    Term q[2]={mkc(a),mkc(b)}; Bind bl[4];
    return prove("next",q,2,bl,0,8);
}
static int fQuery(const char*a,const char*b){
    Term q[2]={mkc(a),mkc(b)}; Bind bl[4];
    return prove("f",q,2,bl,0,24);
}
/* ============ L4: TREE ============ */
static void printTree(int depth){
    for(int i=0;i<NRULE;i++){
        for(int d=0;d<depth+i;d++) putchar(' ');
        Lit* l=&RULE[i];
        if(l->kind==0) printf("node: b[%d]==%d\n",l->i,l->v);
        else if(l->kind==1) printf("node: b[%d]&b[%d]==%d\n",l->i,l->j,l->v);
        else           printf("node: b[%d]^b[%d]==%d\n",l->i,l->j,l->v);
    }
    for(int d=0;d<depth+NRULE;d++) putchar(' ');
    printf("leaf: pos (odd parity)\n");
}
int main(void){
    mk_examples();
    printf("L0: %d pos / %d neg over %d-bit vectors\n",NPOS,NNEG,W);
    initKB();
    printf("L1: next(0,1)? %d  inv1(0,2) [meta-chain]? %d  inv1(2,0)? %d\n",
        nextQuery("0","1"), milQuery("0","2"), milQuery("2","0"));
    foil_all();
    printf("L2: FOIL rules (%d clauses):\n",NRULES);
    for(int c=0;c<NRULES;c++){
        printf("     target(E) :-");
        for(int i=0;i<NRL[c];i++){
            Lit*l=&RULES[c][i];
            if(l->kind==0)      printf(" b[%d]==%d",l->i,l->v);
            else if(l->kind==1) printf(" b[%d]&b[%d]==%d",l->i,l->j,l->v);
            else                printf(" b[%d]^b[%d]==%d",l->i,l->j,l->v);
            printf(i+1<NRL[c]?",":".");
        }
        printf("\n");
    }
    { static const char*MP[6][2]={{"0","1"},{"1","2"},{"2","3"},{"0","2"},{"0","3"},{"1","3"}};
      static const char*MN[3][2]={{"3","0"},{"2","0"},{"3","1"}};
      int cp=0,cn=0;
      for(int i=0;i<6;i++) cp+=fQuery(MP[i][0],MP[i][1]);
      for(int i=0;i<3;i++) cn+=fQuery(MN[i][0],MN[i][1]);
      printf("L3: metagol inv1 = next;next (chain meta-rule, invented)\n");
      printf("     f(A,B) :- next(A,B).  f(A,B) :- inv1(A,B).  f(A,B) :- next(A,C), inv1(C,B).\n");
      printf("     f covers %d/6 pos, %d/3 neg\n",cp,cn); }
    printf("L4: tree:\n");
    for(int c=0;c<NRULES;c++){ memcpy(RULE,RULES[c],NRL[c]*sizeof(Lit)); NRULE=NRL[c]; printf("  clause %d:\n",c+1); printTree(4); }
    { int ok=0; for(int e=0;e<NEX;e++){ int pred=0;
          for(int c=0;c<NRULES;c++) if(covers(RULES[c],NRL[c],&EX[e])) pred=1;
          int t=0; for(int k=0;k<W;k++) t+=EX[e].b[k];
          if(pred==(t&1)) ok++; }
      printf("training accuracy: %.3f\n",(double)ok/NEX); }
    return 0;
}
