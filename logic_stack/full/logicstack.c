/* SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
   Copyright Ahmad Ali Parr */
/* logicstack.c — full ILP kernel: FOIL + Metagol + ILASP-lite + tree
   cc -O2 -o logicstack logicstack.c -lm && ./logicstack */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define W 4
#define MAXEX 32
#define MAXRULE 8
#define MAXLIT 12
#define MAXCLAUSE 16
#define MAXTERM 4
#define MAXB 128   /* max bindings in one proof */
/* ============================================================
   L0: BINARY
   ============================================================ */
static int band(int a,int b){return a*b;}
static int borb(int a,int b){return a>b?a:b;}
static int bxorb(int a,int b){return (a+b)&1;}
typedef struct { int b[W]; } Ex;
static Ex EXS[MAXEX]; static int NEX;
static int POS[MAXEX], NPOS, NEG[MAXEX], NNEG;
static void mk_examples(void){
    NEX = 1<<W;
    for(int i=0;i<NEX;i++)
        for(int j=0;j<W;j++) EXS[i].b[j]=(i>>(W-1-j))&1;
    NPOS=NNEG=0;
    for(int i=0;i<NEX;i++){
        int s=0; for(int j=0;j<W;j++) s+=EXS[i].b[j];
        if(s&1) POS[NPOS++]=i; else NEG[NNEG++]=i;
    }
}
/* ============================================================
   L1: LOGIC — terms, unification, depth-bounded resolution
   ============================================================ */
typedef enum{CONST,VAR} TKind;
typedef struct{TKind k;char n[8];} Term;
static Term mkc(const char*n){Term t;t.k=CONST;strncpy(t.n,n,7);t.n[7]=0;return t;}
static Term mkv(const char*n){Term t;t.k=VAR;strncpy(t.n,n,7);t.n[7]=0;return t;}
typedef struct{char pred[8];Term t[MAXTERM];int n;} Atom;
typedef struct{Atom h;Atom body[MAXTERM];int nb;} Clause;
typedef struct{char v[8];Term t;} Bind;
static Term walk(Bind*bl,int nb,Term t){
    if(t.k==VAR)
        for(int i=0;i<nb;i++)
            if(!strcmp(t.n,bl[i].v)) return walk(bl,nb,bl[i].t);
    return t;
}
static int occurs(const char*x,Term t,Bind*bl,int nb){
    Term w=walk(bl,nb,t);
    return w.k==VAR && !strcmp(w.n,x);
}
static int unify_t(Term a,Term b,Bind*bl,int nb,Bind*out,int*no){
    Term x=walk(bl,nb,a), y=walk(bl,nb,b);
    Bind tmp[MAXB]; int n=nb;
    memcpy(tmp,bl,nb*sizeof(Bind));
    if(x.k==VAR&&y.k==VAR&&!strcmp(x.n,y.n)){memcpy(out,tmp,n*sizeof(Bind));*no=n;return 1;}
    if(x.k==VAR){ if(occurs(x.n,y,tmp,n))return 0;
        strcpy(tmp[n].v,x.n);tmp[n].t=y;n++; }
    else if(y.k==VAR){ if(occurs(y.n,x,tmp,n))return 0;
        strcpy(tmp[n].v,y.n);tmp[n].t=x;n++; }
    else if(x.k==CONST&&y.k==CONST&&!strcmp(x.n,y.n)){ }
    else return 0;
    memcpy(out,tmp,n*sizeof(Bind));*no=n;return 1;
}
static int unify(Term*a,int na,Term*b,int nb2,Bind*bl,int nbl,Bind*out,int*no);
static int unify_at(Term*a,int na,Term*b,Bind*bl,int nb,Bind*out,int*no){
    /* unify two argument vectors of the same arity na */
    if(na<=0||na>MAXTERM) return 0;   /* arity check */
    return unify(a,na,b,na,bl,nb,out,no);
}
static int unify(Term*a,int na,Term*b,int nb2,Bind*bl,int nbl,Bind*out,int*no){
    if(na!=nb2) return 0;
    Bind cur[MAXB]; int n=nbl;
    memcpy(cur,bl,nbl*sizeof(Bind));
    for(int i=0;i<na;i++){
        Bind tmp[MAXB]; int tn;
        if(!unify_t(a[i],b[i],cur,n,tmp,&tn)) return 0;
        memcpy(cur,tmp,tn*sizeof(Bind)); n=tn;
    }
    memcpy(out,cur,n*sizeof(Bind)); *no=n; return 1;
}
static Clause KB[64]; static int NKB=0;
static void fact(const char*p,const char*a,const char*b){
    Clause c; strcpy(c.h.pred,p); c.h.t[0]=mkc(a); c.h.t[1]=mkc(b);
    c.h.n=2; c.nb=0; KB[NKB++]=c;
}
static void rule1(const char*p,const char*q){
    /* p(A,B) :- q(A,B)   (ident) */
    Clause c; strcpy(c.h.pred,p);
    c.h.t[0]=mkv("A"); c.h.t[1]=mkv("B"); c.h.n=2;
    strcpy(c.body[0].pred,q); c.body[0].t[0]=mkv("A"); c.body[0].t[1]=mkv("B"); c.body[0].n=2;
    c.nb=1; KB[NKB++]=c;
}
static void rule_tail(const char*p,const char*q){
    /* p(A,B) :- q(A,C), p(C,B)   (tailrec) */
    Clause c; strcpy(c.h.pred,p);
    c.h.t[0]=mkv("A"); c.h.t[1]=mkv("B"); c.h.n=2;
    strcpy(c.body[0].pred,q); c.body[0].t[0]=mkv("A"); c.body[0].t[1]=mkv("C"); c.body[0].n=2;
    strcpy(c.body[1].pred,p); c.body[1].t[0]=mkv("C"); c.body[1].t[1]=mkv("B"); c.body[1].n=2;
    c.nb=2; KB[NKB++]=c;
}
static void rule2(const char*p,const char*q,const char*r){
    /* p(A,B) :- q(A,C), r(C,B) */
    Clause c; strcpy(c.h.pred,p);
    c.h.t[0]=mkv("A"); c.h.t[1]=mkv("B"); c.h.n=2;
    strcpy(c.body[0].pred,q); c.body[0].t[0]=mkv("A"); c.body[0].t[1]=mkv("C"); c.body[0].n=2;
    strcpy(c.body[1].pred,r); c.body[1].t[0]=mkv("C"); c.body[1].t[1]=mkv("B"); c.body[1].n=2;
    c.nb=2; KB[NKB++]=c;
}
static int FRESH=0;   /* tag used to rename a clause's variables apart per call */
static Term ren_t(Term t,int tag){
    if(t.k==VAR){ char nm[8]; snprintf(nm,sizeof nm,"%.1s%d",t.n,tag%100000); strcpy(t.n,nm); }
    return t;
}
/* solve a goal list left to right, threading bindings (backtracks over clauses) */
static int solve(Atom*gs,int ng,Bind*bl,int nbl,int depth){
    if(ng==0) return 1;
    if(depth<=0) return 0;
    Atom g=gs[0];
    for(int i=0;i<NKB;i++){
        if(strcmp(KB[i].h.pred,g.pred)||KB[i].h.n!=g.n) continue;
        int tag=++FRESH;
        Clause c=KB[i];
        for(int k=0;k<c.h.n;k++) c.h.t[k]=ren_t(c.h.t[k],tag);
        for(int j=0;j<c.nb;j++)
            for(int k=0;k<c.body[j].n;k++) c.body[j].t[k]=ren_t(c.body[j].t[k],tag);
        Bind b2[MAXB]; int n2;
        if(!unify(g.t,g.n,c.h.t,c.h.n,bl,nbl,b2,&n2)) continue;
        Atom ngs[32]; int nn=0;
        for(int j=0;j<c.nb;j++) ngs[nn++]=c.body[j];
        for(int j=1;j<ng&&nn<32;j++) ngs[nn++]=gs[j];
        if(solve(ngs,nn,b2,n2,depth-1)) return 1;
    }
    return 0;
}
static int prove(const char*p,Term*args,int na,Bind*bl,int nbl,int depth){
    Atom g; strcpy(g.pred,p); g.n=na;
    for(int k=0;k<na;k++) g.t[k]=args[k];
    return solve(&g,1,bl,nbl,depth);
}
/* ============================================================
   L2: GENERAL FOIL
   ============================================================ */
typedef struct{int kind; /*0 Has 1 And 2 Geq 3 Xor*/ int i,j,v;} Lit;
static int RPOS[MAXEX], NRPOS;   /* positives not yet covered (set by foil_clause) */
typedef Lit Rule[MAXLIT];
static int lit_holds(Lit*l,Ex*e){
    switch(l->kind){
        case 0: return e->b[l->i]==l->v;
        case 1: return band(e->b[l->i],e->b[l->j])==l->v;
        case 2: return e->b[l->i]>=l->v;
        default:return bxorb(e->b[l->i],e->b[l->j])==l->v;
    }
}
static int covers(Rule r,int n,Ex*e){
    for(int i=0;i<n;i++) if(!lit_holds(&r[i],e)) return 0;
    return 1;
}
static int in_rule(Rule r,int n,Lit*l){
    for(int i=0;i<n;i++)
        if(r[i].kind==l->kind&&r[i].i==l->i&&r[i].j==l->j&&r[i].v==l->v) return 1;
    return 0;
}
static double foil_gain(Lit l,Rule r,int n){
    int p0=0,n0=0,p1=0,n1=0;
    for(int i=0;i<NRPOS;i++){
        int c=covers(r,n,&EXS[RPOS[i]]);
        int c1=c&&lit_holds(&l,&EXS[RPOS[i]]);
        if(c)p0++; if(c1)p1++;
    }
    for(int i=0;i<NNEG;i++){
        int c=covers(r,n,&EXS[NEG[i]]);
        int c1=c&&lit_holds(&l,&EXS[NEG[i]]);
        if(c)n0++; if(c1)n1++;
    }
    if(p0+n0==0||p1+n1==0||p1==0) return 0;
    double g1=log2((double)p1/(p1+n1)), g0=log2((double)p0/(p0+n0));
    return p1*(g1-g0);
}
static double log2v(double x){return log(x)/log(2.0);}
static void best_lit(Rule r,int n,Lit*best,double*bg){
    *bg=0; int found=0;
    for(int kind=0;kind<4;kind++)
    for(int i=0;i<W;i++)
    for(int j=0;j<W;j++)
    for(int v=0;v<2;v++){
        if(kind==0&&j!=0) continue;
        if(kind==2&&j!=0) continue;
        if(kind!=0&&kind!=2&&i>=j) continue;
        if(kind==2&&v!=1) continue;
        Lit l={kind,i,j,v};
        if(in_rule(r,n,&l)) continue;
        double g=foil_gain(l,r,n);
        if(g>*bg+1e-9){*bg=g;*best=l;found=1;}
    }
    (void)found;
}
/* plateau: when no single literal has gain (e.g. parity), look ahead two literals */
static int lookahead(Rule r,int n,Lit*b1,Lit*b2){
    Lit cand[64]; int nc=0;
    for(int kind=0;kind<4;kind++)
    for(int i=0;i<W;i++)
    for(int j=0;j<W;j++)
    for(int v=0;v<2;v++){
        if(kind==0&&j!=0) continue;
        if(kind==2&&j!=0) continue;
        if(kind!=0&&kind!=2&&i>=j) continue;
        if(kind==2&&v!=1) continue;
        Lit l={kind,i,j,v};
        if(in_rule(r,n,&l)) continue;
        cand[nc++]=l;
    }
    double bg=1e-9; int found=0;
    for(int a=0;a<nc;a++)
    for(int b=0;b<nc;b++){
        if(a==b) continue;
        Rule r2; memcpy(r2,r,n*sizeof(Lit)); r2[n]=cand[a];
        double g=foil_gain(cand[a],r,n)+foil_gain(cand[b],r2,n+1);
        if(g>bg){bg=g;*b1=cand[a];*b2=cand[b];found=1;}
    }
    return found;
}
/* foil_clause over a subset of positives given by index list */
static int foil_clause(int*pos,int np,Rule out,int*olen){
    Rule r; int n=0;
    NRPOS=np; for(int i=0;i<np;i++) RPOS[i]=pos[i];
    for(;;){
        int any_neg=0;
        for(int i=0;i<NNEG&&!any_neg;i++)
            if(covers(r,n,&EXS[NEG[i]])) any_neg=1;
        if(!any_neg) break;
        Lit best; double g;
        best_lit(r,n,&best,&g);
        if(g<=1e-9){
            Lit b1,b2;
            if(n+2<=MAXLIT&&lookahead(r,n,&b1,&b2)){ r[n++]=b1; r[n++]=b2; continue; }
            break;
        }
        r[n++]=best;
        if(n>=MAXLIT) break;
    }
    memcpy(out,r,n*sizeof(Lit)); *olen=n;
    return n>0;
}
/* separate & conquer: return clause count */
static Rule CLS[MAXCLAUSE];
static int CLN[MAXCLAUSE], NCLS;
static void foil_run(void){
    NCLS=0;
    int remaining[MAXEX], nrem=NPOS;
    for(int i=0;i<NPOS;i++) remaining[i]=POS[i];
    while(nrem>0&&NCLS<MAXCLAUSE){
        Rule c; int cn;
        if(!foil_clause(remaining,nrem,c,&cn)) break;
        memcpy(CLS[NCLS],c,cn*sizeof(Lit)); CLN[NCLS]=cn; NCLS++;
        int k=0;
        for(int i=0;i<nrem;i++)
            if(!covers(c,cn,&EXS[remaining[i]])) remaining[k++]=remaining[i];
        nrem=k;
    }
}
static int cls_covers_any(int ci,Ex*e){
    return covers(CLS[ci],CLN[ci],e);
}
/* ============================================================
   L3b: ILASP-LITE — constraint prune + literal simplify
   ============================================================ */
static int clause_bad(int ci){
    for(int i=0;i<NNEG;i++)
        if(cls_covers_any(ci,&EXS[NEG[i]])) return 1;
    return 0;
}
static void simplify(int ci){
    for(;;){
        int dropped=0;
        for(int d=0;d<CLN[ci]&&!dropped;d++){
            Rule tmp; int tn=0;
            for(int k=0;k<CLN[ci];k++) if(k!=d) tmp[tn++]=CLS[ci][k];
            int bad=0;
            for(int i=0;i<NNEG&&!bad;i++)
                if(covers(tmp,tn,&EXS[NEG[i]])) bad=1;
            if(!bad){ /* still pure: literal redundant */
                memcpy(CLS[ci],tmp,tn*sizeof(Lit)); CLN[ci]=tn; dropped=1;
            }
        }
        if(!dropped) break;
    }
}
static int ilasp_phase(void){
    int kept=0;
    for(int i=0;i<NCLS;i++){
        if(clause_bad(i)) continue;
        simplify(i);
        if(CLN[i]>0||kept==0){ memcpy(CLS[kept],CLS[i],CLN[i]*sizeof(Lit)); CLN[kept]=CLN[i]; kept++; }
    }
    int pruned=NCLS-kept; NCLS=kept;
    return pruned;
}
/* ============================================================
   L3: METAGOL — MIL with invention (inv1 = succ;succ)
   ============================================================ */
static void initKB(void){
    NKB=0;
    fact("succ","0","1"); fact("succ","1","2");
    fact("succ","2","3"); fact("succ","3","4");
}
static int inv1(const char*a,const char*b){
    /* inv1(A,B) :- succ(A,C), succ(C,B)  -- via chain metarule */
    NKB=0; initKB(); rule2("inv1","succ","succ");
    Term q[2]={mkc(a),mkc(b)};
    return prove("inv1",q,2,NULL,0,8);
}
static int target_f(const char*a,const char*b){
    /* f(A,B) :- inv1(A,B)  (invented pred reused) */
    NKB=0; initKB(); rule2("inv1","succ","succ"); rule1("f","inv1"); rule_tail("f","succ");
    Term q[2]={mkc(a),mkc(b)};
    return prove("f",q,2,NULL,0,8);
}
/* MIL consistency check on pos/neg pairs */
static const char*MP[6][2]={{"0","2"},{"1","3"},{"2","4"},{"0","3"},{"0","4"},{"1","4"}};
static const char*MN[4][2]={{"4","0"},{"3","0"},{"2","0"},{"4","1"}};
static int mil_consistent(int mode){
    /* mode 0 ident f:-succ | 1 chain f:-succ,succ | 2 inv1 + f:-inv1 | 3 inv1 + f:-inv1 + tailrec */
    int ok=1;
    for(int i=0;i<10&&ok;i++){
        NKB=0; initKB();
        if(mode==0) rule1("f","succ");
        else if(mode==1) rule2("f","succ","succ");
        else { rule2("inv1","succ","succ"); rule1("f","inv1"); if(mode==3) rule_tail("f","succ"); }
        int pos=i<6;
        const char**pr=pos?MP[i]:MN[i-6];
        Term q[2]={mkc(pr[0]),mkc(pr[1])};
        int got=prove("f",q,2,NULL,0,24);
        if(got!=pos) ok=0;
    }
    return ok;
}
static void mil_report(void){
    int ident_ok=mil_consistent(0), chain_ok=mil_consistent(1);
    if(!ident_ok&&!chain_ok){
        printf("MIL: single metarule inconsistent -> INVENT inv1\n");
        printf("     inv1(A,B) :- succ(A,C), succ(C,B).\n");
        if(mil_consistent(2)) printf("     f(A,B) :- inv1(A,B).\n");
        else if(mil_consistent(3)){
            printf("     f(A,B) :- inv1(A,B).\n");
            printf("     f(A,B) :- succ(A,C), f(C,B).   /* tailrec */\n");
        } else printf("     (no consistent program found)\n");
        printf("     inv1(0,2)=%d inv1(2,0)=%d f(1,3)=%d f(4,1)=%d\n",
            inv1("0","2"),inv1("2","0"),target_f("1","3"),target_f("4","1"));
    } else if(ident_ok){
        printf("MIL: minimal consistent program: f(A,B) :- succ(A,B).\n");
    } else {
        printf("MIL: minimal consistent program: f(A,B) :- succ(A,C), succ(C,B).\n");
    }
}
/* ============================================================
   L4: TREE
   ============================================================ */
static void print_tree(void){
    for(int c=0;c<NCLS;c++){
        for(int l=0;l<CLN[c];l++){
            for(int d=0;d<2+2*l+2*c;d++) putchar(' ');
            Lit*x=&CLS[c][l];
            switch(x->kind){
                case 0: printf("node b%d=%d\n",x->i,x->v); break;
                case 1: printf("node b%d&b%d=%d\n",x->i,x->j,x->v); break;
                case 2: printf("node b%d>=%d\n",x->i,x->v); break;
                default:printf("node b%d^b%d=%d\n",x->i,x->j,x->v);
            }
        }
        for(int d=0;d<2+2*CLN[c]+2*c;d++) putchar(' ');
        printf("leaf YES\n");
    }
}
static int predict(Ex*e){
    for(int c=0;c<NCLS;c++)
        if(cls_covers_any(c,e)) return 1;
    return 0;
}
static double accuracy(void){
    int tp=0,tn=0;
    for(int i=0;i<NPOS;i++) if(predict(&EXS[POS[i]])) tp++;
    for(int i=0;i<NNEG;i++) if(!predict(&EXS[NEG[i]])) tn++;
    return (double)(tp+tn)/(NPOS+NNEG);
}
/* ============================================================
   MAIN
   ============================================================ */
int main(void){
    mk_examples();
    printf("=== L0 binary: 4-bit universe, odd-parity target ===\n");
    printf("    %d pos / %d neg\n",NPOS,NNEG);
    printf("=== L1 logic self-test ===\n");
    initKB();
    { Term q[2]={mkc("1"),mkc("2")};
      printf("    entails succ(1,2) = %d\n",prove("succ",q,2,NULL,0,8));
      Term q2[2]={mkc("1"),mkc("9")};
      printf("    entails succ(1,9) = %d\n",prove("succ",q2,2,NULL,0,8)); }
    { /* unify X,1 with 0,Y */
      Term a[2]={mkv("X"),mkc("1")}, b[2]={mkc("0"),mkv("Y")};
      Bind out[8]; int no;
      printf("    unify(X,1;0,Y) = %d\n",unify(a,2,b,2,NULL,0,out,&no)); }
    printf("=== L2 FOIL (general, gain-guided) ===\n");
    foil_run();
    for(int c=0;c<NCLS;c++){
        printf("    target(E) :-");
        for(int l=0;l<CLN[c];l++){
            Lit*x=&CLS[c][l];
            if(x->kind==0)      printf(" b%d=%d",x->i,x->v);
            else if(x->kind==1) printf(" b%d&b%d=%d",x->i,x->j,x->v);
            else if(x->kind==2) printf(" b%d>=%d",x->i,x->v);
            else                printf(" b%d^b%d=%d",x->i,x->j,x->v);
        }
        printf("\n");
    }
    printf("=== L3b ILASP-lite: constraints + simplify ===\n");
    int pruned=ilasp_phase();
    printf("    pruned %d clause(s)\n",pruned);
    printf("=== L3 METAGOL: MIL with invention ===\n");
    mil_report();
    printf("=== L4 tree ===\n");
    print_tree();
    printf("=== training accuracy: %.3f ===\n",accuracy());
    return 0;
}
