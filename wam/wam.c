/* SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 */
/* Copyright Ahmad Ali Parr */

/*
 * wam.c -- a Warren Abstract Machine you feed with tokens
 *
 * Etymology: "WAM" is David H. D. Warren's 1983 abstract machine for Prolog;
 * "abstract" because no silicon ever implemented it, it is a design that
 * compilers target. This file follows Hassan Ait-Kaci's tutorial
 * reconstruction: heap, argument/temporary registers, environment stack with
 * permanent variables, trail, choice points, read/write unification mode.
 * "Token" is the old English tacen, a sign: the engine reads signs, one
 * whitespace-separated word at a time, and does what they say.
 *
 * Usage:
 *   ./wam [-all] [-trace] [file | -]
 *   ./wam program.tok          run a token file
 *   ./wam < program.tok        same, from stdin
 *   producer | ./wam           keep sending tokens; send ";" for the next answer
 *   -all                       print every answer of every query
 *   -trace                     print each executed instruction and its effect
 * The token grammar is in docs/wam.md.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>
#include <setjmp.h>
#include <errno.h>

/* ── Sizes ─────────────────────────────────────────────────────────────── */

#define HEAP_MAX   (1 << 21)
#define STACK_MAX  (1 << 21)
#define TRAIL_MAX  (1 << 21)
#define PDL_MAX    (1 << 16)
#define STACK_BASE HEAP_MAX           /* stack addresses sit above the heap */
#define BOTTOM     STACK_BASE         /* the sentinel choice point          */
#define MAXX       1024               /* X1..X1024                          */
#define MAXY       4096               /* Y1..Y4096                          */
#define TOKMAX     4096
#define CODE_MAX   (1 << 20)
#define NAMES_MAX  64

/* ── Cells ─────────────────────────────────────────────────────────────── */

enum { REF, STR, CON, LIS, FUN, INT, FLT };

typedef struct { int tag; int64_t val; } Cell;

static Cell M[HEAP_MAX + STACK_MAX];  /* heap [0,HEAP_MAX), stack above     */
static Cell X[MAXX + 1];              /* argument / temporary registers     */
static int64_t TRAIL[TRAIL_MAX];

static Cell mk(int tag, int64_t v) { Cell c; c.tag = tag; c.val = v; return c; }
static int ceq(Cell a, Cell b) { return a.tag == b.tag && a.val == b.val; }

static Cell mk_flt(double d)
{
    int64_t v;
    memcpy(&v, &d, sizeof v);
    return mk(FLT, v);
}
static double flt_of(Cell c)
{
    double d;
    memcpy(&d, &c.val, sizeof d);
    return d;
}

/* ── Atoms and functors ────────────────────────────────────────────────── */

static char **atom_name;
static int natoms, atom_cap;
#define HASHN 16384
static int atom_head[HASHN];
static int *atom_next;

static char *xstrdup(const char *s)
{
    size_t n = strlen(s) + 1;
    char *p = malloc(n);
    if (!p) { fprintf(stderr, "wam: out of memory\n"); exit(2); }
    memcpy(p, s, n);
    return p;
}

static unsigned hash_str(const char *s)
{
    unsigned h = 2166136261u;
    while (*s) { h ^= (unsigned char)*s++; h *= 16777619u; }
    return h % HASHN;
}

static int intern(const char *s)
{
    unsigned h = hash_str(s);
    int i;
    for (i = atom_head[h] - 1; i >= 0; i = atom_next[i] - 1)
        if (strcmp(atom_name[i], s) == 0) return i;
    if (natoms == atom_cap) {
        atom_cap = atom_cap ? atom_cap * 2 : 256;
        atom_name = realloc(atom_name, sizeof(char *) * (size_t)atom_cap);
        atom_next = realloc(atom_next, sizeof(int) * (size_t)atom_cap);
        if (!atom_name || !atom_next) { fprintf(stderr, "wam: out of memory\n"); exit(2); }
    }
    atom_name[natoms] = xstrdup(s);
    atom_next[natoms] = atom_head[h];
    atom_head[h] = natoms + 1;
    return natoms++;
}

#define FUN_ATOM(v)  ((int)((v) >> 16))
#define FUN_ARITY(v) ((int)((v) & 0xffff))
static Cell mk_fun(int atom, int arity) { return mk(FUN, ((int64_t)atom << 16) | arity); }

/* ── Machine registers ─────────────────────────────────────────────────── */

enum { READ, WRITE };

static int     P, CP, mode;
static int64_t E, B, B0, H, HB, S, TR;
static int     trail_all;             /* \= needs every binding trailed     */
static int     trace_on;

#define STK_CHECK(n) do { if ((n) >= HEAP_MAX + STACK_MAX) rt_error("stack overflow"); } while (0)

/* ── Instruction set ───────────────────────────────────────────────────── */

enum {
    OP_PUT_VARIABLE, OP_PUT_VALUE, OP_PUT_UNSAFE_VALUE, OP_PUT_CONSTANT,
    OP_PUT_STRUCTURE, OP_PUT_LIST,
    OP_GET_VARIABLE, OP_GET_VALUE, OP_GET_CONSTANT, OP_GET_STRUCTURE, OP_GET_LIST,
    OP_SET_VARIABLE, OP_SET_VALUE, OP_SET_LOCAL_VALUE, OP_SET_CONSTANT, OP_SET_VOID,
    OP_UNIFY_VARIABLE, OP_UNIFY_VALUE, OP_UNIFY_LOCAL_VALUE, OP_UNIFY_CONSTANT,
    OP_UNIFY_VOID,
    OP_ALLOCATE, OP_DEALLOCATE, OP_CALL, OP_EXECUTE, OP_PROCEED,
    OP_TRY_ME_ELSE, OP_RETRY_ME_ELSE, OP_TRUST_ME, OP_TRY, OP_RETRY, OP_TRUST,
    OP_SWITCH_ON_TERM,
    OP_NECK_CUT, OP_GET_LEVEL, OP_CUT,
    OP_FAIL, OP_HALT, OP_BUILTIN
};

/* signature letters: R register  A argument register (X only)  Y permanent
 * register  C constant  F functor name/arity  N integer  L label
 * S label that may be the word "fail" */
typedef struct { const char *name; int op; const char *sig; } OpInfo;

static const OpInfo ops[] = {
    {"put_variable", OP_PUT_VARIABLE, "RA"},
    {"put_value", OP_PUT_VALUE, "RA"},
    {"put_unsafe_value", OP_PUT_UNSAFE_VALUE, "YA"},
    {"put_constant", OP_PUT_CONSTANT, "CA"},
    {"put_structure", OP_PUT_STRUCTURE, "FA"},
    {"put_list", OP_PUT_LIST, "A"},
    {"get_variable", OP_GET_VARIABLE, "RA"},
    {"get_value", OP_GET_VALUE, "RA"},
    {"get_constant", OP_GET_CONSTANT, "CA"},
    {"get_structure", OP_GET_STRUCTURE, "FA"},
    {"get_list", OP_GET_LIST, "A"},
    {"set_variable", OP_SET_VARIABLE, "R"},
    {"set_value", OP_SET_VALUE, "R"},
    {"set_local_value", OP_SET_LOCAL_VALUE, "R"},
    {"set_constant", OP_SET_CONSTANT, "C"},
    {"set_void", OP_SET_VOID, "N"},
    {"unify_variable", OP_UNIFY_VARIABLE, "R"},
    {"unify_value", OP_UNIFY_VALUE, "R"},
    {"unify_local_value", OP_UNIFY_LOCAL_VALUE, "R"},
    {"unify_constant", OP_UNIFY_CONSTANT, "C"},
    {"unify_void", OP_UNIFY_VOID, "N"},
    {"allocate", OP_ALLOCATE, "N"},
    {"deallocate", OP_DEALLOCATE, ""},
    {"call", OP_CALL, "L"},
    {"execute", OP_EXECUTE, "L"},
    {"proceed", OP_PROCEED, ""},
    {"try_me_else", OP_TRY_ME_ELSE, "L"},
    {"retry_me_else", OP_RETRY_ME_ELSE, "L"},
    {"trust_me", OP_TRUST_ME, ""},
    {"try", OP_TRY, "L"},
    {"retry", OP_RETRY, "L"},
    {"trust", OP_TRUST, "L"},
    {"switch_on_term", OP_SWITCH_ON_TERM, "SSSS"},
    {"neck_cut", OP_NECK_CUT, ""},
    {"get_level", OP_GET_LEVEL, "Y"},
    {"cut", OP_CUT, "R"},
    {"fail", OP_FAIL, ""},
    {"halt", OP_HALT, ""},
    {NULL, 0, NULL}
};

typedef struct {
    int op;
    int r1, r2;       /* registers: > 0 is Xn, < 0 is Yn                */
    int a[4];         /* code addresses; -1 means fail                  */
    Cell c;           /* constant or functor                            */
    int n;            /* count, or the arity of the owning predicate    */
    char *text;       /* source tokens, for -trace                      */
} Instr;

static Instr *code;
static int ncode;

/* ── Errors ────────────────────────────────────────────────────────────── */

static jmp_buf rtjmp, loadjmp;

static int rt_failed;
static void rt_error(const char *msg)
{
    rt_failed = 1;
    fflush(stdout);
    fprintf(stderr, "wam: runtime error: %s\n", msg);
    longjmp(rtjmp, 1);
}

/* ── Heap, trail, deref, bind, unify ───────────────────────────────────── */

static void hpush(Cell c)
{
    if (H >= HEAP_MAX) rt_error("heap overflow");
    M[H++] = c;
}

static Cell deref(Cell c)
{
    while (c.tag == REF) {
        Cell d = M[c.val];
        if (d.tag == REF && d.val == c.val) return d;
        c = d;
    }
    return c;
}

static void trail(int64_t a)
{
    if (trail_all || a < HB || (a >= STACK_BASE && a < B)) {
        if (TR >= TRAIL_MAX) rt_error("trail overflow");
        TRAIL[TR++] = a;
    }
}

static void unwind(int64_t to)
{
    while (TR > to) {
        int64_t a = TRAIL[--TR];
        M[a] = mk(REF, a);
    }
}

#define BINDLOG_MAX 64
static int64_t bind_addr[BINDLOG_MAX];
static Cell bind_val[BINDLOG_MAX];
static int nbind;

static void bind(Cell var, Cell val)
{
    M[var.val] = val;
    trail(var.val);
    if (trace_on && nbind < BINDLOG_MAX) { bind_addr[nbind] = var.val; bind_val[nbind++] = val; }
}

static int unify(Cell a, Cell b)
{
    static Cell pdl[PDL_MAX];
    int sp = 0;
    pdl[sp++] = a;
    pdl[sp++] = b;
    while (sp) {
        b = deref(pdl[--sp]);
        a = deref(pdl[--sp]);
        if (ceq(a, b)) continue;
        if (a.tag == REF || b.tag == REF) {
            if (a.tag == REF && b.tag == REF) {
                if (a.val < b.val) bind(b, a); else bind(a, b);   /* younger to older */
            } else if (a.tag == REF) bind(a, b);
            else bind(b, a);
        } else if (a.tag != b.tag) {
            return 0;
        } else if (a.tag == LIS) {
            if (sp + 4 > PDL_MAX) rt_error("unify stack overflow");
            pdl[sp++] = M[a.val];     pdl[sp++] = M[b.val];
            pdl[sp++] = M[a.val + 1]; pdl[sp++] = M[b.val + 1];
        } else if (a.tag == STR) {
            int i, n;
            if (!ceq(M[a.val], M[b.val])) return 0;
            n = FUN_ARITY(M[a.val].val);
            if (sp + 2 * n > PDL_MAX) rt_error("unify stack overflow");
            for (i = 1; i <= n; i++) { pdl[sp++] = M[a.val + i]; pdl[sp++] = M[b.val + i]; }
        } else {
            return 0;                 /* two different constants */
        }
    }
    return 1;
}

static int identical(Cell a, Cell b)
{
    static Cell pdl[PDL_MAX];
    int sp = 0;
    pdl[sp++] = a;
    pdl[sp++] = b;
    while (sp) {
        b = deref(pdl[--sp]);
        a = deref(pdl[--sp]);
        if (ceq(a, b)) continue;
        if (a.tag != b.tag) return 0;
        if (a.tag == LIS) {
            if (sp + 4 > PDL_MAX) rt_error("compare stack overflow");
            pdl[sp++] = M[a.val];     pdl[sp++] = M[b.val];
            pdl[sp++] = M[a.val + 1]; pdl[sp++] = M[b.val + 1];
        } else if (a.tag == STR) {
            int i, n;
            if (!ceq(M[a.val], M[b.val])) return 0;
            n = FUN_ARITY(M[a.val].val);
            if (sp + 2 * n > PDL_MAX) rt_error("compare stack overflow");
            for (i = 1; i <= n; i++) { pdl[sp++] = M[a.val + i]; pdl[sp++] = M[b.val + i]; }
        } else {
            return 0;
        }
    }
    return 1;
}

/* ── Writing terms ─────────────────────────────────────────────────────── */

static int symbol_char(int c) { return c && strchr("#$&*+-./:<=>?@^~\\", c) != NULL; }

static int atom_is_plain(const char *s)
{
    const char *p;
    if (!*s) return 0;
    if (!strcmp(s, "[]") || !strcmp(s, "!") || !strcmp(s, ";") || !strcmp(s, "{}")) return 1;
    if (islower((unsigned char)*s)) {
        for (p = s; *p; p++)
            if (!isalnum((unsigned char)*p) && *p != '_' && !((unsigned char)*p & 0x80)) return 0;
        return 1;
    }
    for (p = s; *p; p++) if (!symbol_char((unsigned char)*p)) return 0;
    return 1;
}

static void put_atom(FILE *f, const char *s)
{
    if (atom_is_plain(s)) { fputs(s, f); return; }
    fputc('\'', f);
    for (; *s; s++) {
        if (*s == '\'') fputs("\\'", f);
        else if (*s == '\\') fputs("\\\\", f);
        else if (*s == '\n') fputs("\\n", f);
        else if (*s == '\t') fputs("\\t", f);
        else fputc(*s, f);
    }
    fputc('\'', f);
}

static void put_float(FILE *f, double d)
{
    char buf[64], out[96];
    char *e, *q;
    int i, j = 0;
    snprintf(buf, sizeof buf, "%.15g", d);
    if (strtod(buf, NULL) != d) snprintf(buf, sizeof buf, "%.17g", d);
    e = strchr(buf, 'e');
    q = strchr(buf, '.');
    if (!q && !e && !strstr(buf, "inf") && !strstr(buf, "nan")) strcat(buf, ".0");
    else if (!q && e) {
        memmove(e + 2, e, strlen(e) + 1);
        e[0] = '.'; e[1] = '0';
    }
    for (i = 0; buf[i]; i++) {                 /* e+010 -> e+10, e-05 -> e-5 */
        if (buf[i] == 'e') {
            out[j++] = 'e';
            i++;
            if (buf[i] == '+') out[j++] = buf[i++];
            else if (buf[i] == '-') out[j++] = buf[i++];
            while (buf[i] == '0' && buf[i + 1]) i++;
            i--;
        } else out[j++] = buf[i];
    }
    out[j] = 0;
    fputs(out, f);
}

static struct { char name[256]; int y; } qnames[NAMES_MAX];   /* name V Yk lines */
static int nqnames;
static int64_t named_root[NAMES_MAX];
static int naming;

static void put_var(FILE *f, int64_t a)
{
    if (naming) {
        int i;
        for (i = 0; i < nqnames; i++)
            if (named_root[i] == a) { fputs(qnames[i].name, f); return; }
        fputc('_', f);
        return;
    }
    if (a >= STACK_BASE) fprintf(f, "_L%lld", (long long)(a - STACK_BASE));
    else fprintf(f, "_G%lld", (long long)a);
}

static void put_term(FILE *f, Cell c, int depth)
{
    c = deref(c);
    if (depth > 400) { fputs("...", f); return; }
    switch (c.tag) {
    case REF: put_var(f, c.val); break;
    case CON: put_atom(f, atom_name[c.val]); break;
    case INT: fprintf(f, "%lld", (long long)c.val); break;
    case FLT: put_float(f, flt_of(c)); break;
    case FUN: put_atom(f, atom_name[FUN_ATOM(c.val)]); fprintf(f, "/%d", FUN_ARITY(c.val)); break;
    case LIS: {
        long count = 0;
        fputc('[', f);
        for (;;) {
            Cell t;
            put_term(f, M[c.val], depth + 1);
            t = deref(M[c.val + 1]);
            if (t.tag == LIS) {
                if (++count > 1000000) { fputs(",...", f); break; }
                fputc(',', f); c = t; continue;
            }
            if (!(t.tag == CON && !strcmp(atom_name[t.val], "[]"))) {
                fputc('|', f);
                put_term(f, t, depth + 1);
            }
            break;
        }
        fputc(']', f);
        break; }
    case STR: {
        int i, n = FUN_ARITY(M[c.val].val);
        put_atom(f, atom_name[FUN_ATOM(M[c.val].val)]);
        fputc('(', f);
        for (i = 1; i <= n; i++) {
            if (i > 1) fputc(',', f);
            put_term(f, M[c.val + i], depth + 1);
        }
        fputc(')', f);
        break; }
    default: fputs("?", f);
    }
}

static void put_cell(FILE *f, Cell c)       /* raw cell, for -trace */
{
    switch (c.tag) {
    case REF: fputs("REF ", f); put_var(f, c.val); break;
    case STR: fprintf(f, "STR h%lld", (long long)c.val); break;
    case LIS: fprintf(f, "LIS h%lld", (long long)c.val); break;
    case CON: fputs("CON ", f); put_atom(f, atom_name[c.val]); break;
    case INT: fprintf(f, "INT %lld", (long long)c.val); break;
    case FLT: fputs("FLT ", f); put_float(f, flt_of(c)); break;
    case FUN: fputs("FUN ", f); put_term(f, c, 0); break;
    default: fputs("?", f);
    }
}

/* ── Registers ─────────────────────────────────────────────────────────── */

static Cell *reg(int r)
{
    if (r > 0) return &X[r];
    if (-r > M[E + 2].val) rt_error("permanent variable used outside an environment that holds it");
    return &M[E + 2 + (-r)];
}

/* ── Stack: environments and choice points ─────────────────────────────── */
/*
 * environment at e:   [e] CE  [e+1] CP  [e+2] N   [e+2+i] Yi
 * choice point at b:  [b] n  [b+1..b+n] A1..An  [b+n+1] CE  [b+n+2] CP
 *                     [b+n+3] previous B  [b+n+4] next clause  [b+n+5] TR
 *                     [b+n+6] H
 */

static int64_t stack_top(void)
{
    if (E > B) return E + 3 + M[E + 2].val;
    return B + M[B].val + 7;
}

static void reset_hb(void) { HB = M[B + M[B].val + 6].val; }

static void push_choice(int n, int bp)
{
    int64_t nb = stack_top();
    int i;
    STK_CHECK(nb + n + 7);
    M[nb] = mk(INT, n);
    for (i = 1; i <= n; i++) M[nb + i] = X[i];
    M[nb + n + 1] = mk(INT, E);
    M[nb + n + 2] = mk(INT, CP);
    M[nb + n + 3] = mk(INT, B);
    M[nb + n + 4] = mk(INT, bp);
    M[nb + n + 5] = mk(INT, TR);
    M[nb + n + 6] = mk(INT, H);
    B = nb;
    HB = H;
}

static void restore_choice(void)
{
    int n = (int)M[B].val, i;
    for (i = 1; i <= n; i++) X[i] = M[B + i];
    E = M[B + n + 1].val;
    CP = (int)M[B + n + 2].val;
    unwind(M[B + n + 5].val);
    H = M[B + n + 6].val;
    HB = H;
    B0 = M[B + n + 3].val;
}

static void pop_choice(void)
{
    B = M[B + M[B].val + 3].val;
    reset_hb();
    B0 = B;
}

/* ── Loader: tokens ────────────────────────────────────────────────────── */

typedef struct { char text[TOKMAX]; int line, col, tokno; } Token;

static FILE *src;
static const char *srcname = "stdin";
static int cur_line = 1, cur_col = 0, line_tokno = 0, last_c = '\n';
static int repl_mode;                    /* errors skip a line instead of ending */
static Token tok, pk;
static int has_pk;

static int nextc(void)
{
    int c = getc(src);
    last_c = c;
    if (c == '\n') { cur_line++; cur_col = 0; line_tokno = 0; }
    else if (c != EOF) cur_col++;
    return c;
}

static void load_error(const Token *t, const char *fmt, ...);

#include <stdarg.h>
static void load_error(const Token *t, const char *fmt, ...)
{
    va_list ap;
    fflush(stdout);
    if (t) fprintf(stderr, "%s:%d:%d: token %d '%s': ", srcname, t->line, t->col, t->tokno, t->text);
    else fprintf(stderr, "%s:%d: ", srcname, cur_line);
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    longjmp(loadjmp, 1);
}

/* reads one token; 0 at end of input */
static int read_token(Token *t)
{
    int c, n = 0;
    for (;;) {
        c = nextc();
        if (c == EOF) return 0;
        if (c == '%') { while (c != '\n' && c != EOF) c = nextc(); if (c == EOF) return 0; continue; }
        if (!isspace(c)) break;
    }
    t->line = cur_line; t->col = cur_col; t->tokno = ++line_tokno;
    t->text[n++] = (char)c;
    if (c == '\'') {                               /* quoted atom, may hold spaces */
        for (;;) {
            c = nextc();
            if (c == EOF || c == '\n') { t->text[n] = 0; load_error(t, "unterminated quoted atom"); }
            if (n >= TOKMAX - 4) { t->text[n] = 0; load_error(t, "token too long"); }
            t->text[n++] = (char)c;
            if (c == '\\') {
                c = nextc();
                if (c == EOF || c == '\n') { t->text[n] = 0; load_error(t, "unterminated quoted atom"); }
                t->text[n++] = (char)c;
            } else if (c == '\'') {
                int d = nextc();
                if (d == '\'') { t->text[n++] = '\''; continue; }
                if (d == EOF || isspace(d)) { t->text[n] = 0; return 1; }
                t->text[n++] = (char)d;            /* "/2" or ":" glued to the name */
                break;
            }
        }
    }
    for (;;) {                                      /* rest of the word */
        c = nextc();
        if (c == EOF || isspace(c)) break;
        if (n >= TOKMAX - 2) { t->text[n] = 0; load_error(t, "token too long"); }
        t->text[n++] = (char)c;
    }
    t->text[n] = 0;
    return 1;
}

static int next_token(Token *t)
{
    if (has_pk) { *t = pk; has_pk = 0; return 1; }
    return read_token(t);
}

static int peek_token(void)
{
    if (!has_pk) { if (!read_token(&pk)) return 0; has_pk = 1; }
    return 1;
}

/* ── Loader: names and operands ────────────────────────────────────────── */

/* Scans a quoted atom at s[0]=='\''. Decodes into out. Returns the index just
 * past the closing quote, or -1 if malformed. */
static int scan_quoted(const char *s, char *out, size_t cap)
{
    int i = 1;
    size_t n = 0;
    while (s[i]) {
        if (n + 2 >= cap) return -1;
        if (s[i] == '\'') {
            if (s[i + 1] == '\'') { out[n++] = '\''; i += 2; continue; }
            out[n] = 0;
            return i + 1;
        }
        if (s[i] == '\\') {
            i++;
            switch (s[i]) {
            case '\\': out[n++] = '\\'; break;
            case '\'': out[n++] = '\''; break;
            case 'n': out[n++] = '\n'; break;
            case 't': out[n++] = '\t'; break;
            case 'x': {
                int v = 0, k = 0;
                i++;
                while (isxdigit((unsigned char)s[i])) {
                    v = v * 16 + (isdigit((unsigned char)s[i]) ? s[i] - '0' : (tolower((unsigned char)s[i]) - 'a' + 10));
                    i++; k++;
                }
                if (k == 0 || s[i] != '\\' || v > 255 || v == 0) return -1;
                out[n++] = (char)v;
                break; }
            default: return -1;
            }
            i++;
            continue;
        }
        out[n++] = s[i++];
    }
    return -1;                                      /* ran off the end */
}

static int all_digits(const char *s)
{
    if (!*s) return 0;
    for (; *s; s++) if (!isdigit((unsigned char)*s)) return 0;
    return 1;
}

/* Splits "name/arity" (name possibly quoted). 0 if the token has that shape. */
static int split_functor(const char *raw, char *name, size_t cap, long *arity)
{
    const char *rest;
    if (raw[0] == '\'') {
        int e = scan_quoted(raw, name, cap);
        if (e < 0 || raw[e] != '/') return 0;
        rest = raw + e + 1;
    } else {
        const char *p = strrchr(raw, '/');
        if (!p || p == raw || (size_t)(p - raw) >= cap) return 0;
        memcpy(name, raw, (size_t)(p - raw));
        name[p - raw] = 0;
        rest = p + 1;
    }
    if (!all_digits(rest) || strlen(rest) > 6) return 0;
    *arity = strtol(rest, NULL, 10);
    return *arity <= 65535;
}

/* Canonical label key; returns 1 and sets *arity if it is name/arity. */
static int canon_label(const char *raw, char *key, size_t cap, long *arity)
{
    char name[TOKMAX];
    if (split_functor(raw, name, sizeof name, arity)) {
        snprintf(key, cap, "%s/%ld", name, *arity);
        return 1;
    }
    snprintf(key, cap, "%s", raw);
    return 0;
}

static int parse_reg(const Token *t, const char *s, int want_y, int want_x)
{
    char k = s[0];
    long n;
    if ((k != 'X' && k != 'A' && k != 'Y') || !all_digits(s + 1) || strlen(s + 1) > 5)
        load_error(t, "expected a register (X1.. or Y1..)");
    n = strtol(s + 1, NULL, 10);
    if (k == 'Y') {
        if (!want_y) load_error(t, "expected an argument register X1.., not a permanent one");
        if (n < 1 || n > MAXY) load_error(t, "permanent register out of range 1..%d", MAXY);
        return -(int)n;
    }
    if (!want_x) load_error(t, "expected a permanent register Y1..");
    if (n < 1 || n > MAXX) load_error(t, "register out of range 1..%d", MAXX);
    return (int)n;
}

static int is_numeric_start(const char *s)
{
    if (isdigit((unsigned char)*s)) return 1;
    return (*s == '-' || *s == '+') && isdigit((unsigned char)s[1]);
}

static Cell parse_const(const Token *t, const char *s)
{
    char buf[TOKMAX];
    if (s[0] == '\'') {
        int e = scan_quoted(s, buf, sizeof buf);
        if (e < 0 || s[e] != 0) load_error(t, "malformed quoted atom");
        return mk(CON, intern(buf));
    }
    if (is_numeric_start(s)) {
        char *end;
        const char *p = s + (*s == '-' || *s == '+');
        if (all_digits(p)) {
            long long v;
            errno = 0;
            v = strtoll(s, &end, 10);
            if (errno || *end) load_error(t, "integer out of range");
            return mk(INT, v);
        } else {
            double d;
            const char *q = p;
            int ok = 1;
            while (isdigit((unsigned char)*q)) q++;
            if (*q == '.') { q++; if (!isdigit((unsigned char)*q)) ok = 0; while (isdigit((unsigned char)*q)) q++; }
            if (ok && (*q == 'e' || *q == 'E')) {
                q++;
                if (*q == '-' || *q == '+') q++;
                if (!isdigit((unsigned char)*q)) ok = 0;
                while (isdigit((unsigned char)*q)) q++;
            }
            if (!ok || *q) load_error(t, "malformed number");
            errno = 0;
            d = strtod(s, &end);
            if (errno || *end) load_error(t, "number out of range");
            return mk_flt(d);
        }
    }
    return mk(CON, intern(s));
}

static Cell parse_functor(const Token *t, const char *s)
{
    char name[TOKMAX];
    long ar;
    if (!split_functor(s, name, sizeof name, &ar))
        load_error(t, "expected a functor name/arity with arity 1..65535");
    if (ar < 1) load_error(t, "structure arity must be at least 1");
    return mk_fun(intern(name), (int)ar);
}

/* ── Loader: labels and code ───────────────────────────────────────────── */

typedef struct { char *key; int addr; } Label;
static Label *labels;
static int nlabels, labels_cap;

typedef struct { int ins, slot; char *key; Token t; } Fixup;
static Fixup *fix;
static int nfix, fix_cap;

static int user_code;                       /* first address after the built-in stubs */
static int cur_arity = -1;                 /* arity of the predicate being loaded */

static int find_label(const char *key)
{
    int i;
    for (i = 0; i < nlabels; i++) if (!strcmp(labels[i].key, key)) return labels[i].addr;
    return -2;
}

static void add_label(const char *key, int addr)
{
    if (nlabels == labels_cap) {
        labels_cap = labels_cap ? labels_cap * 2 : 128;
        labels = realloc(labels, sizeof(Label) * (size_t)labels_cap);
        if (!labels) { fprintf(stderr, "wam: out of memory\n"); exit(2); }
    }
    labels[nlabels].key = xstrdup(key);
    labels[nlabels].addr = addr;
    nlabels++;
}

static int emit_instr(Instr in)
{
    if (ncode >= CODE_MAX) { fprintf(stderr, "wam: code area full\n"); exit(2); }
    if (!code) {
        code = malloc(sizeof(Instr) * CODE_MAX);
        if (!code) { fprintf(stderr, "wam: out of memory\n"); exit(2); }
    }
    code[ncode] = in;
    return ncode++;
}

static void add_fixup(int ins, int slot, const char *key, const Token *t)
{
    if (nfix == fix_cap) {
        fix_cap = fix_cap ? fix_cap * 2 : 128;
        fix = realloc(fix, sizeof(Fixup) * (size_t)fix_cap);
        if (!fix) { fprintf(stderr, "wam: out of memory\n"); exit(2); }
    }
    fix[nfix].ins = ins; fix[nfix].slot = slot; fix[nfix].key = xstrdup(key); fix[nfix].t = *t;
    nfix++;
}

/* resolve what can be resolved; report the first label still missing */
static int link_failed;
static int link_code(void)
{
    int i, j = 0, bad = -1;
    for (i = 0; i < nfix; i++) {
        int a = find_label(fix[i].key);
        if (a == -2) { if (bad < 0) bad = j; fix[j++] = fix[i]; }
        else { code[fix[i].ins].a[fix[i].slot] = a; free(fix[i].key); }
    }
    nfix = j;
    if (bad >= 0) {
        fflush(stdout);
        fprintf(stderr, "%s:%d:%d: token %d '%s': undefined label '%s'\n", srcname,
                fix[bad].t.line, fix[bad].t.col, fix[bad].t.tokno, fix[bad].t.text, fix[bad].key);
        link_failed = 1;
        nfix = 0;
        return 0;
    }
    return 1;
}

/* built-ins live in code as "BUILTIN id; proceed" stubs behind ordinary labels */
enum { BI_EQ, BI_NEQ, BI_EQEQ, BI_NEQEQ, BI_VAR, BI_NONVAR, BI_ATOM, BI_ATOMIC, BI_INTEGER };

static void install_builtins(void)
{
    static const struct { const char *key; int id; } bi[] = {
        {"=/2", BI_EQ}, {"\\=/2", BI_NEQ}, {"==/2", BI_EQEQ}, {"\\==/2", BI_NEQEQ},
        {"var/1", BI_VAR}, {"nonvar/1", BI_NONVAR}, {"atom/1", BI_ATOM},
        {"atomic/1", BI_ATOMIC}, {"integer/1", BI_INTEGER}, {NULL, 0}
    };
    int i;
    for (i = 0; bi[i].key; i++) {
        Instr in;
        memset(&in, 0, sizeof in);
        in.op = OP_BUILTIN; in.n = bi[i].id; in.text = xstrdup(bi[i].key);
        add_label(bi[i].key, emit_instr(in));
        memset(&in, 0, sizeof in);
        in.op = OP_PROCEED; in.text = xstrdup("proceed");
        emit_instr(in);
    }
}

/* ── Loader: queries ───────────────────────────────────────────────────── */

static int in_query, query_start;

static void define_label(const Token *t)
{
    char raw[TOKMAX], key[TOKMAX * 2];
    long ar = 0;
    size_t len = strlen(t->text);
    memcpy(raw, t->text, len - 1);
    raw[len - 1] = 0;
    if (!raw[0]) load_error(t, "empty label");
    if (!strchr(raw, '/')) load_error(t, "a label looks like name/arity:");
    if (canon_label(raw, key, sizeof key, &ar)) cur_arity = (int)ar;
    if (find_label(key) != -2) load_error(t, "label '%s' is already defined", key);
    add_label(key, ncode);
}

static void statement(const Token *t)
{
    const OpInfo *oi;
    Instr in;
    char text[TOKMAX * 2];
    Token a;
    const char *sg;
    int nreg = 0, naddr = 0, idx, i;
    size_t len = strlen(t->text);

    if (len > 1 && t->text[len - 1] == ':') { define_label(t); return; }
    if (!strcmp(t->text, ";")) load_error(t, "';' with no query waiting for another answer");
    if (!strcmp(t->text, "query")) {
        if (in_query) load_error(t, "'query' inside a query that has no 'halt' yet");
        in_query = 1; query_start = ncode; nqnames = 0;
        return;
    }
    if (!strcmp(t->text, "name")) {
        Token n1, n2;
        char buf[TOKMAX];
        if (!in_query) load_error(t, "'name' outside a query");
        if (!next_token(&n1)) load_error(t, "end of input after 'name' (expected: name VarName Yn)");
        if (!next_token(&n2)) load_error(&n1, "end of input after variable name (expected a Y register)");
        if (nqnames >= NAMES_MAX) load_error(&n1, "too many named query variables");
        if (n1.text[0] == '\'') {
            int e = scan_quoted(n1.text, buf, sizeof buf);
            if (e < 0 || n1.text[e]) load_error(&n1, "malformed quoted name");
        } else snprintf(buf, sizeof buf, "%s", n1.text);
        snprintf(qnames[nqnames].name, sizeof qnames[nqnames].name, "%.255s", buf);
        qnames[nqnames].y = -parse_reg(&n2, n2.text, 1, 0);
        nqnames++;
        return;
    }
    for (oi = ops; oi->name; oi++) if (!strcmp(oi->name, t->text)) break;
    if (!oi->name) load_error(t, "unknown instruction, label or directive");

    memset(&in, 0, sizeof in);
    in.op = oi->op;
    snprintf(text, sizeof text, "%s", t->text);
    for (sg = oi->sig; *sg; sg++) {
        if (!next_token(&a)) load_error(t, "end of input: '%s' needs more operands", oi->name);
        if (strlen(text) + strlen(a.text) + 2 < sizeof text) { strcat(text, " "); strcat(text, a.text); }
        switch (*sg) {
        case 'R': case 'A': case 'Y': {
            int r = parse_reg(&a, a.text, *sg != 'A', *sg != 'Y');
            if (nreg++ == 0) in.r1 = r; else in.r2 = r;
            break; }
        case 'C': in.c = parse_const(&a, a.text); break;
        case 'F': in.c = parse_functor(&a, a.text); break;
        case 'N': {
            long v;
            if (!all_digits(a.text) || strlen(a.text) > 6) load_error(&a, "expected a non-negative integer");
            v = strtol(a.text, NULL, 10);
            if (!strcmp(oi->name, "allocate") && v > MAXY) load_error(&a, "too many permanent variables (max %d)", MAXY);
            in.n = (int)v;
            break; }
        case 'L': case 'S': {
            char key[TOKMAX * 2];
            long ar;
            if (*sg == 'S' && !strcmp(a.text, "fail")) { in.a[naddr++] = -1; break; }
            if (!a.text[0]) load_error(&a, "empty label");
            canon_label(a.text, key, sizeof key, &ar);
            in.a[naddr] = -2;
            add_fixup(-1 - naddr, naddr, key, &a);     /* instruction index patched below */
            naddr++;
            break; }
        default: break;
        }
    }
    if (oi->op == OP_TRY_ME_ELSE || oi->op == OP_RETRY_ME_ELSE || oi->op == OP_TRY ||
        oi->op == OP_RETRY || oi->op == OP_TRUST) {
        if (cur_arity < 0) load_error(t, "'%s' before any name/arity: label", oi->name);
        in.n = cur_arity;
    }
    in.text = xstrdup(text);
    idx = emit_instr(in);
    for (i = nfix - 1; i >= 0 && fix[i].ins < 0; i--) fix[i].ins = idx;
}

/* ── Execution ─────────────────────────────────────────────────────────── */

static int builtin(int id)
{
    Cell a = deref(X[1]), b = deref(X[2]);
    switch (id) {
    case BI_EQ: return unify(X[1], X[2]);
    case BI_NEQ: {
        int64_t save = TR;
        int r;
        trail_all = 1;
        r = unify(X[1], X[2]);
        trail_all = 0;
        unwind(save);
        return !r; }
    case BI_EQEQ: return identical(X[1], X[2]);
    case BI_NEQEQ: return !identical(X[1], X[2]);
    case BI_VAR: return a.tag == REF;
    case BI_NONVAR: return a.tag != REF;
    case BI_ATOM: return a.tag == CON;
    case BI_ATOMIC: return a.tag == CON || a.tag == INT || a.tag == FLT;
    case BI_INTEGER: return a.tag == INT;
    }
    (void)b;
    return 0;
}

static void start_machine(int pc)
{
    H = 0; TR = 0; HB = 0; S = 0; mode = READ;
    B = BOTTOM;
    M[B] = mk(INT, 0);
    M[B + 1] = mk(INT, -1);          /* CE */
    M[B + 2] = mk(INT, 0);           /* CP */
    M[B + 3] = mk(INT, B);           /* previous B */
    M[B + 4] = mk(INT, -1);          /* BP */
    M[B + 5] = mk(INT, 0);           /* TR */
    M[B + 6] = mk(INT, 0);           /* H  */
    E = -1; CP = 0; B0 = B; P = pc;
}

static void trace_pre(const Instr *in, int pc)
{
    int i;
    for (i = 0; i < nlabels; i++)
        if (pc >= user_code && labels[i].addr == pc) printf("%s:\n", labels[i].key);
    printf("%5d  %s\n", pc, in->text ? in->text : "?");
}

static void trace_regs(const Instr *in, const char *sg)
{
    int k = 0, r;
    for (; *sg; sg++) {
        if (*sg == 'R' || *sg == 'A' || *sg == 'Y') {
            r = k++ ? in->r2 : in->r1;
            if (r > 0) printf("  X%d=", r); else printf("  Y%d=", -r);
            put_cell(stdout, *reg(r));
            if (mode == READ) { Cell d = deref(*reg(r)); if (d.tag == STR || d.tag == LIS || (d.tag == REF && r > 0)) { printf(" ~ "); put_term(stdout, d, 0); } }
        }
    }
}

static void trace_post(const Instr *in, int64_t h0)
{
    int64_t a;
    int i;
    const OpInfo *oi;
    printf("       H=%lld S=%lld mode=%s E=%lld B=%lld TR=%lld CP=%d",
           (long long)H, (long long)S, mode == READ ? "read" : "write",
           (long long)(E < 0 ? -1 : E - STACK_BASE), (long long)(B - STACK_BASE), (long long)TR, CP);
    for (oi = ops; oi->name; oi++) if (oi->op == in->op) { trace_regs(in, oi->sig); break; }
    printf("\n");
    for (i = 0; i < nbind; i++) {
        printf("       bind ");
        if (bind_addr[i] >= STACK_BASE) printf("s%lld", (long long)(bind_addr[i] - STACK_BASE));
        else printf("h%lld", (long long)bind_addr[i]);
        printf(" := ");
        put_cell(stdout, bind_val[i]);
        printf("\n");
    }
    nbind = 0;
    for (a = h0; a < H; a++) {
        printf("       h%lld = ", (long long)a);
        put_cell(stdout, M[a]);
        printf("\n");
    }
}

/* runs until halt (returns 1) or until the last choice point fails (returns 0) */
static int run(int resume)
{
    int failing = resume;
    for (;;) {
        Instr *in;
        int64_t h0;
        if (failing) goto failed;
        in = &code[P];
        h0 = H;
        if (trace_on) trace_pre(in, P);
        switch (in->op) {
        case OP_PUT_VARIABLE:
            if (in->r1 > 0) {
                M[H] = mk(REF, H);
                X[in->r1] = X[in->r2] = M[H];
                if (H >= HEAP_MAX) rt_error("heap overflow");
                H++;
            } else {
                int64_t a = E + 2 + (-in->r1);
                M[a] = mk(REF, a);
                X[in->r2] = M[a];
            }
            P++; break;
        case OP_PUT_VALUE: X[in->r2] = *reg(in->r1); P++; break;
        case OP_PUT_UNSAFE_VALUE: {
            Cell c = deref(*reg(in->r1));
            if (c.tag == REF && c.val >= E && c.val >= STACK_BASE) {
                M[H] = mk(REF, H);
                bind(c, M[H]);
                X[in->r2] = M[H];
                if (H >= HEAP_MAX) rt_error("heap overflow");
                H++;
            } else X[in->r2] = c;
            P++; break; }
        case OP_PUT_CONSTANT: X[in->r1] = in->c; P++; break;
        case OP_PUT_STRUCTURE:
            X[in->r1] = mk(STR, H);
            hpush(in->c);
            mode = WRITE;
            P++; break;
        case OP_PUT_LIST: X[in->r1] = mk(LIS, H); mode = WRITE; P++; break;

        case OP_GET_VARIABLE: *reg(in->r1) = X[in->r2]; P++; break;
        case OP_GET_VALUE:
            if (!unify(*reg(in->r1), X[in->r2])) goto failed;
            P++; break;
        case OP_GET_CONSTANT: {
            Cell c = deref(X[in->r1]);
            if (c.tag == REF) bind(c, in->c);
            else if (!ceq(c, in->c)) goto failed;
            P++; break; }
        case OP_GET_STRUCTURE: {
            Cell c = deref(X[in->r1]);
            if (c.tag == REF) {
                int64_t fa = H;
                hpush(in->c);
                bind(c, mk(STR, fa));
                mode = WRITE;
            } else if (c.tag == STR && ceq(M[c.val], in->c)) {
                S = c.val + 1; mode = READ;
            } else goto failed;
            P++; break; }
        case OP_GET_LIST: {
            Cell c = deref(X[in->r1]);
            if (c.tag == REF) { bind(c, mk(LIS, H)); mode = WRITE; }
            else if (c.tag == LIS) { S = c.val; mode = READ; }
            else goto failed;
            P++; break; }

        case OP_SET_VARIABLE:
        case OP_UNIFY_VARIABLE:
            if (in->op == OP_UNIFY_VARIABLE && mode == READ) { *reg(in->r1) = M[S]; S++; }
            else {
                M[H] = mk(REF, H);
                *reg(in->r1) = M[H];
                if (H >= HEAP_MAX) rt_error("heap overflow");
                H++;
            }
            P++; break;
        case OP_SET_VALUE:
            hpush(*reg(in->r1));
            P++; break;
        case OP_UNIFY_VALUE:
            if (mode == READ) { if (!unify(*reg(in->r1), M[S])) goto failed; S++; }
            else hpush(*reg(in->r1));
            P++; break;
        case OP_SET_LOCAL_VALUE:
        case OP_UNIFY_LOCAL_VALUE:
            if (in->op == OP_UNIFY_LOCAL_VALUE && mode == READ) {
                if (!unify(*reg(in->r1), M[S])) goto failed;
                S++;
            } else {
                Cell c = deref(*reg(in->r1));
                if (c.tag == REF && c.val >= STACK_BASE) {
                    M[H] = mk(REF, H);
                    bind(c, M[H]);
                    if (H >= HEAP_MAX) rt_error("heap overflow");
                    H++;
                } else hpush(c);
            }
            P++; break;
        case OP_SET_CONSTANT: hpush(in->c); P++; break;
        case OP_UNIFY_CONSTANT:
            if (mode == READ) {
                Cell c = deref(M[S]);
                if (c.tag == REF) bind(c, in->c);
                else if (!ceq(c, in->c)) goto failed;
                S++;
            } else hpush(in->c);
            P++; break;
        case OP_SET_VOID:
        case OP_UNIFY_VOID:
            if (in->op == OP_UNIFY_VOID && mode == READ) S += in->n;
            else {
                int i;
                for (i = 0; i < in->n; i++) { hpush(mk(REF, H)); }
            }
            P++; break;

        case OP_ALLOCATE: {
            int64_t ne = stack_top();
            int i;
            STK_CHECK(ne + 3 + in->n);
            M[ne] = mk(INT, E);
            M[ne + 1] = mk(INT, CP);
            M[ne + 2] = mk(INT, in->n);
            for (i = 1; i <= in->n; i++) M[ne + 2 + i] = mk(INT, 0);
            E = ne;
            P++; break; }
        case OP_DEALLOCATE:
            CP = (int)M[E + 1].val;
            E = M[E].val;
            P++; break;
        case OP_CALL: CP = P + 1; B0 = B; P = in->a[0]; break;
        case OP_EXECUTE: B0 = B; P = in->a[0]; break;
        case OP_PROCEED: P = CP; break;

        case OP_TRY_ME_ELSE: push_choice(in->n, in->a[0]); P++; break;
        case OP_RETRY_ME_ELSE:
            restore_choice();
            M[B + M[B].val + 4] = mk(INT, in->a[0]);
            P++; break;
        case OP_TRUST_ME: restore_choice(); pop_choice(); P++; break;
        case OP_TRY: push_choice(in->n, P + 1); P = in->a[0]; break;
        case OP_RETRY:
            restore_choice();
            M[B + M[B].val + 4] = mk(INT, P + 1);
            P = in->a[0];
            break;
        case OP_TRUST: restore_choice(); pop_choice(); P = in->a[0]; break;

        case OP_SWITCH_ON_TERM: {
            Cell c = deref(X[1]);
            int t = c.tag == REF ? in->a[0]
                  : (c.tag == CON || c.tag == INT || c.tag == FLT) ? in->a[1]
                  : c.tag == LIS ? in->a[2] : in->a[3];
            if (t < 0) goto failed;
            P = t;
            break; }

        case OP_NECK_CUT:
            if (B > B0) { B = B0; reset_hb(); }
            P++; break;
        case OP_GET_LEVEL: *reg(in->r1) = mk(INT, B0); P++; break;
        case OP_CUT: {
            int64_t lvl = reg(in->r1)->val;
            if (B > lvl) { B = lvl; reset_hb(); }
            P++; break; }

        case OP_FAIL: goto failed;
        case OP_HALT:
            if (trace_on) trace_post(in, h0);
            return 1;
        case OP_BUILTIN:
            if (!builtin(in->n)) goto failed;
            P++; break;
        default: rt_error("bad instruction");
        }
        if (trace_on) trace_post(in, h0);
        continue;

    failed:
        failing = 0;
        if (trace_on) { printf("       FAIL\n"); nbind = 0; }
        if (B == BOTTOM) return 0;
        P = (int)M[B + M[B].val + 4].val;
        if (trace_on) printf("       backtrack to choice point at s%lld, next clause at %d\n",
                             (long long)(B - STACK_BASE), P);
    }
}

static int guarded_run(int resume)
{
    if (setjmp(rtjmp)) return -1;
    return run(resume);
}

/* ── Answers ───────────────────────────────────────────────────────────── */

static int opt_all;

static void print_answer(void)
{
    int i, shown = 0;
    for (i = 0; i < nqnames; i++) {                 /* roots of unbound variables */
        int y = qnames[i].y;
        Cell d;
        named_root[i] = -1;
        if (E < 0 || y > M[E + 2].val) continue;
        d = deref(M[E + 2 + y]);
        if (d.tag == REF) named_root[i] = d.val;
    }
    naming = 1;
    for (i = 0; i < nqnames; i++) {
        int y = qnames[i].y, j;
        Cell d;
        if (E < 0 || y > M[E + 2].val) {
            printf("%s%s = <no such variable Y%d>", shown++ ? ", " : "", qnames[i].name, y);
            continue;
        }
        d = deref(M[E + 2 + y]);
        if (d.tag == REF) {
            for (j = 0; j < i && named_root[j] != named_root[i]; j++) ;
            if (j == i) continue;                   /* unbound: nothing to say */
            printf("%s%s = %s", shown++ ? ", " : "", qnames[i].name, qnames[j].name);
            continue;
        }
        printf("%s%s = ", shown++ ? ", " : "", qnames[i].name);
        put_term(stdout, d, 0);
    }
    naming = 0;
    if (!shown) fputs("true", stdout);
    putchar('\n');
}

static void run_query(const Token *t)
{
    int r, count = 0, resume = 0;
    Instr in;
    in_query = 0;
    if (!link_code()) return;
    (void)t;
    memset(&in, 0, sizeof in);
    start_machine(query_start);
    nbind = 0;
    for (;;) {
        r = guarded_run(resume);
        if (r < 0) return;
        if (r == 0) {
            if (count == 0 || !opt_all) puts("false");
            fflush(stdout);
            return;
        }
        count++;
        print_answer();
        fflush(stdout);
        if (opt_all) { resume = 1; continue; }
        if (peek_token() && !strcmp(pk.text, ";")) { has_pk = 0; resume = 1; continue; }
        return;
    }
}

/* ── Main ──────────────────────────────────────────────────────────────── */

static int load_all(void)
{
    if (setjmp(loadjmp)) return 1;
    while (next_token(&tok)) {
        statement(&tok);
        if (in_query && !strcmp(tok.text, "halt")) run_query(&tok);
    }
    if (in_query) load_error(NULL, "end of input inside a query (no 'halt')");
    if (link_failed || (nfix && !link_code())) return 1;
    return 0;
}

int main(int argc, char **argv)
{
    int i;
    const char *file = NULL;
    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-all")) opt_all = 1;
        else if (!strcmp(argv[i], "-trace")) trace_on = 1;
        else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            puts("usage: wam [-all] [-trace] [file | -]");
            return 0;
        } else if (argv[i][0] == '-' && argv[i][1]) {
            fprintf(stderr, "wam: unknown option %s\nusage: wam [-all] [-trace] [file | -]\n", argv[i]);
            return 2;
        } else file = argv[i];
    }
    if (file && strcmp(file, "-")) {
        src = fopen(file, "r");
        if (!src) { fprintf(stderr, "wam: cannot open %s\n", file); return 2; }
        srcname = file;
    } else {
        src = stdin;
        repl_mode = 1;
    }
    install_builtins();
    user_code = ncode;
    while (load_all()) {
        if (!repl_mode) return 1;
        in_query = 0;                              /* keep going after a bad token */
        has_pk = 0;
        while (last_c != '\n' && last_c != EOF) nextc();
        if (last_c == EOF) break;
    }
    fflush(stdout);
    return rt_failed;
}
