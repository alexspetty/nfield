/*
 * nfield: Fractional field analysis engine.
 *
 * For any integer n and positional base b, computes the structural
 * invariants of the fractional field {k/n : k = 1, ..., n-1}
 * by analyzing the repetend (periodic block) of each fraction's
 * expansion in base b.
 *
 * Compile with -DNFIELD_GMP and link -lgmp for arbitrary precision.
 * Without GMP, uses long long (good to ~9.2 * 10^18).
 *
 * 2025-2026  Alexander S. Petty
 */

#ifndef NFIELD_H
#define NFIELD_H

#include <stddef.h>

#ifdef NFIELD_GMP
#include <gmp.h>
typedef mpz_t nf_int;
#define nf_init(x)        mpz_init(x)
#define nf_init_set(x,v)  mpz_init_set_si(x, (long)(v))
#define nf_clear(x)       mpz_clear(x)
#define nf_set(x,v)       mpz_set_si(x, (long)(v))
#define nf_mul_ui(r,a,b)  mpz_mul_ui(r,a,b)
#define nf_tdiv_q(q,a,b)  mpz_tdiv_q(q,a,b)
#define nf_mod(r,a,b)     mpz_mod(r,a,b)
#define nf_get_si(x)      ((long long)mpz_get_si(x))
#define nf_cmp_ui(x,v)    mpz_cmp_ui(x,v)
#define nf_cmp(a,b)       mpz_cmp(a,b)
#else
typedef long long nf_int;
#define nf_init(x)        ((void)(x))
#define nf_init_set(x,v)  ((x) = (long long)(v))
#define nf_clear(x)       ((void)(x))
#define nf_set(x,v)       ((x) = (long long)(v))
#define nf_get_si(x)      (x)
#endif

/* ── Repetend ────────────────────────────────────────────── */

typedef struct {
    int  *digits;       /* full digit sequence (prefix + cycle)       */
    int   len;          /* total length of digits array               */
    int   cycle_start;  /* index where the cycle begins               */
    int   cycle_len;    /* length of repeating block (0 = terminates) */
} Repetend;

Repetend repetend_compute(int k, int n, int base);
void     repetend_free(Repetend *r);

/* ── Row ─────────────────────────────────────────────────── */

typedef struct {
    int       k;
    Repetend  rep;
    int       rot_index;    /* rotation offset relative to base rep    */
    double    alignment;    /* fraction of matching cycle positions     */
    double    curvature;    /* mean |d[i] - d[i+1]| in cycle           */
} Row;

/* ── Field ───────────────────────────────────────────────── */

typedef struct {
    int       n;
    int       base;
    Repetend  base_rep;     /* repetend of 1/n                         */
    Row      *rows;         /* rows[0..n-2] for k = 1..n-1             */
    int       num_rows;
} Field;

Field field_build(int n, int base);
void  field_free(Field *f);

/* ── Invariants ──────────────────────────────────────────── */
/*
 * Primitive invariants (pre-alignment program):
 *   C(n)  curvature     mean adjacent-digit variation in the base repetend
 *   R(n)  coherence     dominance of the most common rotation index
 *   H3(n) harmonicity   1 if cycle length divisible by 3, else 0
 *   S(n)  structure     R/C + H3
 *   B(n)  burden        accumulated structural load
 *   D(n)  depth         1/S + B
 *
 * Alignment program invariants (papers 1-15):
 *   alpha(n)  alignment       mean digit-match proportion across field
 *   sigma(n)  pairwise        mean digit-match among all pairs
 *   F(n)      focused         alpha - sigma
 *   Phi(k)    spectral power  Dirichlet kernel formula (paper 8)
 *   R(ell)    autocorrelation digit matches at lag ell (paper 9)
 *   C(g)      collision count residues sharing bin under multiplier g (paper 11)
 *   Gamma(ell) phase filter   spectral gate function (paper 10)
 */

typedef struct {
    int     n;
    int     base;
    int     cycle_length;   /* L: repetend length of 1/n               */
    double  curvature;      /* C(n)  (primitive)                       */
    double  coherence;      /* R(n)  (primitive)                       */
    int     harmonicity;    /* H3(n) (primitive)                       */
    double  structure;      /* S(n)  (primitive)                       */
    double  burden;         /* B(n)  (primitive)                       */
    double  depth;          /* D(n)  (primitive)                       */
    double  alignment;      /* mean alignment across the field         */
} Invariants;

Invariants invariants_compute(int n, int base);

/* ── Alignment ───────────────────────────────────────────── */

double alignment_exact(int n, int base);
double alignment_formula(int m, int p);
int    mult_order(int base, int p);
int    is_b_smooth(int n, int base);

/* ── Output ──────────────────────────────────────────────── */

void field_print(const Field *f);
void polar_print(int n, int base);
void invariants_print(const Invariants *inv);
void survey(int n_max, int base, int csv);
void survey_range(int n_min, int n_max, int base, int csv);
void table1(void);
/* ── Paper 5: coherence decomposition ────────────────────── */

double sigma_exact(int n, int base);
void   decompose_print(int n, int base);

/* ── Paper 8: spectral power ─────────────────────────────── */

void   spectral_print(int p, int base);

/* ── Verification ────────────────────────────────────── */

int    verify_dispatch(const char *name);

#endif /* NFIELD_H */
