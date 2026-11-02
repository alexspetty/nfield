/* Certified full conductor intervals and exhaustive restricted-gap bounds. */
#include "weighted_remainder_conductor.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAX = WEIGHTED_REMAINDER_EXACT_MAX };
typedef struct {
    mpq_t weight[MAX+1], eta_lo[MAX+1], eta_hi[MAX+1];
    mpq_t beta_lo[MAX+1], beta_hi[MAX+1], tail;
    mpz_t period;
    unsigned Q;
} ConductorTable;

static int valid_cutoffs(unsigned Q, unsigned M)
{
    return Q >= 2 && Q <= MAX && M >= 2 && M <= MAX;
}

static int distinct(mpq_ptr *out, unsigned n)
{
    for (unsigned i = 0; i < n; ++i)
        for (unsigned j = 0; j < i; ++j) if (out[i] == out[j]) return 0;
    return 1;
}

static int mobius(unsigned n)
{
    int sign = 1;
    for (unsigned p = 2; p <= n/p; ++p) if (n%p == 0) {
        n /= p; sign = -sign;
        if (n%p == 0) return 0;
    }
    return n > 1 ? -sign : sign;
}

static unsigned totient(unsigned n)
{
    unsigned phi = n;
    for (unsigned p = 2; p <= n/p; ++p) if (n%p == 0) {
        phi = phi/p*(p-1);
        do { n /= p; } while (n%p == 0);
    }
    return n > 1 ? phi/n*(n-1) : phi;
}

int weighted_remainder_conductor_period_z(mpz_t period, unsigned Q)
{
    if (Q < 2 || Q > MAX) return 0;
    mpz_set_ui(period, 1);
    for (unsigned d = 2; d <= Q; ++d) mpz_lcm_ui(period, period, d);
    return 1;
}

static void table_clear(ConductorTable *t)
{
    for (unsigned k = 0; k <= MAX; ++k)
        mpq_clears(t->weight[k], t->eta_lo[k], t->eta_hi[k],
                   t->beta_lo[k], t->beta_hi[k], NULL);
    mpq_clear(t->tail); mpz_clear(t->period); free(t);
}

static ConductorTable *table_build(unsigned Q, unsigned M)
{
    if (!valid_cutoffs(Q, M)) return NULL;
    ConductorTable *t = malloc(sizeof(*t));
    if (!t) return NULL;
    t->Q = Q;
    for (unsigned k = 0; k <= MAX; ++k)
        mpq_inits(t->weight[k], t->eta_lo[k], t->eta_hi[k],
                  t->beta_lo[k], t->beta_hi[k], NULL);
    mpq_init(t->tail); mpq_set_ui(t->tail, 1, 1); mpz_init(t->period);
    weighted_remainder_conductor_period_z(t->period, Q);
    for (unsigned k = 2; k <= (Q > M ? Q : M); ++k) {
        weighted_remainder_weight_q(t->weight[k], k);
        if (k <= M) mpq_sub(t->tail, t->tail, t->weight[k]);
    }
    for (unsigned q = 2; q <= Q; ++q) {
        for (unsigned k = q; k <= M; k += q)
            mpq_add(t->eta_lo[q], t->eta_lo[q], t->weight[k]);
        mpq_add(t->eta_hi[q], t->eta_lo[q], t->tail);
    }
    mpq_t half;
    mpq_init(half);
    for (unsigned d = 2; d <= Q; ++d) {
        for (unsigned j = 1; j <= Q/d; ++j) {
            int mu = mobius(j);
            if (mu > 0) {
                mpq_add(t->beta_lo[d], t->beta_lo[d], t->eta_lo[d*j]);
                mpq_add(t->beta_hi[d], t->beta_hi[d], t->eta_hi[d*j]);
            } else if (mu < 0) {
                mpq_sub(t->beta_lo[d], t->beta_lo[d], t->eta_hi[d*j]);
                mpq_sub(t->beta_hi[d], t->beta_hi[d], t->eta_lo[d*j]);
            }
        }
        /* Proved universal bound beta_d(Q)>w_d/2, not a finite positivity test. */
        mpq_div_2exp(half, t->weight[d], 1);
        if (mpq_cmp(t->beta_lo[d], half) < 0) mpq_set(t->beta_lo[d], half);
    }
    mpq_clear(half);
    return t;
}

int weighted_remainder_beta_interval_q(mpq_t lower, mpq_t upper,
                                       unsigned d, unsigned Q, unsigned M)
{
    if (lower == upper || d < 2 || d > Q || !valid_cutoffs(Q, M)) return 0;
    ConductorTable *t = table_build(Q, M);
    if (!t) return 0;
    mpq_set(lower, t->beta_lo[d]); mpq_set(upper, t->beta_hi[d]);
    table_clear(t);
    return 1;
}

static long row_twice(unsigned q, const mpz_t address)
{
    long row = 0;
    for (unsigned d = 1; d <= q; ++d) if (q%d == 0)
        row += mobius(q/d)*(2*(long)mpz_fdiv_ui(address, d)-(long)d+1);
    return row;
}

static void add_multiple(mpq_t sum, const mpq_t value, long numerator,
                         unsigned denominator, mpq_t factor, mpq_t term)
{
    mpq_set_si(factor, numerator, denominator); mpq_canonicalize(factor);
    mpq_mul(term, value, factor); mpq_add(sum, sum, term);
}

int weighted_remainder_conductor_interval_q(mpq_t fl, mpq_t fu, mpq_t vl, mpq_t vu,
                                            mpq_t gl, mpq_t gu, unsigned Q,
                                            const mpz_t address, unsigned M)
{
    mpq_ptr outputs[] = {fl, fu, vl, vu, gl, gu};
    if (!distinct(outputs, 6) || !valid_cutoffs(Q, M)) return 0;
    ConductorTable *t = table_build(Q, M);
    if (!t) return 0;
    mpq_t f_lo, f_hi, v_lo, v_hi, g_lo, g_hi, factor, term;
    mpq_inits(f_lo, f_hi, v_lo, v_hi, g_lo, g_hi, factor, term, NULL);
    for (unsigned q = 2; q <= Q; ++q) {
        long row = row_twice(q, address);
        add_multiple(f_lo, row >= 0 ? t->eta_lo[q] : t->eta_hi[q], row, 3, factor, term);
        add_multiple(f_hi, row >= 0 ? t->eta_hi[q] : t->eta_lo[q], row, 3, factor, term);
        add_multiple(v_lo, t->eta_lo[q], totient(q), 3, factor, term);
        add_multiple(v_hi, t->eta_hi[q], totient(q), 3, factor, term);
        long r2 = 2*(long)mpz_fdiv_ui(address, q);
        add_multiple(g_lo, t->beta_lo[q], r2, 3, factor, term);
        add_multiple(g_hi, t->beta_hi[q], r2, 3, factor, term);
    }
    /* Address may be part of an output rational; no address reads follow. */
    mpq_set(fl, f_lo); mpq_set(fu, f_hi); mpq_set(vl, v_lo);
    mpq_set(vu, v_hi); mpq_set(gl, g_lo); mpq_set(gu, g_hi);
    mpq_clears(f_lo, f_hi, v_lo, v_hi, g_lo, g_hi, factor, term, NULL);
    table_clear(t);
    return 1;
}

int weighted_remainder_prime_candidate_z(mpz_t address, unsigned Q, unsigned p)
{
    if (Q < 3 || Q > MAX || p < 2 || p > Q || Q >= 2*p) return 0;
    for (unsigned d = 2; d <= p/d; ++d) if (p%d == 0) return 0;
    mpz_t period, complement, prime, inverse, result;
    mpz_inits(period, complement, prime, inverse, result, NULL);
    weighted_remainder_conductor_period_z(period, Q);
    mpz_divexact_ui(complement, period, p); mpz_set_ui(prime, p);
    int ok = mpz_invert(inverse, complement, prime) != 0;
    if (ok) { mpz_mul(result, complement, inverse); mpz_set(address, result); }
    mpz_clears(period, complement, prime, inverse, result, NULL);
    return ok;
}

static void scaled_rational(mpq_t out, const mpz_t value, const mpz_t denominator)
{
    mpz_mul_ui(mpq_numref(out), value, 2);
    mpz_mul_ui(mpq_denref(out), denominator, 3);
    mpq_canonicalize(out);
}

static void next_gap(mpz_t value, mpz_t *coefficient, const mpz_t total,
                     unsigned Q, unsigned next)
{
    mpz_add(value, value, total);
    for (unsigned d = 2; d <= Q; ++d) if (next%d == 0)
        mpz_submul_ui(value, coefficient[d], d);
}

int weighted_remainder_conductor_extrema_q(mpq_t lower, mpq_t upper,
                                           unsigned *witness, unsigned *possible_count,
                                           unsigned Q, unsigned M,
                                           WeightedConductorVisitor visit, void *context)
{
    if (lower == upper || !witness || !possible_count || witness == possible_count ||
        Q < 3 || !valid_cutoffs(Q, M)) return 0;
    ConductorTable *t = table_build(Q, M);
    if (!t) return 0;
    if (mpz_cmp_ui(t->period, WEIGHTED_REMAINDER_CONDUCTOR_ENUM_MAX) > 0) {
        table_clear(t); return 0;
    }
    unsigned L = (unsigned)mpz_get_ui(t->period), best = 1, count = 0;
    mpz_t coeff_lo[MAX+1], coeff_hi[MAX+1], den, total_lo, total_hi, lo, hi, min_lo, min_hi;
    mpz_inits(den, total_lo, total_hi, lo, hi, min_lo, min_hi, NULL);
    mpz_set_ui(den, 1);
    for (unsigned d = 2; d <= Q; ++d) {
        mpz_inits(coeff_lo[d], coeff_hi[d], NULL);
        mpz_lcm(den, den, mpq_denref(t->beta_lo[d]));
        mpz_lcm(den, den, mpq_denref(t->beta_hi[d]));
    }
    for (unsigned d = 2; d <= Q; ++d) {
        mpz_divexact(coeff_lo[d], den, mpq_denref(t->beta_lo[d]));
        mpz_mul(coeff_lo[d], coeff_lo[d], mpq_numref(t->beta_lo[d]));
        mpz_divexact(coeff_hi[d], den, mpq_denref(t->beta_hi[d]));
        mpz_mul(coeff_hi[d], coeff_hi[d], mpq_numref(t->beta_hi[d]));
        mpz_add(total_lo, total_lo, coeff_lo[d]); mpz_add(total_hi, total_hi, coeff_hi[d]);
    }
    /* At a=1 all d>=2 have remainder one. Exact integer reset recurrence
     * avoids repeating rational gcd reduction at every residue. */
    mpz_set(lo, total_lo); mpz_set(hi, total_hi);
    mpz_set(min_lo, lo); mpz_set(min_hi, hi);
    for (unsigned a = 1; a < L-1; ++a) {
        if (mpz_cmp(lo, min_lo) < 0) mpz_set(min_lo, lo);
        if (mpz_cmp(hi, min_hi) < 0) { mpz_set(min_hi, hi); best = a; }
        next_gap(lo, coeff_lo, total_lo, Q, a+1);
        next_gap(hi, coeff_hi, total_hi, Q, a+1);
    }
    mpq_t row_lo, row_hi, result_lo, result_hi;
    mpq_inits(row_lo, row_hi, result_lo, result_hi, NULL);
    scaled_rational(result_lo, min_lo, den); scaled_rational(result_hi, min_hi, den);
    mpz_set(lo, total_lo); mpz_set(hi, total_hi);
    int ok = 1;
    for (unsigned a = 1; a < L-1; ++a) {
        if (mpz_cmp(lo, min_hi) <= 0) {
            ++count;
            if (visit) {
                scaled_rational(row_lo, lo, den); scaled_rational(row_hi, hi, den);
                if (!visit(a, row_lo, row_hi, context)) { ok = 0; break; }
            }
        }
        next_gap(lo, coeff_lo, total_lo, Q, a+1);
        next_gap(hi, coeff_hi, total_hi, Q, a+1);
    }
    if (ok) {
        mpq_set(lower, result_lo); mpq_set(upper, result_hi);
        *witness = best; *possible_count = count;
    }
    for (unsigned d = 2; d <= Q; ++d) mpz_clears(coeff_lo[d], coeff_hi[d], NULL);
    mpz_clears(den, total_lo, total_hi, lo, hi, min_lo, min_hi, NULL);
    mpq_clears(row_lo, row_hi, result_lo, result_hi, NULL);
    table_clear(t);
    return ok;
}

static int parse_uint(const char *s, unsigned *out)
{
    if (!s || !*s) return 0;
    for (const char *p = s; *p; ++p) if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    unsigned long n = strtoul(s, &end, 10);
    if (errno || *end || n > MAX) return 0;
    *out = (unsigned)n;
    return 1;
}

static int parse_address(mpz_t out, const char *s)
{
    if (!s || !*s) return 0;
    const char *p = s;
    if (*p == '-' || *p == '+') ++p;
    if (!*p) return 0;
    for (; *p; ++p) if (*p < '0' || *p > '9') return 0;
    return mpz_set_str(out, *s == '+' ? s+1 : s, 10) == 0;
}

static int print_candidate(unsigned a, const mpq_t lo, const mpq_t hi, void *context)
{
    (void)context;
    gmp_printf("possible_minimizer=%u gap_lower=%Qd gap_upper=%Qd\n", a, lo, hi);
    return 1;
}

int weighted_remainder_conductor_command(int argc, char **argv)
{
    unsigned Q = 0, M = 0, d = 0, best = 0, count = 0;
    int ok = 0;
    mpz_t address, period, residue, last;
    mpz_inits(address, period, residue, last, NULL);
    mpq_t fl, fu, vl, vu, gl, gu;
    mpq_inits(fl, fu, vl, vu, gl, gu, NULL);
    if (argc == 6 && strcmp(argv[2], "conductor-full") == 0 &&
        parse_uint(argv[3], &Q) && parse_address(address, argv[4]) && parse_uint(argv[5], &M)) {
        ok = weighted_remainder_conductor_interval_q(fl, fu, vl, vu, gl, gu, Q, address, M);
        if (ok) {
            weighted_remainder_conductor_period_z(period, Q); mpz_mod(residue, address, period);
            mpz_sub_ui(last, period, 1);
            gmp_printf("conductor_cutoff=%u\nperiod_cutoff=%u\nperiod=%Zd\nresidue=%Zd\n"
                       "value_lower=%Qd\nvalue_upper=%Qd\nendpoint_lower=%Qd\nendpoint_upper=%Qd\n"
                       "gap_lower=%Qd\ngap_upper=%Qd\nunique_minimum_residue=0\nunique_maximum_residue=%Zd\n",
                       Q, M, period, residue, fl, fu, vl, vu, gl, gu, last);
        }
    } else if (argc == 6 && strcmp(argv[2], "conductor-beta") == 0 &&
               parse_uint(argv[3], &d) && parse_uint(argv[4], &Q) && parse_uint(argv[5], &M)) {
        ok = weighted_remainder_beta_interval_q(gl, gu, d, Q, M);
        if (ok) gmp_printf("row=%u\nconductor_cutoff=%u\nperiod_cutoff=%u\nbeta_lower=%Qd\nbeta_upper=%Qd\n",
                           d, Q, M, gl, gu);
    } else if (argc == 5 && strcmp(argv[2], "conductor-prime") == 0 &&
               parse_uint(argv[3], &Q) && parse_uint(argv[4], &d)) {
        ok = weighted_remainder_prime_candidate_z(address, Q, d);
        if (ok) {
            weighted_remainder_conductor_period_z(period, Q);
            gmp_printf("conductor_cutoff=%u\nprime=%u\nperiod=%Zd\ncandidate_residue=%Zd\n"
                       "candidate_gap=2*eta_prime/3\n", Q, d, period, address);
        }
    } else if (argc == 5 && (strcmp(argv[2], "conductor-extrema") == 0 ||
                            strcmp(argv[2], "conductor-minimizers") == 0) &&
               parse_uint(argv[3], &Q) && parse_uint(argv[4], &M)) {
        ok = weighted_remainder_conductor_extrema_q(gl, gu, &best, &count, Q, M,
             strcmp(argv[2], "conductor-minimizers") == 0 ? print_candidate : NULL, NULL);
        if (ok) {
            weighted_remainder_conductor_period_z(period, Q);
            gmp_printf("conductor_cutoff=%u\nperiod_cutoff=%u\nperiod=%Zd\n"
                       "restricted_gap_lower=%Qd\nrestricted_gap_upper=%Qd\n"
                       "upper_bound_witness=%u\npossible_minimizer_count=%u\n",
                       Q, M, period, gl, gu, best, count);
            if (count == 1) printf("certified_unique_minimizer=%u\n", best);
            else puts("minimizer_status=overlapping_intervals");
        }
    }
    if (!ok) fputs("Invalid conductor query or resource bound exceeded; see weighted-remainder-state help.\n", stderr);
    mpz_clears(address, period, residue, last, NULL);
    mpq_clears(fl, fu, vl, vu, gl, gu, NULL);
    return ok ? 0 : 1;
}
