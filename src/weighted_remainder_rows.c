#include "weighted_remainder_rows.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAX = WEIGHTED_REMAINDER_EXACT_MAX };

static int valid_period(unsigned q) { return q >= 2 && q <= MAX; }

static int mobius(unsigned n)
{
    int sign = 1;
    for (unsigned p = 2; p <= n / p; ++p) if (n % p == 0) {
        n /= p; sign = -sign;
        if (n % p == 0) return 0;
    }
    return n > 1 ? -sign : sign;
}

static long primitive_twice(unsigned q, const mpz_t n)
{
    long value = 0;
    for (unsigned d = 1; d <= q; ++d) if (q % d == 0)
        value += mobius(q / d) * (2L * (long)mpz_fdiv_ui(n, d) - (long)d + 1);
    return value;
}

void weighted_remainder_rows_init(WeightedRemainderRows *s)
{
    s->conductor = s->residue = s->radical = s->scale = s->totient = s->jordan_two = 0;
    mpq_inits(s->primitive, s->odd, s->ramanujan, s->primitive_norm_squared,
              s->odd_norm_squared, s->ramanujan_norm_squared, s->radical_descent, NULL);
}

void weighted_remainder_rows_clear(WeightedRemainderRows *s)
{
    mpq_clears(s->primitive, s->odd, s->ramanujan, s->primitive_norm_squared,
               s->odd_norm_squared, s->ramanujan_norm_squared, s->radical_descent, NULL);
}

int weighted_remainder_rows_compute(WeightedRemainderRows *out, unsigned q,
                                    const mpz_t address)
{
    if (!out || !valid_period(q)) return 0;
    long p2 = 0, r2 = 0, c = 0, j2 = 0, phi = 0;
    unsigned residue = (unsigned)mpz_fdiv_ui(address, q), radical = 1, n = q;
    for (unsigned d = 1; d <= q; ++d) if (q % d == 0) {
        long mu = mobius(q / d), r = residue % d;
        p2 += mu * (2 * r - (long)d + 1);
        r2 += mu * (r == 0 ? 0 : 2 * r - (long)d);
        if (r == 0) c += mu * d;
        phi += mu * d;
        j2 += mu * d * d;
    }
    for (unsigned p = 2; p <= n / p; ++p) if (n % p == 0) {
        radical *= p;
        do { n /= p; } while (n % p == 0);
    }
    if (n > 1) radical *= n;
    unsigned scale = q / radical;
    mpz_t descended;
    mpz_init(descended);
    mpz_fdiv_q_ui(descended, address, scale);
    long descent2 = (long)scale * primitive_twice(radical, descended);
    mpz_clear(descended);
    /* No address reads follow, including when it occupies an output limb. */
    out->conductor = q; out->residue = residue; out->radical = radical;
    out->scale = scale; out->totient = (unsigned)phi; out->jordan_two = (unsigned)j2;
    mpq_set_si(out->primitive, p2, 2); mpq_canonicalize(out->primitive);
    mpq_set_si(out->odd, r2, 2); mpq_canonicalize(out->odd);
    mpq_set_si(out->ramanujan, c, 1);
    mpq_set_si(out->primitive_norm_squared, j2, 12);
    mpq_canonicalize(out->primitive_norm_squared);
    mpq_set_si(out->odd_norm_squared, j2 - 3 * phi, 12);
    mpq_canonicalize(out->odd_norm_squared);
    mpq_set_si(out->ramanujan_norm_squared, phi, 1);
    mpq_set_si(out->radical_descent, descent2, 2); mpq_canonicalize(out->radical_descent);
    return 1;
}

static int canonical(const mpq_t x)
{
    if (mpz_sgn(mpq_denref(x)) <= 0) return 0;
    mpz_t g;
    mpz_init(g);
    mpz_gcd(g, mpq_numref(x), mpq_denref(x));
    int ok = mpz_cmp_ui(g, 1) == 0;
    mpz_clear(g);
    return ok;
}

int weighted_remainder_mass_inverse_q(mpq_t out, const mpq_t *xi,
                                      unsigned m, unsigned k)
{
    if (!xi || !valid_period(m) || !valid_period(k)) return 0;
    for (unsigned q = 0; q <= m; ++q) if (!canonical(xi[q])) return 0;
    if (mpq_sgn(xi[0]) || mpq_sgn(xi[1])) return 0;
    mpq_t value;
    mpq_init(value);
    for (unsigned j = 1; j <= m / k; ++j) {
        int mu = mobius(j);
        if (mu > 0) mpq_add(value, value, xi[k * j]);
        else if (mu < 0) mpq_sub(value, value, xi[k * j]);
    }
    mpq_set(out, value);
    mpq_clear(value);
    return 1;
}

void weighted_remainder_recovery_init(WeightedRemainderRecovery *s)
{
    s->period = s->conductor_cutoff = s->period_cutoff = s->quotient = 0;
    s->period_binary = s->quotient_binary = 0;
    mpq_inits(s->beta_lower, s->beta_upper, s->inverse_tail_error,
              s->mass_lower, s->mass_upper, NULL);
}

void weighted_remainder_recovery_clear(WeightedRemainderRecovery *s)
{
    mpq_clears(s->beta_lower, s->beta_upper, s->inverse_tail_error,
               s->mass_lower, s->mass_upper, NULL);
}

static unsigned binary_bound(unsigned n)
{
    unsigned b = 0, power = 1;
    while (power < 2 * n) { power *= 2; ++b; }
    return b;
}

int weighted_remainder_mass_recovery_compute(WeightedRemainderRecovery *out,
                                             unsigned d, unsigned Q, unsigned M)
{
    if (!out || !valid_period(d) || !valid_period(Q) || !valid_period(M) || d > Q) return 0;
    WeightedRemainderRecovery s;
    weighted_remainder_recovery_init(&s);
    mpq_t weights[MAX + 1], tail, amplitude;
    mpq_inits(tail, amplitude, NULL);
    mpq_set_ui(tail, 1, 1);
    for (unsigned k = 0; k <= M; ++k) {
        mpq_init(weights[k]);
        weighted_remainder_weight_q(weights[k], k);
        mpq_sub(tail, tail, weights[k]);
    }
    /* Raw interval arithmetic for the inverse prefix. In particular, do not
     * use the extrema API's lower clipping at the directly evaluated w_d/2:
     * this recovery certificate must not use its target to tighten itself. */
    for (unsigned j = 1; j <= Q / d; ++j) {
        int mu = mobius(j);
        if (!mu) continue;
        mpq_set_ui(amplitude, 0, 1);
        for (unsigned k = d * j; k <= M; k += d * j)
            mpq_add(amplitude, amplitude, weights[k]);
        if (mu > 0) {
            mpq_add(s.beta_lower, s.beta_lower, amplitude);
            mpq_add(s.beta_upper, s.beta_upper, amplitude);
            mpq_add(s.beta_upper, s.beta_upper, tail);
        } else {
            mpq_sub(s.beta_lower, s.beta_lower, amplitude);
            mpq_sub(s.beta_lower, s.beta_lower, tail);
            mpq_sub(s.beta_upper, s.beta_upper, amplitude);
        }
    }
    {
        unsigned J = Q / d, bd = binary_bound(d), bj = binary_bound(J);
        mpq_set_ui(s.inverse_tail_error, 4 * (bd + 2 * bj + 3), d * d * J);
        mpq_canonicalize(s.inverse_tail_error);
        mpq_sub(s.mass_lower, s.beta_lower, s.inverse_tail_error);
        if (mpq_sgn(s.mass_lower) < 0) mpq_set_ui(s.mass_lower, 0, 1);
        mpq_add(s.mass_upper, s.beta_upper, s.inverse_tail_error);
        out->period = d; out->conductor_cutoff = Q; out->period_cutoff = M;
        out->quotient = J; out->period_binary = bd; out->quotient_binary = bj;
        mpq_set(out->beta_lower, s.beta_lower); mpq_set(out->beta_upper, s.beta_upper);
        mpq_set(out->inverse_tail_error, s.inverse_tail_error);
        mpq_set(out->mass_lower, s.mass_lower); mpq_set(out->mass_upper, s.mass_upper);
    }
    for (unsigned k = 0; k <= M; ++k) mpq_clear(weights[k]);
    mpq_clears(tail, amplitude, NULL);
    weighted_remainder_recovery_clear(&s);
    return 1;
}

static int parse_period(const char *s, unsigned *out)
{
    if (!s || !*s) return 0;
    unsigned n = 0;
    for (; *s; ++s) {
        if (*s < '0' || *s > '9') return 0;
        n = n * 10 + (unsigned)(*s - '0');
        if (n > MAX) return 0;
    }
    if (!valid_period(n)) return 0;
    *out = n; return 1;
}

static int parse_integer(mpz_t out, const char *s)
{
    if (!s || !*s) return 0;
    const char *p = s;
    if (*p == '-') ++p;
    if (!*p) return 0;
    for (; *p; ++p) if (*p < '0' || *p > '9') return 0;
    return mpz_set_str(out, s, 10) == 0;
}

static int parse_rational(mpq_t out, const char *s)
{
    if (!s || !*s) return 0;
    const char *p = s;
    if (*p == '-') ++p;
    if (*p < '0' || *p > '9') return 0;
    while (*p >= '0' && *p <= '9') ++p;
    if (*p == '/') {
        ++p;
        if (*p < '0' || *p > '9') return 0;
        while (*p >= '0' && *p <= '9') ++p;
    }
    if (*p || mpq_set_str(out, s, 10) || mpz_sgn(mpq_denref(out)) <= 0) return 0;
    mpq_canonicalize(out); return 1;
}

static void print_row(const WeightedRemainderRows *s)
{
    gmp_printf("row %u %Qd %Qd %Qd %Qd\n", s->residue, s->primitive,
               s->odd, s->ramanujan, s->radical_descent);
}

int weighted_remainder_rows_command(int argc, char **argv)
{
    unsigned q, m, k;
    int ok = 0;
    if (argc < 3) return 1;
    if (!strcmp(argv[2], "rows")) {
        if ((argc != 4 && argc != 5) || !parse_period(argv[3], &q)) goto bad;
        mpz_t address;
        mpz_init(address);
        WeightedRemainderRows s;
        weighted_remainder_rows_init(&s);
        ok = argc == 4 || parse_integer(address, argv[4]);
        if (ok) {
            weighted_remainder_rows_compute(&s, q, address);
            printf("Exact primitive conductor rows\nconductor=%u\nradical=%u\nscale=%u\n"
                   "totient=%u\njordan_two=%u\n", q, s.radical, s.scale, s.totient, s.jordan_two);
            gmp_printf("primitive_norm_squared=%Qd\nodd_norm_squared=%Qd\nramanujan_norm_squared=%Qd\n",
                       s.primitive_norm_squared, s.odd_norm_squared, s.ramanujan_norm_squared);
            puts("row_columns=residue P R c radical_descent");
            if (argc == 5) { gmp_printf("address=%Zd\n", address); print_row(&s); }
            else for (unsigned a = 0; a < q; ++a) {
                mpz_set_ui(address, a); weighted_remainder_rows_compute(&s, q, address); print_row(&s);
            }
        }
        weighted_remainder_rows_clear(&s); mpz_clear(address);
    } else if (!strcmp(argv[2], "mass-inverse")) {
        if (argc < 5 || !parse_period(argv[3], &m) || !parse_period(argv[4], &k)) goto bad;
        mpq_t xi[MAX + 1], value;
        unsigned char seen[MAX + 1] = {0};
        for (unsigned j = 0; j <= MAX; ++j) mpq_init(xi[j]);
        mpq_init(value); ok = 1;
        for (int i = 5; i < argc && ok; ++i) {
            const char *colon = strchr(argv[i], ':');
            char index[32];
            if (!colon || colon == argv[i] || (size_t)(colon - argv[i]) >= sizeof index) { ok = 0; break; }
            size_t len = (size_t)(colon - argv[i]);
            memcpy(index, argv[i], len); index[len] = 0;
            if (!parse_period(index, &q) || q > m || seen[q] || !parse_rational(xi[q], colon + 1)) {
                ok = 0; break;
            }
            seen[q] = 1;
        }
        if (ok) ok = weighted_remainder_mass_inverse_q(value, xi, m, k);
        if (ok) {
            printf("Exact finite amplitude-to-mass inverse\ncutoff=%u\nperiod=%u\n", m, k);
            gmp_printf("recovered_mass=%Qd\n", value);
            puts("amplitude_semantics=supplied finite multiple transform; omitted entries zero");
        }
        for (unsigned j = 0; j <= MAX; ++j) mpq_clear(xi[j]);
        mpq_clear(value);
    } else if (!strcmp(argv[2], "mass-recovery")) {
        if (argc != 6 || !parse_period(argv[3], &k) || !parse_period(argv[4], &q) ||
            !parse_period(argv[5], &m)) goto bad;
        WeightedRemainderRecovery s;
        weighted_remainder_recovery_init(&s);
        ok = weighted_remainder_mass_recovery_compute(&s, k, q, m);
        if (ok) {
            printf("Full collision mass recovery enclosure\nperiod=%u\nconductor_cutoff=%u\n"
                   "period_cutoff=%u\nquotient=%u\nperiod_binary=%u\nquotient_binary=%u\n",
                   k, q, m, s.quotient, s.period_binary, s.quotient_binary);
            gmp_printf("beta_lower=%Qd\nbeta_upper=%Qd\ninverse_tail_error=%Qd\n"
                       "mass_lower=%Qd\nmass_upper=%Qd\n", s.beta_lower, s.beta_upper,
                       s.inverse_tail_error, s.mass_lower, s.mass_upper);
        }
        weighted_remainder_recovery_clear(&s);
    }
    if (ok) return 0;
bad:
    fputs("rows requires q in 2..240 and optional signed integer address; "
          "mass-inverse requires M,k in 2..240 and distinct q:amplitude entries with q<=M; "
          "mass-recovery requires 2<=d<=Q<=240 and 2<=M<=240.\n", stderr);
    return 1;
}
