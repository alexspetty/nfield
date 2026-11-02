#include "weighted_remainder_activation.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void weighted_remainder_activation_init(WeightedActivationResult *r)
{
    r->dimension = r->interval_count = 0;
    mpq_inits(r->minimum_increment, r->probability_sum, r->event_probability,
        r->coupled_probability, r->active_mean, r->active_variance,
        r->sperner_bound, r->universal_bound_squared, NULL);
}

void weighted_remainder_activation_clear(WeightedActivationResult *r)
{
    mpq_clears(r->minimum_increment, r->probability_sum, r->event_probability,
        r->coupled_probability, r->active_mean, r->active_variance,
        r->sperner_bound, r->universal_bound_squared, NULL);
}

static void result_set(WeightedActivationResult *r, const WeightedActivationResult *s)
{
    r->dimension = s->dimension; r->interval_count = s->interval_count;
    mpq_set(r->minimum_increment, s->minimum_increment);
    mpq_set(r->probability_sum, s->probability_sum);
    mpq_set(r->event_probability, s->event_probability);
    mpq_set(r->coupled_probability, s->coupled_probability);
    mpq_set(r->active_mean, s->active_mean);
    mpq_set(r->active_variance, s->active_variance);
    mpq_set(r->sperner_bound, s->sperner_bound);
    mpq_set(r->universal_bound_squared, s->universal_bound_squared);
}

static int canonical(mpq_srcptr q)
{
    if (!q || mpz_sgn(mpq_denref(q)) <= 0) return 0;
    mpz_t g;
    mpz_init(g); mpz_gcd(g, mpq_numref(q), mpq_denref(q));
    int ok = mpz_cmp_ui(g, 1) == 0;
    mpz_clear(g);
    return ok;
}

static unsigned bit_count(unsigned mask)
{
    unsigned n = 0;
    for (; mask; mask &= mask - 1) ++n;
    return n;
}

/* Build the complete law without division, including zero probabilities. */
static void product_law(mpq_t *law, unsigned n, const mpq_t *b, int activate)
{
    mpq_t p, complement;
    mpq_inits(p, complement, NULL);
    mpq_set_ui(law[0], 1, 1);
    for (unsigned i = 0; i < n; ++i) {
        mpq_set(p, b[i]);
        if (activate) mpq_mul_2exp(p, p, 1);
        mpq_set_ui(complement, 1, 1); mpq_sub(complement, complement, p);
        unsigned bit = 1u << i;
        for (unsigned s = 0; s < bit; ++s) {
            mpq_mul(law[s | bit], law[s], p);
            mpq_mul(law[s], law[s], complement);
        }
    }
    mpq_clears(p, complement, NULL);
}

int weighted_remainder_activation_q(WeightedActivationResult *out, unsigned n,
    const mpq_t *b, size_t nb, const mpq_t *values, size_t nvalues,
    const mpq_t a, const mpq_t u, const mpq_t v)
{
    if (!out || n > WEIGHTED_REMAINDER_ACTIVATION_MAX || nb != n ||
        nvalues != ((size_t)1 << n) || (n && !b) || !values ||
        !canonical(a) || !canonical(u) || !canonical(v) || mpq_sgn(a) <= 0) return 0;
    for (unsigned i = 0; i < n; ++i)
        if (!canonical(b[i]) || mpq_sgn(b[i]) < 0 || mpq_cmp_ui(b[i], 1, 2) > 0) return 0;
    for (size_t s = 0; s < nvalues; ++s) if (!canonical(values[s])) return 0;

    WeightedActivationResult r;
    weighted_remainder_activation_init(&r); r.dimension = n;
    mpq_t term, gap, total, one;
    mpq_inits(term, gap, total, one, NULL); mpq_set_ui(one, 1, 1);
    mpq_sub(gap, v, u);
    int ok = mpq_cmp(gap, a) < 0;
    unsigned first = 1;
    for (unsigned s = 0; ok && s < nvalues; ++s) {
        for (unsigned i = 0; i < n; ++i) if (!(s & (1u << i))) {
            mpq_sub(gap, values[s | (1u << i)], values[s]);
            if (first || mpq_cmp(gap, r.minimum_increment) < 0)
                mpq_set(r.minimum_increment, gap);
            first = 0;
            if (mpq_cmp(gap, a) < 0) { ok = 0; break; }
        }
    }
    mpq_t *law = NULL, *active = NULL;
    unsigned *subset_count = NULL;
    if (ok) {
        law = calloc(nvalues, sizeof(*law)); active = calloc(nvalues, sizeof(*active));
        subset_count = calloc(nvalues, sizeof(*subset_count));
        if (!law || !active || !subset_count) ok = 0;
    }
    if (ok) {
        for (unsigned s = 0; s < nvalues; ++s) { mpq_init(law[s]); mpq_init(active[s]); }
        product_law(law, n, b, 0); product_law(active, n, b, 1);
        for (unsigned s = 0; s < nvalues; ++s) {
            mpq_add(total, total, law[s]);
            if (mpq_cmp(u, values[s]) <= 0 && mpq_cmp(values[s], v) <= 0) {
                subset_count[s] = 1; ++r.interval_count;
                mpq_add(r.event_probability, r.event_probability, law[s]);
            }
        }
        /* Subset zeta transform: exact conditional counts on every active set. */
        for (unsigned i = 0; i < n; ++i)
            for (unsigned s = 0; s < nvalues; ++s)
                if (s & (1u << i)) subset_count[s] += subset_count[s ^ (1u << i)];
        mpz_t middle;
        mpz_init(middle);
        for (unsigned s = 0; s < nvalues; ++s) {
            if (mpq_cmp(u, values[s]) <= 0 && mpq_cmp(values[s], v) <= 0 &&
                subset_count[s] != 1) ok = 0; /* comparable distinct members */
            unsigned k = bit_count(s);
            mpq_set_ui(term, subset_count[s], 1u << k);
            mpq_canonicalize(term);
            mpq_mul(term, term, active[s]); mpq_add(r.coupled_probability, r.coupled_probability, term);
            mpz_bin_uiui(middle, k, k / 2);
            if (mpz_cmp_ui(middle, subset_count[s]) < 0) ok = 0;
            mpq_set_z(term, middle); mpq_div_2exp(term, term, k);
            mpq_mul(term, term, active[s]); mpq_add(r.sperner_bound, r.sperner_bound, term);
        }
        mpz_clear(middle);
        for (unsigned i = 0; i < n; ++i) {
            mpq_add(r.probability_sum, r.probability_sum, b[i]);
            mpq_mul_2exp(term, b[i], 1); mpq_sub(gap, one, term); mpq_mul(term, term, gap);
            mpq_add(r.active_variance, r.active_variance, term);
        }
        mpq_mul_2exp(r.active_mean, r.probability_sum, 1);
        mpq_add(gap, one, r.probability_sum); mpq_set_ui(term, 400, 1);
        mpq_div(r.universal_bound_squared, term, gap);
        mpq_mul(term, r.event_probability, r.event_probability);
        ok = ok && mpq_equal(total, one) && mpq_equal(r.event_probability, r.coupled_probability) &&
            mpq_cmp(r.event_probability, r.sperner_bound) <= 0 &&
            mpq_cmp(term, r.universal_bound_squared) <= 0;
        for (unsigned s = 0; s < nvalues; ++s) { mpq_clear(law[s]); mpq_clear(active[s]); }
    }
    if (ok) result_set(out, &r);
    free(law); free(active); free(subset_count);
    mpq_clears(term, gap, total, one, NULL); weighted_remainder_activation_clear(&r);
    return ok;
}

static int parse_dimension(const char *s, unsigned *n)
{
    if (!s || !*s) return 0;
    for (const char *p = s; *p; ++p) if (*p < '0' || *p > '9') return 0;
    char *end; errno = 0; unsigned long v = strtoul(s, &end, 10);
    if (errno || *end || v > WEIGHTED_REMAINDER_ACTIVATION_MAX) return 0;
    *n = (unsigned)v; return 1;
}

static int parse_rational(mpq_t q, const char *s)
{
    if (!s || !*s) return 0;
    const char *p = s;
    if (*p == '-' || *p == '+') ++p;
    const char *start = p;
    while (*p >= '0' && *p <= '9') ++p;
    if (p == start) return 0;
    if (*p == '/') {
        start = ++p;
        while (*p >= '0' && *p <= '9') ++p;
        if (p == start) return 0;
    }
    if (*p || mpq_set_str(q, *s == '+' ? s + 1 : s, 10) || mpz_sgn(mpq_denref(q)) <= 0) return 0;
    mpq_canonicalize(q); return 1;
}

static int parse_list(mpq_t *out, size_t n, const char *s)
{
    if (!n) return s && strcmp(s, "-") == 0;
    if (!s) return 0;
    char *copy = malloc(strlen(s) + 1);
    if (!copy) return 0;
    strcpy(copy, s);
    char *p = copy; int ok = 1;
    for (size_t i = 0; i < n; ++i) {
        char *next = strchr(p, ',');
        if (next) *next = '\0';
        if (!parse_rational(out[i], p) || (i + 1 < n) != (next != NULL)) { ok = 0; break; }
        if (next) p = next + 1;
    }
    free(copy); return ok;
}

int weighted_remainder_activation_command(int argc, char **argv)
{
    unsigned n = 0;
    if (argc != 9 || strcmp(argv[2], "activation") || !parse_dimension(argv[3], &n)) {
        fputs("Invalid activation query; expected n a u v probabilities values, n=0..12.\n", stderr);
        return 1;
    }
    size_t count = (size_t)1 << n;
    mpq_t *b = calloc(n ? n : 1, sizeof(*b)), *values = calloc(count, sizeof(*values));
    if (!b || !values) { free(b); free(values); return 1; }
    for (unsigned i = 0; i < n; ++i) mpq_init(b[i]);
    for (size_t i = 0; i < count; ++i) mpq_init(values[i]);
    mpq_t a, u, v;
    mpq_inits(a, u, v, NULL);
    WeightedActivationResult r; weighted_remainder_activation_init(&r);
    int ok = parse_rational(a, argv[4]) && parse_rational(u, argv[5]) && parse_rational(v, argv[6]) &&
        parse_list(b, n, argv[7]) && parse_list(values, count, argv[8]) &&
        weighted_remainder_activation_q(&r, n, b, n, values, count, a, u, v);
    if (ok) {
        printf("dimension=%u\ncube_size=%zu\ninterval_count=%u\ninterval_antichain=1\n", n, count, r.interval_count);
        if (n) gmp_printf("minimum_increment=%Qd\n", r.minimum_increment);
        else puts("minimum_increment=undefined_no_edges");
        gmp_printf("probability_sum=%Qd\nevent_probability=%Qd\ncoupled_probability=%Qd\n"
            "active_mean=%Qd\nactive_variance=%Qd\nsperner_bound=%Qd\nuniversal_bound_squared=%Qd\n",
            r.probability_sum, r.event_probability, r.coupled_probability,
            r.active_mean, r.active_variance, r.sperner_bound, r.universal_bound_squared);
        puts("Exact finite cube. The dimension-free bound is proved separately in Lean.");
    } else fputs("Invalid activation query: check rational lists, biases, positive increment and strict interval width.\n", stderr);
    weighted_remainder_activation_clear(&r); mpq_clears(a, u, v, NULL);
    for (unsigned i = 0; i < n; ++i) mpq_clear(b[i]);
    for (size_t i = 0; i < count; ++i) mpq_clear(values[i]);
    free(b); free(values);
    return ok ? 0 : 1;
}
