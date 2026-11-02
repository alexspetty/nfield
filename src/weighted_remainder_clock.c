#include "weighted_remainder_clock.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned clock_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned r = a % b; a = b; b = r; }
    return a;
}

static int clock_cutoff(unsigned m)
{
    return m >= 2 && m <= WEIGHTED_REMAINDER_EXACT_MAX;
}

void weighted_remainder_clock_init(WeightedRemainderClock *c)
{
    c->cutoff = 0;
    mpq_inits(c->retained_mass, c->omitted_mass, c->raw_age,
              c->stationary_age, c->centered_age, c->increment, NULL);
}

void weighted_remainder_clock_clear(WeightedRemainderClock *c)
{
    mpq_clears(c->retained_mass, c->omitted_mass, c->raw_age,
               c->stationary_age, c->centered_age, c->increment, NULL);
}

int weighted_remainder_clock_compute(WeightedRemainderClock *out, unsigned m,
                                      const mpz_t address)
{
    if (!out || !clock_cutoff(m)) return 0;
    WeightedRemainderClock c;
    weighted_remainder_clock_init(&c);
    mpq_t weight, factor, term;
    mpq_inits(weight, factor, term, NULL);
    for (unsigned k = 2; k <= m; ++k) {
        unsigned r = (unsigned)mpz_fdiv_ui(address, k);
        weighted_remainder_weight_q(weight, k);
        mpq_add(c.retained_mass, c.retained_mass, weight);
        mpq_set_ui(factor, 2 * r, 3);
        mpq_canonicalize(factor);
        mpq_mul(term, weight, factor);
        mpq_add(c.raw_age, c.raw_age, term);
        mpq_set_ui(factor, k - 1, 3);
        mpq_canonicalize(factor);
        mpq_mul(term, weight, factor);
        mpq_add(c.stationary_age, c.stationary_age, term);
        mpq_set_si(factor, r ? 2 : 2 - 2 * (long)k, 3);
        mpq_canonicalize(factor);
        mpq_mul(term, weight, factor);
        mpq_add(c.increment, c.increment, term);
    }
    mpq_sub(c.centered_age, c.raw_age, c.stationary_age);
    mpq_set_ui(c.omitted_mass, 1, 1);
    mpq_sub(c.omitted_mass, c.omitted_mass, c.retained_mass);
    out->cutoff = m;
    mpq_set(out->retained_mass, c.retained_mass);
    mpq_set(out->omitted_mass, c.omitted_mass);
    mpq_set(out->raw_age, c.raw_age);
    mpq_set(out->stationary_age, c.stationary_age);
    mpq_set(out->centered_age, c.centered_age);
    mpq_set(out->increment, c.increment);
    mpq_clears(weight, factor, term, NULL);
    weighted_remainder_clock_clear(&c);
    return 1;
}

typedef struct { mpq_t value; } ClockSample;

static int clock_compare(const void *first, const void *second)
{
    const ClockSample *a = first, *b = second;
    return mpq_cmp(a->value, b->value);
}

int weighted_remainder_clock_law(unsigned *period, unsigned *distinct,
                                  unsigned m, WeightedClockLawVisitor visit,
                                  void *context)
{
    if (!period || !distinct || period == distinct || !clock_cutoff(m)) return 0;
    unsigned length = 1;
    for (unsigned k = 2; k <= m; ++k) {
        unsigned reduced = length / clock_gcd(length, k);
        if (reduced > WEIGHTED_REMAINDER_CLOCK_LAW_MAX / k) return 0;
        length = reduced * k;
    }
    ClockSample *samples = malloc(length * sizeof *samples);
    if (!samples) return 0;
    mpq_t weights[WEIGHTED_REMAINDER_EXACT_MAX + 1], factor, term;
    mpq_inits(factor, term, NULL);
    for (unsigned k = 2; k <= m; ++k) {
        mpq_init(weights[k]);
        weighted_remainder_weight_q(weights[k], k);
    }
    for (unsigned n = 0; n < length; ++n) {
        mpq_init(samples[n].value);
        for (unsigned k = 2; k <= m; ++k) {
            mpq_set_si(factor, 2L * (n % k) - (long)k + 1, 3);
            mpq_canonicalize(factor);
            mpq_mul(term, factor, weights[k]);
            mpq_add(samples[n].value, samples[n].value, term);
        }
    }
    qsort(samples, length, sizeof *samples, clock_compare);
    unsigned count = 0;
    int ok = 1;
    for (unsigned i = 0; i < length;) {
        unsigned j = i + 1;
        while (j < length && mpq_equal(samples[i].value, samples[j].value)) ++j;
        ++count;
        if (visit && !visit(samples[i].value, j - i, context)) { ok = 0; break; }
        i = j;
    }
    if (ok) { *period = length; *distinct = count; }
    for (unsigned n = 0; n < length; ++n) mpq_clear(samples[n].value);
    for (unsigned k = 2; k <= m; ++k) mpq_clear(weights[k]);
    mpq_clears(factor, term, NULL);
    free(samples);
    return ok;
}

int weighted_remainder_cycle_q(mpq_t orbit, mpq_t stationary, mpq_t cesaro,
                                unsigned k, unsigned r,
                                const mpz_t address, const mpz_t last)
{
    if (orbit == stationary || orbit == cesaro || stationary == cesaro ||
        !clock_cutoff(k) || r >= k || mpz_sgn(last) < 0) return 0;
    mpz_t count, length;
    mpz_inits(count, length, NULL);
    mpz_add_ui(length, last, 1);
    if (mpz_cmp_ui(last, r) >= 0) {
        mpz_sub_ui(count, last, r);
        mpz_fdiv_q_ui(count, count, k);
        mpz_add_ui(count, count, 1);
    }
    int hit = mpz_fdiv_ui(address, k) == r;
    mpq_t weight, star, average, factor;
    mpq_inits(weight, star, average, factor, NULL);
    weighted_remainder_weight_q(weight, k);
    mpq_set_ui(factor, 1, k);
    mpq_mul(star, weight, factor);
    mpz_set(mpq_numref(factor), count);
    mpz_set(mpq_denref(factor), length);
    mpq_canonicalize(factor);
    mpq_mul(average, weight, factor);
    if (hit) mpq_set(orbit, weight); else mpq_set_ui(orbit, 0, 1);
    mpq_set(stationary, star);
    mpq_set(cesaro, average);
    mpq_clears(weight, star, average, factor, NULL);
    mpz_clears(count, length, NULL);
    return 1;
}

int weighted_remainder_cycle_tv_q(mpq_t lower, mpq_t upper, mpq_t omitted,
                                   unsigned m, const mpz_t last)
{
    if (lower == upper || lower == omitted || upper == omitted ||
        !clock_cutoff(m) || mpz_sgn(last) < 0) return 0;
    mpz_t length;
    mpz_init(length);
    mpz_add_ui(length, last, 1);
    mpq_t sum, tail, weight, factor, term;
    mpq_inits(sum, tail, weight, factor, term, NULL);
    mpq_set_ui(tail, 1, 1);
    for (unsigned k = 2; k <= m; ++k) {
        unsigned s = (unsigned)mpz_fdiv_ui(length, k);
        weighted_remainder_weight_q(weight, k);
        mpq_sub(tail, tail, weight);
        /* s residues have one extra visit. Half their total discrepancy
         * from uniform is s*(k-s)/(k*length), before multiplying by w_k. */
        mpz_set_ui(mpq_numref(factor), s * (k - s));
        mpz_mul_ui(mpq_denref(factor), length, k);
        mpq_canonicalize(factor);
        mpq_mul(term, weight, factor);
        mpq_add(sum, sum, term);
    }
    mpq_set(lower, sum);
    mpq_add(upper, sum, tail);
    mpq_set(omitted, tail);
    mpq_clears(sum, tail, weight, factor, term, NULL);
    mpz_clear(length);
    return 1;
}

int weighted_remainder_clock_covariance_q(mpq_t out, unsigned k, unsigned l)
{
    if (!k || !l || k > WEIGHTED_REMAINDER_EXACT_MAX ||
        l > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    unsigned g = clock_gcd(k, l);
    mpq_set_ui(out, g * g - 1, 12);
    mpq_canonicalize(out);
    return 1;
}

static int clock_mobius(unsigned n)
{
    int sign = 1;
    for (unsigned p = 2; p <= n / p; ++p) if (n % p == 0) {
        n /= p;
        if (n % p == 0) return 0;
        sign = -sign;
    }
    return n > 1 ? -sign : sign;
}

int weighted_remainder_age_budget_q(mpq_t harmonic_cross, mpq_t first_moment,
                                     unsigned m)
{
    if (harmonic_cross == first_moment || m > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t cross[WEIGHTED_REMAINDER_EXACT_MAX + 1], h, h2, factor, sum, term;
    mpq_inits(h, h2, factor, sum, term, NULL);
    mpq_init(cross[0]);
    for (unsigned k = 1; k <= m; ++k) {
        mpq_init(cross[k]);
        mpq_set_ui(factor, 1, k);
        mpq_add(h, h, factor);
        mpq_set_ui(factor, 1, k * k);
        mpq_add(h2, h2, factor);
        mpq_mul(cross[k], h, h);
        mpq_sub(cross[k], cross[k], h2);
        mpq_div_2exp(cross[k], cross[k], 1);
    }
    for (unsigned d = 1; d <= m; ++d) {
        mpq_set_si(factor, clock_mobius(d), d * d);
        mpq_canonicalize(factor);
        mpq_mul(term, factor, cross[m / d]);
        mpq_add(sum, sum, term);
    }
    mpq_set(harmonic_cross, cross[m]);
    mpq_set(first_moment, sum);
    for (unsigned k = 0; k <= m; ++k) mpq_clear(cross[k]);
    mpq_clears(h, h2, factor, sum, term, NULL);
    return 1;
}

static int clock_parse_index(const char *text, unsigned *out)
{
    if (!text || !*text) return 0;
    unsigned n = 0;
    for (const char *p = text; *p; ++p) {
        if (*p < '0' || *p > '9') return 0;
        n = 10 * n + (unsigned)(*p - '0');
        if (n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    }
    *out = n;
    return 1;
}

static int clock_parse_integer(mpz_t out, const char *text, int nonnegative)
{
    if (!text || !*text) return 0;
    const char *p = text;
    if (*p == '-' || *p == '+') ++p;
    if (!*p) return 0;
    for (const char *digit = p; *digit; ++digit)
        if (*digit < '0' || *digit > '9') return 0;
    /* GMP accepts '-' but its decimal parser need not accept '+'. */
    if (mpz_set_str(out, *text == '+' ? text + 1 : text, 10)) return 0;
    return !nonnegative || mpz_sgn(out) >= 0;
}

static int clock_print_atom(const mpq_t value, unsigned count, void *context)
{
    (void)context;
    return gmp_printf("atom %Qd %u\n", value, count) >= 0;
}

int weighted_remainder_clock_command(int argc, char **argv)
{
    int ok = 0;
    unsigned m = 0, r = 0;
    mpz_t address, last;
    mpz_inits(address, last, NULL);
    mpq_t first, second, third;
    mpq_inits(first, second, third, NULL);
    if (argc == 5 && !strcmp(argv[2], "clock") &&
        clock_parse_index(argv[3], &m) &&
        clock_parse_integer(address, argv[4], 0)) {
        WeightedRemainderClock state;
        weighted_remainder_clock_init(&state);
        ok = weighted_remainder_clock_compute(&state, m, address);
        if (ok) {
            printf("Exact finite remainder clock\ncutoff %u\n", m);
            gmp_printf("address %Zd\nretained_mass %Qd\nomitted_mass %Qd\n"
                       "raw_age %Qd\nstationary_age %Qd\ncentered_age %Qd\n"
                       "finite_increment %Qd\n", address, state.retained_mass,
                       state.omitted_mass, state.raw_age, state.stationary_age,
                       state.centered_age, state.increment);
        }
        weighted_remainder_clock_clear(&state);
    } else if (argc == 4 && !strcmp(argv[2], "clock-law") &&
               clock_parse_index(argv[3], &m)) {
        unsigned period, distinct;
        ok = weighted_remainder_clock_law(&period, &distinct, m, clock_print_atom, NULL);
        if (ok) {
            printf("Exact finite centered-age law\ncutoff %u\nperiod %u\ndistinct %u\n"
                   "Each atom line gives value and multiplicity; probability is multiplicity/period.\n",
                   m, period, distinct);
            mpq_set_ui(first, 0, 1);
            for (unsigned k = 2; k <= m; ++k) {
                weighted_remainder_weight_q(third, k);
                mpq_add(first, first, third);
            }
            mpq_set_ui(second, 1, 1);
            mpq_sub(second, second, first);
            gmp_printf("retained_mass %Qd\nomitted_mass %Qd\n", first, second);
        }
    } else if (argc == 7 && !strcmp(argv[2], "cycle") &&
               clock_parse_index(argv[3], &m) && clock_parse_index(argv[4], &r) &&
               clock_parse_integer(address, argv[5], 0) &&
               clock_parse_integer(last, argv[6], 1)) {
        ok = weighted_remainder_cycle_q(first, second, third, m, r, address, last);
        if (ok) {
            printf("Exact cycle probabilities\nperiod %u\nresidue %u\nnext_residue %u\n",
                   m, r, (r + 1) % m);
            gmp_printf("address %Zd\nlast_observation %Zd\norbit_mass %Qd\n"
                       "stationary_mass %Qd\ncesaro_mass %Qd\n", address, last,
                       first, second, third);
            mpz_add_ui(last, last, 1);
            gmp_printf("observations %Zd\n", last);
            weighted_remainder_weight_q(first, m);
            mpq_set_ui(second, 1, 1);
            mpq_sub(second, second, first);
            gmp_printf("cycle_mass %Qd\nother_cycle_mass %Qd\n", first, second);
        }
    } else if (argc == 5 && !strcmp(argv[2], "cycle-tv") &&
               clock_parse_index(argv[3], &m) && clock_parse_integer(last, argv[4], 1)) {
        ok = weighted_remainder_cycle_tv_q(first, second, third, m, last);
        if (ok) {
            printf("Exact bounds for Cesaro total variation\ncutoff %u\n", m);
            gmp_printf("last_observation %Zd\ntv_lower %Qd\ntv_upper %Qd\n"
                       "omitted_mass %Qd\n", last, first, second, third);
            mpz_add_ui(last, last, 1);
            gmp_printf("observations %Zd\n", last);
        }
    } else if (argc == 4 && !strcmp(argv[2], "age-budget") &&
               clock_parse_index(argv[3], &m)) {
        ok = weighted_remainder_age_budget_q(first, second, m);
        if (ok) {
            printf("Exact stationary-age harmonic budget\ncutoff %u\n", m);
            gmp_printf("harmonic_cross_sum %Qd\nfirst_moment_mobius %Qd\n", first, second);
        }
    } else if (argc == 5 && !strcmp(argv[2], "covariance") &&
               clock_parse_index(argv[3], &m) && clock_parse_index(argv[4], &r)) {
        ok = weighted_remainder_clock_covariance_q(first, m, r);
        if (ok) {
            printf("Exact complete-period remainder covariance\nfirst_period %u\nsecond_period %u\n",
                   m, r);
            gmp_printf("covariance %Qd\n", first);
        }
    }
    mpq_clears(first, second, third, NULL);
    mpz_clears(address, last, NULL);
    if (!ok) {
        fputs("Use clock <cutoff> <address>, clock-law <cutoff>, "
              "cycle <period> <residue> <address> <last>, cycle-tv <cutoff> <last>, "
              "covariance <first> <second>, or age-budget <cutoff>. Cutoffs and cycle periods are 2..240; "
              "age-budget cutoffs are 0..240; "
              "covariance periods are 1..240; residue is 0..period-1. "
              "Address is a signed integer; last is a nonnegative integer, "
              "averaging observations 0..last. Clock-law requires lcm(1..cutoff)<=50000 "
              "(cutoff 2..12).\n", stderr);
    }
    return ok ? 0 : 1;
}
