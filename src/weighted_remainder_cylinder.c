/* Exact finite cylinder sums and certified full-position intervals. */
#include "weighted_remainder_cylinder.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned cylinder_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned r = a % b; a = b; b = r; }
    return a;
}

static int distinct_outputs(mpq_ptr *outputs, unsigned count)
{
    for (unsigned i = 0; i < count; ++i)
        for (unsigned j = 0; j < i; ++j) if (outputs[i] == outputs[j]) return 0;
    return 1;
}

static int valid_cylinder(unsigned modulus, unsigned cutoff)
{
    return modulus >= 1 && modulus <= WEIGHTED_REMAINDER_EXACT_MAX &&
           cutoff >= 2 && cutoff <= WEIGHTED_REMAINDER_EXACT_MAX;
}

static int canonical_rational(const mpq_t value)
{
    if (mpz_sgn(mpq_denref(value)) <= 0) return 0;
    mpz_t g;
    mpz_init(g);
    mpz_gcd(g, mpq_numref(value), mpq_denref(value));
    int valid = mpz_cmp_ui(g, 1) == 0;
    mpz_clear(g);
    return valid;
}

static void cap_probability(mpq_t value)
{
    if (mpq_cmp_ui(value, 1, 1) > 0) mpq_set_ui(value, 1, 1);
}

int weighted_remainder_cylinder_q(mpq_t alignment, mpq_t mean, mpq_t radius,
                                  mpq_t omitted_mass, unsigned modulus,
                                  const mpz_t address, unsigned cutoff)
{
    mpq_ptr outputs[] = {alignment, mean, radius, omitted_mass};
    if (!valid_cylinder(modulus, cutoff) || !distinct_outputs(outputs, 4)) return 0;
    unsigned a = (unsigned)mpz_fdiv_ui(address, modulus);
    mpq_t c, m, r, tail, weight, factor, term;
    mpq_inits(c, m, r, tail, weight, factor, term, NULL);
    mpq_set_ui(tail, 1, 1);
    for (unsigned k = 2; k <= cutoff; ++k) {
        unsigned d = cylinder_gcd(k, modulus);
        weighted_remainder_weight_q(weight, k);
        mpq_sub(tail, tail, weight);
        mpq_set_ui(factor, d-1, 3);
        mpq_canonicalize(factor);
        mpq_mul(term, weight, factor);
        mpq_add(c, c, term);
        mpq_set_si(factor, 2L*(long)(a%d)-(long)(d-1), 3);
        mpq_canonicalize(factor);
        mpq_mul(term, weight, factor);
        mpq_add(m, m, term);
    }
    mpq_set_ui(factor, modulus-1, 3);
    mpq_canonicalize(factor);
    mpq_mul(r, factor, tail);
    mpq_set(alignment, c); mpq_set(mean, m);
    mpq_set(radius, r); mpq_set(omitted_mass, tail);
    mpq_clears(c, m, r, tail, weight, factor, term, NULL);
    return 1;
}

int weighted_remainder_position_q(mpq_t gap_lower, mpq_t gap_upper,
                                  mpq_t event_lower, mpq_t event_upper,
                                  mpq_t omitted_upper, unsigned modulus,
                                  const mpz_t address, unsigned cutoff,
                                  const mpq_t threshold)
{
    mpq_ptr outputs[] = {gap_lower, gap_upper, event_lower, event_upper, omitted_upper};
    if (!valid_cylinder(modulus, cutoff) || modulus < 2 || modulus > cutoff ||
        !distinct_outputs(outputs, 5) || !canonical_rational(threshold)) return 0;
    unsigned a = (unsigned)mpz_fdiv_ui(address, modulus);
    mpq_t c, m, r, tail, cup, half_gap, event, rel, weight, factor;
    mpq_t gl, gu, el, eu, omitted;
    mpq_inits(c, m, r, tail, cup, half_gap, event, rel, weight, factor,
              gl, gu, el, eu, omitted, NULL);
    weighted_remainder_cylinder_q(c, m, r, tail, modulus, address, cutoff);
    mpq_add(cup, c, r);
    mpq_add(half_gap, m, c);
    mpq_set_ui(factor, 1, 2);
    mpq_mul(half_gap, half_gap, factor);
    for (unsigned k = 2; k <= cutoff; ++k) {
        unsigned d = cylinder_gcd(k, modulus);
        if (d == 1) continue;
        mpq_set_ui(rel, a%d, d-1);
        mpq_canonicalize(rel);
        if (mpq_cmp(rel, threshold) <= 0) continue;
        weighted_remainder_weight_q(weight, k);
        mpq_set_ui(factor, d-1, 3);
        mpq_canonicalize(factor);
        mpq_mul(weight, weight, factor);
        mpq_add(event, event, weight);
    }
    mpq_div(gl, half_gap, cup);
    mpq_add(gu, half_gap, r); mpq_div(gu, gu, c); cap_probability(gu);
    mpq_div(el, event, cup);
    mpq_add(eu, event, r); mpq_div(eu, eu, c); cap_probability(eu);
    mpq_div(omitted, r, c); cap_probability(omitted);
    mpq_set(gap_lower, gl); mpq_set(gap_upper, gu);
    mpq_set(event_lower, el); mpq_set(event_upper, eu); mpq_set(omitted_upper, omitted);
    mpq_clears(c, m, r, tail, cup, half_gap, event, rel, weight, factor,
               gl, gu, el, eu, omitted, NULL);
    return 1;
}

int weighted_remainder_position_weight_q(mpq_t lower, mpq_t upper, mpq_t relative,
                                         unsigned modulus, const mpz_t address,
                                         unsigned period, unsigned cutoff)
{
    mpq_ptr outputs[] = {lower, upper, relative};
    if (!valid_cylinder(modulus, cutoff) || modulus < 2 || modulus > cutoff ||
        period > WEIGHTED_REMAINDER_EXACT_MAX || !distinct_outputs(outputs, 3)) return 0;
    unsigned d = cylinder_gcd(period, modulus);
    unsigned a = (unsigned)mpz_fdiv_ui(address, modulus);
    mpq_t c, m, r, tail, cup, numerator, factor, lo, hi, rel;
    mpq_inits(c, m, r, tail, cup, numerator, factor, lo, hi, rel, NULL);
    weighted_remainder_cylinder_q(c, m, r, tail, modulus, address, cutoff);
    mpq_add(cup, c, r);
    weighted_remainder_weight_q(numerator, period);
    mpq_set_ui(factor, d-1, 3); mpq_canonicalize(factor);
    mpq_mul(numerator, numerator, factor);
    mpq_div(lo, numerator, cup); mpq_div(hi, numerator, c); cap_probability(hi);
    if (d > 1) { mpq_set_ui(rel, a%d, d-1); mpq_canonicalize(rel); }
    mpq_set(lower, lo); mpq_set(upper, hi); mpq_set(relative, rel);
    mpq_clears(c, m, r, tail, cup, numerator, factor, lo, hi, rel, NULL);
    return 1;
}

static int parse_uint(const char *text, unsigned *out)
{
    if (!text || !*text) return 0;
    for (const char *p = text; *p; ++p) if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    unsigned long n = strtoul(text, &end, 10);
    if (errno || *end || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    *out = (unsigned)n;
    return 1;
}

static int parse_address(mpz_t out, const char *text)
{
    if (!text || !*text) return 0;
    const char *p = text;
    if (*p == '-' || *p == '+') ++p;
    if (!*p) return 0;
    for (; *p; ++p) if (*p < '0' || *p > '9') return 0;
    return mpz_set_str(out, *text == '+' ? text+1 : text, 10) == 0;
}

static int parse_threshold(mpq_t out, const char *text)
{
    if (!text || !*text) return 0;
    const char *p = text;
    if (*p == '-' || *p == '+') ++p;
    if (*p < '0' || *p > '9') return 0;
    while (*p >= '0' && *p <= '9') ++p;
    if (*p == '/') {
        ++p;
        if (*p < '0' || *p > '9') return 0;
        while (*p >= '0' && *p <= '9') ++p;
    }
    if (*p || mpq_set_str(out, *text == '+' ? text+1 : text, 10) != 0 ||
        mpz_sgn(mpq_denref(out)) <= 0) return 0;
    mpq_canonicalize(out);
    return 1;
}

int weighted_remainder_cylinder_command(int argc, char **argv)
{
    unsigned modulus = 0, cutoff = 0, period = 0;
    int ok = 0;
    mpz_t address;
    mpz_init(address);
    mpq_t c, m, r, tail, lo, hi, third, fourth, fifth, delta;
    mpq_inits(c, m, r, tail, lo, hi, third, fourth, fifth, delta, NULL);
    if (argc >= 6 && parse_uint(argv[3], &modulus) && parse_address(address, argv[4])) {
        if (strcmp(argv[2], "cylinder") == 0 && argc == 6 && parse_uint(argv[5], &cutoff)) {
            ok = weighted_remainder_cylinder_q(c, m, r, tail, modulus, address, cutoff);
            if (ok) {
                mpq_add(hi, c, r);
                gmp_printf("modulus=%u\nresidue=%lu\ncutoff=%u\nomitted_unit_mass=%Qd\n"
                           "finite_alignment=%Qd\nalignment_lower=%Qd\nalignment_upper=%Qd\n"
                           "finite_mean=%Qd\nmean_radius=%Qd\n", modulus,
                           mpz_fdiv_ui(address, modulus), cutoff, tail, c, c, hi, m, r);
                mpq_sub(lo, m, r); mpq_add(hi, m, r);
                gmp_printf("mean_lower=%Qd\nmean_upper=%Qd\n", lo, hi);
                mpq_add(lo, m, c); mpq_add(hi, lo, r); mpq_add(hi, hi, r);
                gmp_printf("absolute_gap_lower=%Qd\nabsolute_gap_upper=%Qd\n"
                           "unique_minimum_residue=0\nunique_maximum_residue=%u\n", lo, hi, modulus-1);
            }
        } else if (strcmp(argv[2], "position") == 0 && argc == 7 &&
                   parse_uint(argv[5], &cutoff) && parse_threshold(delta, argv[6])) {
            ok = weighted_remainder_position_q(lo, hi, third, fourth, fifth, modulus, address, cutoff, delta);
            if (ok) gmp_printf("modulus=%u\nresidue=%lu\ncutoff=%u\nthreshold=%Qd\n"
                               "relative_gap_lower=%Qd\nrelative_gap_upper=%Qd\n"
                               "exceedance_lower=%Qd\nexceedance_upper=%Qd\n"
                               "omitted_position_mass_upper=%Qd\n", modulus,
                               mpz_fdiv_ui(address, modulus), cutoff, delta, lo, hi, third, fourth, fifth);
        } else if (strcmp(argv[2], "position-weight") == 0 && argc == 7 &&
                   parse_uint(argv[5], &period) && parse_uint(argv[6], &cutoff)) {
            ok = weighted_remainder_position_weight_q(lo, hi, third, modulus, address, period, cutoff);
            if (ok) gmp_printf("modulus=%u\nresidue=%lu\nperiod=%u\ncutoff=%u\n"
                               "probability_lower=%Qd\nprobability_upper=%Qd\nrelative_residue=%Qd\n",
                               modulus, mpz_fdiv_ui(address, modulus), period, cutoff, lo, hi, third);
        }
    }
    if (!ok) fprintf(stderr, "Invalid cylinder query or resource bound exceeded; see weighted-remainder-state help.\n");
    mpz_clear(address);
    mpq_clears(c, m, r, tail, lo, hi, third, fourth, fifth, delta, NULL);
    return ok ? 0 : 1;
}
