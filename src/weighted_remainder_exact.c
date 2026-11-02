/* Exact finite boundary objects and Lebesgue ramp integrals. */
#include "weighted_remainder_exact.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned exact_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned t = a % b; a = b; b = t; }
    return a;
}

int weighted_remainder_weight_q(mpq_t out, unsigned k)
{
    if (k > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t sum, term;
    mpq_inits(sum, term, NULL);
    for (unsigned a = 1; a < k; ++a) if (exact_gcd(a, k) == 1) {
        mpq_set_ui(term, 1, a);
        mpq_add(sum, sum, term);
    }
    if (k) {
        mpq_set_ui(term, 1, k * k);
        mpq_mul(sum, sum, term);
    }
    mpq_set(out, sum);
    mpq_clears(sum, term, NULL);
    return 1;
}

int weighted_remainder_capacity_q(mpq_t out, unsigned n)
{
    if (n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t sum, term;
    mpq_inits(sum, term, NULL);
    for (unsigned r = 1; r <= n; ++r) for (unsigned s = 1; s <= n; ++s) {
        unsigned g = exact_gcd(r, s);
        mpq_set_ui(term, g * g, 3 * r * s);
        mpq_canonicalize(term);
        mpq_add(sum, sum, term);
    }
    mpq_set(out, sum);
    mpq_clears(sum, term, NULL);
    return 1;
}

int weighted_remainder_ramp_overlap_q(mpq_t out, unsigned r, unsigned s)
{
    if (!r || !s || r > WEIGHTED_REMAINDER_EXACT_MAX ||
        s > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    unsigned cells = r / exact_gcd(r, s) * s;
    mpq_t sum, first, second, correction, term;
    mpq_inits(sum, first, second, correction, term, NULL);
    /* On each cell, use actual midpoint values and slopes. No gcd-energy
     * formula is used to compute the integral. All products are GMP rationals. */
    mpq_set_ui(correction, r * s, 12);
    mpz_mul_ui(mpq_denref(correction), mpq_denref(correction), cells);
    mpz_mul_ui(mpq_denref(correction), mpq_denref(correction), cells);
    mpq_canonicalize(correction);
    for (unsigned j = 0; j < cells; ++j) {
        long a = 2L * ((r * j) % cells) + (long)r - (long)cells;
        long b = 2L * ((s * j) % cells) + (long)s - (long)cells;
        mpq_set_si(first, a, 2 * cells);
        mpq_set_si(second, b, 2 * cells);
        mpq_canonicalize(first);
        mpq_canonicalize(second);
        mpq_mul(term, first, second);
        mpq_add(term, term, correction);
        mpq_add(sum, sum, term);
    }
    mpq_set_ui(term, 1, cells);
    mpq_mul(out, sum, term);
    mpq_clears(sum, first, second, correction, term, NULL);
    return 1;
}

int weighted_remainder_midpoint_q(mpq_t out, unsigned r, const mpq_t phase)
{
    if (r > WEIGHTED_REMAINDER_EXACT_MAX || mpz_sgn(mpq_denref(phase)) <= 0) return 0;
    mpq_t value, half;
    mpq_inits(value, half, NULL);
    mpz_mul_ui(mpq_numref(value), mpq_numref(phase), r);
    mpz_mod(mpq_numref(value), mpq_numref(value), mpq_denref(phase));
    mpz_set(mpq_denref(value), mpq_denref(phase));
    mpq_canonicalize(value);
    if (mpq_sgn(value)) {
        mpq_set_ui(half, 1, 2);
        mpq_sub(value, value, half);
    }
    mpq_set(out, value);
    mpq_clears(value, half, NULL);
    return 1;
}

int weighted_remainder_response_q(mpq_t out, unsigned n, const mpq_t phase)
{
    if (n > WEIGHTED_REMAINDER_EXACT_MAX || mpz_sgn(mpq_denref(phase)) <= 0) return 0;
    mpq_t sum, term;
    mpq_inits(sum, term, NULL);
    for (unsigned r = 1; r <= n; ++r) {
        weighted_remainder_midpoint_q(term, r, phase);
        mpq_add(sum, sum, term);
    }
    mpq_add(out, sum, sum);
    mpq_clears(sum, term, NULL);
    return 1;
}

int weighted_remainder_boundary_visit(unsigned n, WeightedBoundaryVisitor visit, void *context)
{
    if (n > WEIGHTED_REMAINDER_EXACT_MAX || !visit) return 0;
    for (unsigned k = 1; k <= n; ++k)
        for (unsigned a = 0; a < k; ++a)
            if (exact_gcd(a, k) == 1 && !visit(a, k, n / k, context)) return 0;
    return 1;
}

int weighted_remainder_amplitude_interval_q(mpq_t lower, mpq_t upper,
                                            unsigned q, unsigned cutoff)
{
    if (lower == upper || q < 2 || cutoff < 2 ||
        q > WEIGHTED_REMAINDER_EXACT_MAX || cutoff > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t partial, mass, weight, high;
    mpq_inits(partial, mass, weight, high, NULL);
    for (unsigned k = 2; k <= cutoff; ++k) {
        weighted_remainder_weight_q(weight, k);
        mpq_add(mass, mass, weight);
        if (k % q == 0) mpq_add(partial, partial, weight);
    }
    mpq_set_ui(high, 1, 1);
    mpq_sub(high, high, mass);
    mpq_add(high, high, partial);
    mpq_set(lower, partial);
    mpq_set(upper, high);
    mpq_clears(partial, mass, weight, high, NULL);
    return 1;
}

static int parse_index(const char *text, unsigned minimum, unsigned *out)
{
    if (!text || !*text || *text == '-') return 0;
    char *end;
    errno = 0;
    unsigned long n = strtoul(text, &end, 10);
    if (errno || *end || n < minimum || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    *out = (unsigned)n;
    return 1;
}

static int print_atom(unsigned a, unsigned k, unsigned multiplicity, void *context)
{
    (void)context;
    printf("%u/%u %u\n", a, k, multiplicity);
    return 1;
}

int weighted_remainder_exact_command(int argc, char **argv)
{
    unsigned a, b;
    mpq_t value, deficit;
    if (argc == 4 && strcmp(argv[2], "boundary") == 0 && parse_index(argv[3], 0, &a)) {
        mpq_inits(value, deficit, NULL);
        weighted_remainder_capacity_q(value, a);
        mpq_set_ui(deficit, a, 1);
        mpq_sub(deficit, deficit, value);
        printf("Exact rational boundary\nresolution %u\n", a);
        gmp_printf("capacity %Qd\ndeficit %Qd\n", value, deficit);
        printf("total multiplicity %u\naddress multiplicity\n", a * (a + 1) / 2);
        weighted_remainder_boundary_visit(a, print_atom, NULL);
        puts("GMP rational energy; exact reduced addresses and integer multiplicities.");
        mpq_clears(value, deficit, NULL);
        return 0;
    }
    if (argc == 5 && strcmp(argv[2], "ramp") == 0 &&
        parse_index(argv[3], 1, &a) && parse_index(argv[4], 1, &b)) {
        mpq_init(value);
        weighted_remainder_ramp_overlap_q(value, a, b);
        printf("Exact affine ramp overlap\nperiods %u %u\n", a, b);
        gmp_printf("integral %Qd\n", value);
        puts("Direct affine-cell integration with GMP rational arithmetic.");
        mpq_clear(value);
        return 0;
    }
    if (argc == 5 && strcmp(argv[2], "amplitude") == 0 &&
        parse_index(argv[3], 2, &a) && parse_index(argv[4], 2, &b)) {
        mpq_inits(value, deficit, NULL);
        weighted_remainder_amplitude_interval_q(value, deficit, a, b);
        printf("Full conductor amplitude enclosure\nconductor %u; period cutoff %u\n", a, b);
        gmp_printf("lower %Qd\nupper %Qd\n", value, deficit);
        mpq_sub(deficit, deficit, value);
        gmp_printf("width %Qd\n", deficit);
        puts("Exact rational endpoints; the width is the omitted unit mass.");
        puts("The lower endpoint is eta(q,M); the interval contains the full eta(q).");
        mpq_clears(value, deficit, NULL);
        return 0;
    }
    fputs("Use boundary <resolution 0..240>, ramp <first 1..240> <second 1..240>, or amplitude <conductor 2..240> <cutoff 2..240>.\n", stderr);
    return 1;
}
