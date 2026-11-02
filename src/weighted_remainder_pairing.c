/* Exact boundary readouts and certified finite Haar test approximations. */
#include "weighted_remainder_pairing.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned pairing_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned r = a % b; a = b; b = r; }
    return a;
}

static int valid_table(unsigned period, const mpq_t *real, const mpq_t *imag)
{
    if (!period || period > WEIGHTED_REMAINDER_EXACT_MAX || !real || !imag) return 0;
    for (unsigned j = 0; j < period; ++j)
        if (mpz_sgn(mpq_denref(real[j])) <= 0 || mpz_sgn(mpq_denref(imag[j])) <= 0) return 0;
    return 1;
}

int weighted_remainder_reset_q(mpq_t out, unsigned n)
{
    if (!n || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t total, weight, factor;
    mpq_inits(total, weight, factor, NULL);
    mpq_set_ui(total, 1, 1);
    for (unsigned k = 2; k <= n; ++k) if (n % k == 0) {
        weighted_remainder_weight_q(weight, k);
        mpq_set_ui(factor, k, 1);
        mpq_mul(weight, weight, factor);
        mpq_sub(total, total, weight);
    }
    mpq_set_ui(factor, 2, 3);
    mpq_mul(out, total, factor);
    mpq_clears(total, weight, factor, NULL);
    return 1;
}

int weighted_remainder_boundary_test_q(mpq_t real, mpq_t imag,
                                      unsigned length, unsigned period,
                                      const mpq_t *real_values,
                                      const mpq_t *imag_values)
{
    if (real == imag || !length || length > WEIGHTED_REMAINDER_EXACT_MAX ||
        !valid_table(period, real_values, imag_values)) return 0;
    mpq_t sum_real, sum_imag, reset, term, divisor;
    mpq_inits(sum_real, sum_imag, reset, term, divisor, NULL);
    for (unsigned n = 1; n <= length; ++n) {
        weighted_remainder_reset_q(reset, n);
        mpq_mul(term, reset, real_values[n % period]);
        mpq_add(sum_real, sum_real, term);
        mpq_mul(term, reset, imag_values[n % period]);
        mpq_sub(sum_imag, sum_imag, term);
    }
    mpq_set_ui(divisor, length, 1);
    mpq_div(sum_real, sum_real, divisor);
    mpq_div(sum_imag, sum_imag, divisor);
    /* Delay writes so output/table aliasing is safe. */
    mpq_set(real, sum_real);
    mpq_set(imag, sum_imag);
    mpq_clears(sum_real, sum_imag, reset, term, divisor, NULL);
    return 1;
}

int weighted_remainder_haar_test_q(mpq_t real, mpq_t imag,
                                  mpq_t real_radius, mpq_t imag_radius,
                                  unsigned period, unsigned cutoff,
                                  const mpq_t *real_values,
                                  const mpq_t *imag_values)
{
    if (real == imag || real == real_radius || real == imag_radius ||
        imag == real_radius || imag == imag_radius || real_radius == imag_radius ||
        cutoff < 2 || cutoff > WEIGHTED_REMAINDER_EXACT_MAX ||
        !valid_table(period, real_values, imag_values)) return 0;
    mpq_t center_real, center_imag, bound_real, bound_imag, sum_real, sum_imag;
    mpq_t weight, mass, factor, term;
    mpq_inits(center_real, center_imag, bound_real, bound_imag, sum_real, sum_imag,
              weight, mass, factor, term, NULL);
    for (unsigned j = 0; j < period; ++j) {
        mpq_add(center_real, center_real, real_values[j]);
        mpq_add(center_imag, center_imag, imag_values[j]);
        mpq_abs(term, real_values[j]);
        if (mpq_cmp(term, bound_real) > 0) mpq_set(bound_real, term);
        mpq_abs(term, imag_values[j]);
        if (mpq_cmp(term, bound_imag) > 0) mpq_set(bound_imag, term);
    }
    mpq_set_ui(factor, 1, period);
    mpq_mul(center_real, center_real, factor);
    mpq_mul(center_imag, center_imag, factor);
    for (unsigned k = 2; k <= cutoff; ++k) {
        unsigned g = pairing_gcd(k, period), lcm = k / g * period;
        weighted_remainder_weight_q(weight, k);
        mpq_add(mass, mass, weight);
        mpq_set_ui(factor, k, lcm);
        mpq_canonicalize(factor);
        mpq_mul(factor, factor, weight);
        mpq_set_ui(sum_real, 0, 1);
        mpq_set_ui(sum_imag, 0, 1);
        /* CRT: k|n and n=j (mod period) has one solution modulo lcm
         * precisely when gcd(k,period)|j. */
        for (unsigned j = 0; j < period; j += g) {
            mpq_add(sum_real, sum_real, real_values[j]);
            mpq_add(sum_imag, sum_imag, imag_values[j]);
        }
        mpq_mul(term, factor, sum_real);
        mpq_sub(center_real, center_real, term);
        mpq_mul(term, factor, sum_imag);
        mpq_sub(center_imag, center_imag, term);
    }
    mpq_set_ui(factor, 2, 3);
    mpq_mul(center_real, center_real, factor);
    mpq_mul(center_imag, center_imag, factor);
    mpq_neg(center_imag, center_imag);
    mpq_set_ui(term, 1, 1);
    mpq_sub(mass, term, mass);
    mpq_mul(mass, mass, factor);
    mpq_mul(bound_real, bound_real, mass);
    mpq_mul(bound_imag, bound_imag, mass);
    mpq_set(real, center_real);
    mpq_set(imag, center_imag);
    mpq_set(real_radius, bound_real);
    mpq_set(imag_radius, bound_imag);
    mpq_clears(center_real, center_imag, bound_real, bound_imag, sum_real, sum_imag,
               weight, mass, factor, term, NULL);
    return 1;
}

static int pairing_index(const char *text, unsigned minimum, unsigned *out)
{
    if (!text || !*text || *text == '-') return 0;
    char *end;
    errno = 0;
    unsigned long n = strtoul(text, &end, 10);
    if (errno || *end || n < minimum || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    *out = (unsigned)n;
    return 1;
}

int weighted_remainder_pairing_command(int argc, char **argv)
{
    unsigned n, period, residue, cutoff;
    if (argc == 4 && strcmp(argv[2], "reset") == 0 && pairing_index(argv[3], 1, &n)) {
        mpq_t reset;
        mpq_init(reset);
        weighted_remainder_reset_q(reset, n);
        printf("Exact boundary increment\nresolution %u\n", n);
        gmp_printf("increment %Qd\n", reset);
        mpq_clear(reset);
        return 0;
    }
    if (argc == 7 && strcmp(argv[2], "pairing") == 0 &&
        pairing_index(argv[3], 1, &n) && pairing_index(argv[4], 1, &period) &&
        pairing_index(argv[5], 0, &residue) && residue < period &&
        pairing_index(argv[6], 2, &cutoff)) {
        mpq_t real_values[WEIGHTED_REMAINDER_EXACT_MAX];
        mpq_t imag_values[WEIGHTED_REMAINDER_EXACT_MAX];
        mpq_t empirical, imag, center, radius, imag_radius, endpoint;
        mpq_inits(empirical, imag, center, radius, imag_radius, endpoint, NULL);
        for (unsigned j = 0; j < period; ++j) {
            mpq_init(real_values[j]);
            mpq_init(imag_values[j]);
            mpq_set_ui(real_values[j], j == residue, 1);
        }
        weighted_remainder_boundary_test_q(empirical, imag, n, period, real_values, imag_values);
        weighted_remainder_haar_test_q(center, imag, radius, imag_radius,
                                      period, cutoff, real_values, imag_values);
        printf("Boundary pairing with a residue indicator\nlength %u; period %u; residue %u; cutoff %u\n",
               n, period, residue, cutoff);
        gmp_printf("finite average %Qd\nHaar center %Qd\nHaar radius %Qd\n", empirical, center, radius);
        mpq_sub(endpoint, center, radius);
        gmp_printf("Haar lower %Qd\n", endpoint);
        mpq_add(endpoint, center, radius);
        gmp_printf("Haar upper %Qd\n", endpoint);
        puts("The finite average is exact. The Haar interval uses the proved omitted-mass bound.");
        for (unsigned j = 0; j < period; ++j) {
            mpq_clear(real_values[j]);
            mpq_clear(imag_values[j]);
        }
        mpq_clears(empirical, imag, center, radius, imag_radius, endpoint, NULL);
        return 0;
    }
    fputs("Use reset <resolution 1..240> or pairing <length 1..240> <period 1..240> <residue 0..period-1> <cutoff 2..240>.\n", stderr);
    return 1;
}
