#ifndef NFIELD_WEIGHTED_REMAINDER_EXPANSION_H
#define NFIELD_WEIGHTED_REMAINDER_EXPANSION_H

#include "weighted_remainder_constants.h"

/* q=1..240 and independent constant cutoff N=1..240. The harmonic
 * expansion is available for every admitted q. The uniform amplitude
 * expansion requires q>=2 and is marked by amplitude_expansion_available;
 * its fields stay zero at q=1. Prime-power fields apply when prime_base>0;
 * prime-leading fields apply only when prime_exponent=1.
 * All interval endpoints are exact rationals. Raw signed harmonic-error
 * endpoints remain separate from their proved negative-range intersection.
 * Initialize/clear once; invalid calls preserve the complete output. */
typedef struct {
    unsigned conductor, amplitude_expansion_available, prime_base, prime_exponent;
    WeightedRemainderConstants constants;
    mpq_t delta, jordan_three, totient_ratio, rho, prime_factor_plus_product;
    mpq_t log_lower, log_upper, nu_lower, nu_upper;
    mpq_t mobius_inverse, mobius_log_lower, mobius_log_upper;
    mpq_t harmonic_prefix, harmonic_error_raw_lower, harmonic_error_raw_upper;
    mpq_t harmonic_error_lower, harmonic_error_upper, harmonic_error_bound;
    mpq_t seed_main_lower, seed_main_upper, seed_error_bound, seed_lower, seed_upper;
    mpq_t main_lower, main_upper, error_upper, amplitude_lower, amplitude_upper;
    mpq_t prime_power_main_lower, prime_power_main_upper;
    mpq_t prime_leading_lower, prime_leading_upper;
} WeightedRemainderExpansion;

void weighted_remainder_expansion_init(WeightedRemainderExpansion *out);
void weighted_remainder_expansion_clear(WeightedRemainderExpansion *out);
int weighted_remainder_expansion_compute(WeightedRemainderExpansion *out,
                                          unsigned q, unsigned N);

int weighted_remainder_expansion_command(int argc, char **argv);

#endif
