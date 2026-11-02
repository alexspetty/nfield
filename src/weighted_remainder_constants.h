#ifndef NFIELD_WEIGHTED_REMAINDER_CONSTANTS_H
#define NFIELD_WEIGHTED_REMAINDER_CONSTANTS_H

#include "weighted_remainder_amplitude.h"

/* Natural logarithm of n=1..240. A proved binary-reduced 24-term odd
 * polynomial supplies exact rational bounds, rounded outward on grid
 * 10^-24. Initialized outputs must be distinct; failures preserve them. */
int weighted_remainder_log_interval_q(mpq_t lower, mpq_t upper, unsigned n);

/* Natural logarithm of any positive canonical rational whose numerator
 * and denominator each have at most 256 bits. Signed binary reduction
 * handles inputs below one. Same 24-term kernel and 10^-24 outward grid
 * as above. Distinct initialized outputs; either may alias x. Rejected
 * calls preserve both outputs, including malformed rationals. */
int weighted_remainder_rational_log_interval_q(mpq_t lower,mpq_t upper,const mpq_t x);

/* Constants for the uniform amplitude expansion. N=1..240 independently
 * limits the cubic zeta prefix, gamma harmonic index and log-square
 * moment prefix. Every endpoint is an exact rational. Prefixes remain
 * finite; log_moment_tail_upper encloses the omitted infinite series.
 * Initialize/clear once. Invalid computations preserve the whole output. */
typedef struct {
    unsigned cutoff, log_tail_binary_exponent;
    mpq_t pi_lower, pi_upper;
    mpq_t zeta_two_lower, zeta_two_upper, zeta_three_lower, zeta_three_upper;
    mpq_t zeta_four_lower, zeta_four_upper;
    mpq_t gamma_harmonic_prefix, log_n_lower, log_n_upper, gamma_lower, gamma_upper;
    mpq_t log_moment_prefix_lower, log_moment_prefix_upper, log_moment_tail_upper;
    mpq_t log_moment_lower, log_moment_upper, kappa_lower, kappa_upper;
    mpq_t leading_lower, leading_upper;
} WeightedRemainderConstants;

void weighted_remainder_constants_init(WeightedRemainderConstants *out);
void weighted_remainder_constants_clear(WeightedRemainderConstants *out);
int weighted_remainder_constants_compute(WeightedRemainderConstants *out,
                                          unsigned N);

#endif
