#ifndef NFIELD_WEIGHTED_REMAINDER_SMALL_AMPLITUDE_H
#define NFIELD_WEIGHTED_REMAINDER_SMALL_AMPLITUDE_H

#include "weighted_remainder_amplitude.h"

/* Small-modulus character examples. N,K=1..240 independently bound the
 * signed reciprocal-square and cubic-zeta series. The discriminant -3,
 * discriminant -4 (Catalan), and induced modulus-six character use their
 * actual residue tables. All finite prefixes are exact rational values.
 * induced_prefix_rhs retains the floor(N/2) cutoff; the full induced
 * L-value factor is 5/4. eta_six_direct and eta_six_relation are separate
 * evaluations of the two printed routes. Initialize/clear once; invalid
 * calls preserve the entire output. */
typedef struct {
    unsigned cutoff,zeta_cutoff;
    mpq_t three_prefix,three_lower,three_upper,catalan_prefix,catalan_lower,catalan_upper;
    mpq_t six_prefix,six_lower,six_upper,induced_prefix_rhs,induced_factor,induced_lower,induced_upper;
    mpq_t l_tail_upper,zeta_lower,zeta_upper,sqrt_three_lower,sqrt_three_upper;
    mpq_t eta_three_lower,eta_three_upper,eta_four_lower,eta_four_upper;
    mpq_t eta_six_direct_lower,eta_six_direct_upper,eta_six_relation_lower,eta_six_relation_upper;
} WeightedRemainderSmallAmplitude;
void weighted_remainder_small_amplitude_init(WeightedRemainderSmallAmplitude *out);
void weighted_remainder_small_amplitude_clear(WeightedRemainderSmallAmplitude *out);
int weighted_remainder_small_amplitude_compute(WeightedRemainderSmallAmplitude *out,
    unsigned N,unsigned K);

#endif
