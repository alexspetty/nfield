#ifndef NFIELD_WEIGHTED_REMAINDER_COTANGENT_H
#define NFIELD_WEIGHTED_REMAINDER_COTANGENT_H

#include "weighted_remainder_amplitude.h"

/* Literal C(q) and unit C(q) prefixes through N. q=1..240, N=0..240.
 * Multiples of q are omitted; both prefixes at q=1 are zero. Four
 * initialized distinct outputs; invalid calls preserve every output. */
int weighted_remainder_cotangent_prefix_q(mpq_t lower,mpq_t upper,
    mpq_t unit_lower,mpq_t unit_upper,unsigned q,unsigned N);

/* q=1..240; N=1..240 is the cotangent series cutoff; K=1..240 is
 * the independent cubic-zeta cutoff. Residue maxima give the separate
 * absolute tails. Gcd/Mobius PREFIX descent uses floor(N*d/q) and
 * floor(N/d), respectively. FULL descent uses cutoff N for each divisor
 * series, with that series' own tail. Raw signed intervals are retained.
 * harmonic_seed encloses F(q) via its root-average cotangent formula.
 * eta at q=1 is explicitly one; otherwise it uses the unit cotangent
 * amplitude formula. Initialize/clear once; failures preserve all fields. */
typedef struct {
    unsigned modulus, cutoff, zeta_cutoff;
    mpq_t residue_bound, unit_residue_bound;
    mpq_t prefix_lower,prefix_upper,unit_prefix_lower,unit_prefix_upper;
    mpq_t tail_upper,unit_tail_upper,lower,upper,unit_lower,unit_upper;
    mpq_t gcd_prefix_lower,gcd_prefix_upper,mobius_prefix_lower,mobius_prefix_upper;
    mpq_t gcd_lower,gcd_upper,mobius_lower,mobius_upper;
    mpq_t zeta_lower,zeta_upper,delta,harmonic_seed_lower,harmonic_seed_upper,eta_lower,eta_upper;
} WeightedRemainderCotangent;

void weighted_remainder_cotangent_init(WeightedRemainderCotangent *out);
void weighted_remainder_cotangent_clear(WeightedRemainderCotangent *out);
int weighted_remainder_cotangent_compute(WeightedRemainderCotangent *out,
    unsigned q,unsigned N,unsigned K);

#endif
