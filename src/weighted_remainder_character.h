#ifndef NFIELD_WEIGHTED_REMAINDER_CHARACTER_H
#define NFIELD_WEIGHTED_REMAINDER_CHARACTER_H

#include "weighted_remainder_complex.h"

/* q=2..240, N=1..240; index refers to the full FiniteCharacterTable,
 * including induced characters. Only odd indices are admitted. The
 * coefficient is sum_a conjugate(chi(a))*cot(pi*a/q). Its pi/(2q)
 * multiple encloses the naturally ordered L(1,conjugate chi).
 * L(2,chi) has a finite prefix through N and a separate norm tail 1/N.
 * Initialize/clear once; every rejected call preserves every field. */
typedef struct {
    unsigned modulus, index, conductor, denominator, cutoff;
    WeightedRemainderComplex cotangent_coefficient, l_one_conjugate;
    WeightedRemainderComplex l_two_prefix, l_two, mixed_product;
    mpq_t l_two_tail;
} WeightedRemainderCharacter;

void weighted_remainder_character_init(WeightedRemainderCharacter *out);
void weighted_remainder_character_clear(WeightedRemainderCharacter *out);
int weighted_remainder_character_compute(WeightedRemainderCharacter *out,
    unsigned q,unsigned index,unsigned N);

/* All odd L(1,conjugate chi)*L(2,chi) products, retaining the raw
 * imaginary interval. N (L-series) and K (zeta-three) are independent.
 * No character is discarded on account of its induced conductor.
 * eta_lower/upper are the raw mixed-formula bounds; positive_amplitude
 * bounds are a separate intersection with the positive period formula
 * at the independently supplied M. q=2 is exactly one half. */
typedef struct {
    unsigned modulus, cutoff, zeta_cutoff, period_cutoff;
    unsigned character_count, odd_count, induced_odd_count;
    WeightedRemainderComplex mixed_moment;
    mpq_t delta, zeta_lower, zeta_upper, denominator_lower, denominator_upper;
    mpq_t eta_lower, eta_upper, positive_amplitude_lower, positive_amplitude_upper;
} WeightedRemainderMixedMoment;

void weighted_remainder_mixed_moment_init(WeightedRemainderMixedMoment *out);
void weighted_remainder_mixed_moment_clear(WeightedRemainderMixedMoment *out);
int weighted_remainder_mixed_moment_compute(WeightedRemainderMixedMoment *out,
    unsigned q,unsigned N,unsigned K,unsigned M);

int weighted_remainder_mixed_command(int argc,char **argv);

#endif
