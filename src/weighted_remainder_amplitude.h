#ifndef NFIELD_WEIGHTED_REMAINDER_AMPLITUDE_H
#define NFIELD_WEIGHTED_REMAINDER_AMPLITUDE_H

#include "weighted_remainder_exact.h"

/* Exact local factors Delta(q) and J3(q), including q=1. q=1..240;
 * initialized outputs must be distinct. Failures preserve outputs. */
int weighted_remainder_amplitude_factors_q(mpq_t delta, mpq_t jordan,
                                           unsigned q);

/* Positive cubic sum through N with a proved tail <=1/(2*N^2).
 * N=1..240; initialized outputs must be distinct. No floating endpoints. */
int weighted_remainder_zeta_three_interval_q(mpq_t lower, mpq_t upper,
                                             unsigned N);

/* Literal positive harmonic seed sum over n<=M divisible by q:
 * H_(n-1)/n^2. q=1..240; M=0..240. This is a finite prefix. */
int weighted_remainder_harmonic_seed_prefix_q(mpq_t out, unsigned q, unsigned M);

/* Full seed/amplitude readout with independent cutoffs: q=1..240,
 * period M=2..240, cubic N=1..240, Mobius D=1..240. eta_1=1 is explicit;
 * retained_amplitude is always the finite period mass, including q=1.
 * Initial full amplitude bounds use positive period masses, omitted unit
 * mass, the proved period-specific tail and binary conductor bound. Full harmonic seed bounds
 * then use the exact Jordan budget and the independent cubic enclosure.
 * Refinement and Mobius intervals retain raw signed numerator bounds.
 * They enclose the full amplitude, not a finite identity with eta replaced
 * by its prefix. prime_lower/upper are available only when prime=1.
 * Initialize/clear once. Every invalid call preserves the whole output. */
typedef struct {
    unsigned conductor, period_cutoff, zeta_cutoff, mobius_cutoff;
    unsigned binary_exponent, prime, period_binary_exponent;
    mpq_t delta, jordan_three, zeta_lower, zeta_upper, zeta_tail;
    mpq_t retained_amplitude, amplitude_lower, amplitude_upper, conductor_upper;
    mpq_t seed_prefix, seed_budget_lower, seed_lower, seed_upper, seed_tail_upper;
    mpq_t refinement_numerator_lower, refinement_numerator_upper;
    mpq_t refinement_lower, refinement_upper;
    mpq_t jordan_sum_lower, jordan_sum_upper, jordan_rhs_lower, jordan_rhs_upper;
    mpq_t mobius_prefix_lower, mobius_prefix_upper, mobius_tail_upper;
    mpq_t mobius_lower, mobius_upper, prime_lower, prime_upper;
    mpq_t period_tail_bound, period_tail_upper;
} WeightedRemainderAmplitude;

void weighted_remainder_amplitude_init(WeightedRemainderAmplitude *out);
void weighted_remainder_amplitude_clear(WeightedRemainderAmplitude *out);
int weighted_remainder_amplitude_refinement_compute(WeightedRemainderAmplitude *out,
    unsigned q, unsigned M, unsigned N, unsigned D);
int weighted_remainder_amplitude_command(int argc, char **argv);

#endif
