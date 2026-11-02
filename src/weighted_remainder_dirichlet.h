#ifndef NFIELD_WEIGHTED_REMAINDER_DIRICHLET_H
#define NFIELD_WEIGHTED_REMAINDER_DIRICHLET_H

#include "weighted_remainder_power.h"

/* N(n)=2^(omega(n)-1)-1 for n>=2, with N(0)=N(1)=0.
 * Exact finite arithmetic, n=0..240. Invalid input preserves out. */
int weighted_remainder_divisor_deficit_q(mpq_t out, unsigned n);

/* The full positive series A(s)=sum_{n>=2} N(n)/n^s. Domain: canonical
 * rational 1<s<=6 with numerator/denominator at most 255 bits; N=1..240.
 * Positive prefixes, zeta integral tails and raw zeta-formula intervals
 * are separate. Specializations: 2 means s=2, 3 means s=3/2, 0 otherwise.
 * The s=2 bounds use 7/4-zeta(2) and A(2)<1/8; s=3/2 uses A(3/2)<67/80.
 * special_* is zero when specialization=0. All bounds are rational.
 * Initialize/clear once. Failures preserve the entire output. Input s may
 * alias any initialized field of out. */
typedef struct {
    unsigned cutoff, specialization;
    mpq_t exponent;
    mpq_t zeta_prefix_lower, zeta_prefix_upper, zeta_tail_upper, zeta_lower, zeta_upper;
    mpq_t doubled_prefix_lower, doubled_prefix_upper, doubled_tail_upper, doubled_lower, doubled_upper;
    mpq_t prefix_lower, prefix_upper, formula_lower, formula_upper;
    mpq_t special_lower, special_upper, lower, upper, tail_upper;
} WeightedRemainderDirichlet;

void weighted_remainder_dirichlet_init(WeightedRemainderDirichlet *out);
void weighted_remainder_dirichlet_clear(WeightedRemainderDirichlet *out);
int weighted_remainder_dirichlet_compute(WeightedRemainderDirichlet *out,
                                         const mpq_t s, unsigned N);

/* Display 100: both actual series intervals and their literal weighted
 * bound. The strict infinite margin is a Lean theorem. A finite prefix
 * is not its proof. The same N=1..240 is used in both positive sums. */
typedef struct {
    WeightedRemainderDirichlet two, three_halves;
    mpq_t two_weight, three_halves_weight, loss_lower, loss_upper;
    mpq_t margin_lower, margin_upper, literal_loss_bound, literal_margin;
} WeightedRemainderDeficitDiagnostic;

void weighted_remainder_deficit_diagnostic_init(WeightedRemainderDeficitDiagnostic *out);
void weighted_remainder_deficit_diagnostic_clear(WeightedRemainderDeficitDiagnostic *out);
int weighted_remainder_deficit_diagnostic_compute(WeightedRemainderDeficitDiagnostic *out,
                                                  unsigned N);

#endif
