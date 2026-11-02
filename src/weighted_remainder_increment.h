#ifndef NFIELD_WEIGHTED_REMAINDER_INCREMENT_H
#define NFIELD_WEIGHTED_REMAINDER_INCREMENT_H

#include "weighted_remainder_exact.h"

/* Exact covariance of the finite mean-zero increment
 * g_v(n)=(2/3)*(sum v_k-sum k*v_k*[k|n]). Signed canonical rational
 * arrays [0..M] are admitted, with v[0]=v[1]=0 and 2<=M<=240.
 * The arithmetic and Ramanujan formulas are computed separately. zero and
 * one give the same finite observable's covariance at shifts zero and one.
 * Shift is an arbitrary signed GMP integer. All four initialized outputs
 * must be distinct; invalid calls preserve them. Input/output overlap is
 * allowed: every array entry and shift is consumed before outputs change. */
int weighted_remainder_increment_covariance_q(mpq_t arithmetic, mpq_t ramanujan,
                                               mpq_t zero, mpq_t one,
                                               const mpq_t *weights, unsigned M,
                                               const mpz_t shift);

/* Collision weights through cutoff 2..240, with a rigorous interval for
 * the actual full Haar increment covariance at the supplied signed shift.
 * Let E=256*(b+1)^2/M, with b minimal such that 2*M<=2^b. The squared
 * increment cutoff error is at most 4E. With V=finite covariance at zero,
 * u is rounded upward to a 1/M^2 grid and satisfies u^2>=V*4E. The full
 * covariance lies in [finite-(2u+4E),finite+(2u+4E)].
 * The actual lcm return has squared potential displacement <=4E, and
 * full covariance loss K(0)-K(lcm) is in [0,8E]. These universal bounds
 * are proved in CollisionCovarianceEnclosure; finite sign observations
 * and exact finite periodicity are distinct from infinite recurrence.
 * Initialize/clear once. Invalid calls preserve all fields; shift may
 * occupy an output integer or rational limb. No floating endpoints. */
typedef struct {
    unsigned cutoff, binary_exponent;
    mpz_t shift, cutoff_period;
    mpq_t mass, arithmetic, ramanujan, zero, one;
    mpq_t potential_squared_error, increment_squared_error, cross_upper;
    mpq_t covariance_error, full_lower, full_upper;
    mpq_t potential_recurrence_squared_upper, covariance_recurrence_loss_upper;
} WeightedRemainderIncrement;

void weighted_remainder_increment_init(WeightedRemainderIncrement *out);
void weighted_remainder_increment_clear(WeightedRemainderIncrement *out);
int weighted_remainder_increment_compute(WeightedRemainderIncrement *out,
                                          unsigned M, const mpz_t shift);
int weighted_remainder_increment_command(int argc, char **argv);

#endif
