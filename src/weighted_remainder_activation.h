#ifndef NFIELD_WEIGHTED_REMAINDER_ACTIVATION_H
#define NFIELD_WEIGHTED_REMAINDER_ACTIVATION_H

#include <gmp.h>
#include <stddef.h>

/* Resource limit for exhaustive finite cubes, not for the Lean theorem. */
#define WEIGHTED_REMAINDER_ACTIVATION_MAX 12

typedef struct {
    unsigned dimension, interval_count;
    /* minimum_increment is zero when dimension=0 (there are no edges). */
    mpq_t minimum_increment, probability_sum, event_probability;
    mpq_t coupled_probability, active_mean, active_variance;
    mpq_t sperner_bound, universal_bound_squared;
} WeightedActivationResult;

void weighted_remainder_activation_init(WeightedActivationResult *out);
void weighted_remainder_activation_clear(WeightedActivationResult *out);

/* b has n entries, values has exactly 2^n entries in bit-mask order:
 * bit i is coordinate i. All input rationals must be canonical, with a
 * positive denominator. Requires 0<=b_i<=1/2, a>0, v-u<a and every upward
 * edge increment >=a, including edges of probability zero. An empty
 * interval is allowed. n=0 has one value and permits b=NULL, nb=0.
 *
 * Compute the exact closed-interval mass and the independent 2b activation
 * mixture of fair conditional masses; check equality, the actual interval
 * antichain, and its mixture of exact Sperner bounds. The last field is
 * 400/(1+sum b_i), the square of the separately proved universal bound.
 * No floating approximation or infinite distribution is computed.
 *
 * out must be initialized. Failure preserves every output field. Inputs
 * may alias its rational fields: all computation finishes before mutation.
 * Null required pointers, wrong lengths and invalid domains are rejected.
 */
int weighted_remainder_activation_q(WeightedActivationResult *out, unsigned n,
    const mpq_t *b, size_t nb, const mpq_t *values, size_t nvalues,
    const mpq_t a, const mpq_t u, const mpq_t v);

int weighted_remainder_activation_command(int argc, char **argv);

#endif
