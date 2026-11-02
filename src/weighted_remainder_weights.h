#ifndef NFIELD_WEIGHTED_REMAINDER_WEIGHTS_H
#define NFIELD_WEIGHTED_REMAINDER_WEIGHTS_H

#include "weighted_remainder_exact.h"

/* Exact finite arrays, without implicit normalization. Weights[0..cutoff]
 * must be initialized canonical GMP rationals, with weights[0]=weights[1]=0.
 * Signed weights are allowed for finite algebra; they are not probabilities.
 * The general infinite probability-weight criterion additionally requires
 * nonnegative weights and unit mass. The two flags report those properties
 * separately. The finite increment is (2/3)*(mass-divisor_forcing).
 * All ages and variances are finite-cutoff quantities. */
typedef struct {
    unsigned cutoff;
    int nonnegative, unit_mass;
    mpq_t mass, first_moment, raw_age, stationary_age, centered_age;
    mpq_t divisor_forcing, increment, gram_variance, jordan_variance;
} WeightedRemainderWeights;

void weighted_remainder_weights_init(WeightedRemainderWeights *state);
void weighted_remainder_weights_clear(WeightedRemainderWeights *state);

/* Cutoff 2..240; arbitrary signed GMP address. Invalid input preserves the
 * initialized output. All inputs are consumed before outputs change; address
 * may alias a numerator/denominator in out. */
int weighted_remainder_weights_compute(WeightedRemainderWeights *out,
                                       const mpq_t *weights, unsigned cutoff,
                                       const mpz_t address);

/* Exact finite multiple-weight amplitude for a conductor 2..240. A conductor
 * above cutoff gives zero. The initialized output is unchanged on failure. */
int weighted_remainder_weights_amplitude_q(mpq_t out, const mpq_t *weights,
                                           unsigned cutoff, unsigned conductor);

/* Actual completed energy for finite nonnegative unit weights at a
 * nonnegative GMP resolution: N/3+(2/3)*sum k*v_k*floor(N/k).
 * Rejects nonunit or negative weights and negative resolutions, preserving
 * the initialized output. Input/output-limb overlap is allowed. */
int weighted_remainder_weights_energy_q(mpq_t out, const mpq_t *weights,
                                        unsigned cutoff, const mpz_t resolution);

/* The manuscript's family w+epsilon*(1_2-2*1_3+1_4), through cutoff 4..240.
 * Epsilon is canonical rational and satisfies 0<abs(epsilon)<1/24.
 * Output is an initialized array [0..cutoff]. Failure preserves all entries.
 * Epsilon may alias an output; it is consumed before output changes.
 * The full infinite tail is unchanged; this finite prefix is not unit mass. */
int weighted_remainder_perturbed_weights_q(mpq_t *out, unsigned cutoff,
                                          const mpq_t epsilon);

/* Exact full original and perturbed deficit at a resolution 0..240, using
 * the capacity computation and the proved finite perturbation identity.
 * Epsilon has the same strict domain as above. Distinct initialized outputs
 * are preserved on failure; epsilon may alias an output. */
int weighted_remainder_perturbed_deficit_q(mpq_t original, mpq_t perturbed,
                                          unsigned resolution, const mpq_t epsilon);

/* Finite collision variance V, a proved squared L2 cutoff error E,
 * a rational u with u^2>=V*E, and upper=V+2*u+E for the full Haar variance.
 * E=256*(b+1)^2/M, where b is the least integer with 2*M<=2^b.
 * u is rounded upward to the grid 1/M^2 using exact integer square roots.
 * Cutoff 2..240. Four initialized rational outputs must be distinct and
 * binary_exponent must be nonnull. Failure preserves every output.
 * The interval [V,upper] uses the proved collision cutoff bound; it does
 * not replace a limiting L2 function with an integer point value. */
int weighted_remainder_collision_variance_q(mpq_t finite, mpq_t squared_error,
                                           mpq_t cross_upper, mpq_t full_upper,
                                           unsigned *binary_exponent, unsigned cutoff);

int weighted_remainder_weights_command(int argc, char **argv);

#endif
