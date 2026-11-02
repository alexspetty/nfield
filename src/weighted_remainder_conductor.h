#ifndef NFIELD_WEIGHTED_REMAINDER_CONDUCTOR_H
#define NFIELD_WEIGHTED_REMAINDER_CONDUCTOR_H

#include "weighted_remainder_exact.h"

/* Full-amplitude conductor objects. All rational endpoints are exact.
 * 2<=Q,M<=240; M is the retained period cutoff, Q the conductor cutoff.
 * M may be smaller than Q. Initialized outputs must be pairwise distinct.
 * A failure leaves outputs unchanged. Signed addresses may have any size,
 * including an address stored in an output rational's numerator/denominator.
 * The latter is consumed completely before any output changes. */
int weighted_remainder_conductor_period_z(mpz_t period, unsigned Q);
int weighted_remainder_beta_interval_q(mpq_t lower, mpq_t upper,
                                       unsigned d, unsigned Q, unsigned M);
int weighted_remainder_conductor_interval_q(mpq_t f_lower, mpq_t f_upper,
                                            mpq_t v_lower, mpq_t v_upper,
                                            mpq_t gap_lower, mpq_t gap_upper,
                                            unsigned Q, const mpz_t address, unsigned M);

/* The actual CRT address 0 mod L_Q/p and 1 mod p. Requires 3<=Q<=240,
 * p prime, Q/2<p<=Q; result is the interior representative modulo L_Q. */
int weighted_remainder_prime_candidate_z(mpz_t address, unsigned Q, unsigned p);

/* Enumerate the entire restricted residue set 1..L_Q-2. The resource cap
 * applies to L_Q, not to any theorem. The full minimum lies in [lower,upper].
 * witness attains the least computed upper endpoint. Every true minimizer
 * occurs among the possible_count addresses whose lower endpoint <= upper.
 * A single possible address therefore certifies the unique minimizer.
 * The optional visitor receives every possible address in ascending order;
 * its rational arguments are borrowed and must not be changed or retained.
 * Returning zero aborts with failure and leaves function outputs unchanged.
 * witness and possible_count must be nonnull, distinct initialized objects.
 * The callback's own side effects are not rolled back on an aborted visit. */
#define WEIGHTED_REMAINDER_CONDUCTOR_ENUM_MAX 50000
typedef int (*WeightedConductorVisitor)(unsigned residue, const mpq_t lower,
                                       const mpq_t upper, void *context);
int weighted_remainder_conductor_extrema_q(mpq_t lower, mpq_t upper,
                                           unsigned *witness, unsigned *possible_count,
                                           unsigned Q, unsigned M,
                                           WeightedConductorVisitor visit, void *context);

int weighted_remainder_conductor_command(int argc, char **argv);

#endif
