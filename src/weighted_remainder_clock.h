#ifndef NFIELD_WEIGHTED_REMAINDER_CLOCK_H
#define NFIELD_WEIGHTED_REMAINDER_CLOCK_H

#include "weighted_remainder_exact.h"

/* Call init/clear exactly once around use. All sums run over 2<=k<=cutoff:
 * raw_age=(2/3) sum w_k*r_k(address), stationary_age=sum w_k*(k-1)/3,
 * centered_age=raw_age-stationary_age, and increment=raw_age(n)-raw_age(n-1).
 * All fields describe the finite cutoff, never a point value of the limiting
 * Haar L2 potential. Omitted mass is exactly one minus retained mass. */
typedef struct {
    unsigned cutoff;
    mpq_t retained_mass, omitted_mass, raw_age, stationary_age, centered_age, increment;
} WeightedRemainderClock;
void weighted_remainder_clock_init(WeightedRemainderClock *clock);
void weighted_remainder_clock_clear(WeightedRemainderClock *clock);
/* Cutoff 2..240; arbitrary signed GMP address. Failure preserves out.
 * The address may alias a numerator/denominator in out: it is consumed
 * before outputs change. Increment uses retained mass, not unit mass. */
int weighted_remainder_clock_compute(WeightedRemainderClock *out, unsigned cutoff,
                                      const mpz_t address);

/* Enumerate the exact finite law on a complete period, sorted by value.
 * Equal values are combined; probability is multiplicity/period.
 * Outputs period/distinct must be nonnull and distinct. Callback values
 * are borrowed and read-only. An aborted callback preserves outputs, but
 * its own side effects are not rolled back. A null callback is allowed. */
#define WEIGHTED_REMAINDER_CLOCK_LAW_MAX 50000
typedef int (*WeightedClockLawVisitor)(const mpq_t value, unsigned multiplicity,
                                       void *context);
int weighted_remainder_clock_law(unsigned *period, unsigned *distinct,
                                  unsigned cutoff, WeightedClockLawVisitor visit,
                                  void *context);

/* Exact orbit mass at address, stationary mass, and Cesaro mass for
 * observations 0..last (denominator last+1), at the given cycle residue.
 * Period 2..240, residue<period, arbitrary signed address and last>=0.
 * Initialized outputs must be pairwise distinct and are preserved on
 * failure. GMP inputs may alias output limbs and are consumed first. */
int weighted_remainder_cycle_q(mpq_t orbit, mpq_t stationary, mpq_t cesaro,
                                unsigned period, unsigned residue,
                                const mpz_t address, const mpz_t last);

/* Lower=half the total mass discrepancy on cycles 2..cutoff, with
 * observations 0..last. Upper=lower+omitted unit mass encloses the full
 * total variation distance. Cutoff 2..240, last>=0; distinct initialized
 * outputs, input/output aliasing allowed, unchanged outputs on failure. */
int weighted_remainder_cycle_tv_q(mpq_t lower, mpq_t upper, mpq_t omitted_mass,
                                   unsigned cutoff, const mpz_t last);

/* Exact centered remainder covariance on periods 1..240, also the
 * complete-lcm-cycle mean. Invalid input preserves initialized output. */
int weighted_remainder_clock_covariance_q(mpq_t out, unsigned first, unsigned second);

/* cutoff=0..240. Return the harmonic cross sum (H_M^2-H_M^(2))/2
 * and the Mobius expression sum_{d<=M} mu(d)/d^2 * cross_sum(floor(M/d)),
 * which equals sum_{k<=M} k*w_k. Initialized outputs must be distinct;
 * both remain unchanged on invalid input. */
int weighted_remainder_age_budget_q(mpq_t harmonic_cross, mpq_t first_moment,
                                     unsigned cutoff);
int weighted_remainder_clock_command(int argc, char **argv);

#endif
