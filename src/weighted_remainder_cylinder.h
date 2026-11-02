#ifndef NFIELD_WEIGHTED_REMAINDER_CYLINDER_H
#define NFIELD_WEIGHTED_REMAINDER_CYLINDER_H

#include "weighted_remainder_exact.h"

/* Exact finite rational centers for the full Haar cylinder mean and scale.
 * 1<=modulus<=240, 2<=cutoff<=240; signed address is reduced modulo modulus.
 * alignment=sum w_k*(gcd(k,L)-1)/3, mean=sum 2*w_k*E_gcd(k,L)(a)/3,
 * omitted_mass=1-sum w_k, radius=(L-1)*omitted_mass/3, with k=2..cutoff.
 * The full alignment lies in [alignment,alignment+radius], and the full
 * mean lies in [mean-radius,mean+radius]. These are proved Lean enclosures.
 * Outputs must be initialized and pairwise distinct. They may contain the
 * address input's mpz object; all inputs are consumed before outputs change.
 * Every failure preserves all output objects. Resource limits are finite
 * implementation bounds, not restrictions on the universal theorems. */
int weighted_remainder_cylinder_q(mpq_t alignment, mpq_t mean, mpq_t radius,
                                  mpq_t omitted_mass, unsigned modulus,
                                  const mpz_t address, unsigned cutoff);

/* Intervals for the full normalized mean relative position and the full
 * probability of relative position strictly exceeding threshold, plus an
 * upper bound on normalized probability at periods beyond cutoff.
 * 2<=modulus<=cutoff<=240 ensures the finite denominator is positive.
 * threshold may be any canonical GMP rational with positive denominator;
 * output objects may alias threshold. Pairwise distinct initialized outputs
 * and unchanged-on-failure behavior are required as above. */
int weighted_remainder_position_q(mpq_t gap_lower, mpq_t gap_upper,
                                  mpq_t event_lower, mpq_t event_upper,
                                  mpq_t omitted_upper, unsigned modulus,
                                  const mpz_t address, unsigned cutoff,
                                  const mpq_t threshold);

/* Exact relative residue and interval for one full period probability.
 * 2<=modulus<=cutoff<=240, 0<=period<=240; period may exceed cutoff.
 * gcd=1 and periods 0,1 have zero probability. Relative residue is zero
 * when gcd=1. The three initialized outputs must be pairwise distinct. */
int weighted_remainder_position_weight_q(mpq_t lower, mpq_t upper, mpq_t relative,
                                         unsigned modulus, const mpz_t address,
                                         unsigned period, unsigned cutoff);

int weighted_remainder_cylinder_command(int argc, char **argv);

#endif
