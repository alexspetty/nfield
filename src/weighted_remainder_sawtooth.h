#ifndef NFIELD_WEIGHTED_REMAINDER_SAWTOOTH_H
#define NFIELD_WEIGHTED_REMAINDER_SAWTOOTH_H

#include "weighted_remainder_exact.h"

/* Periods are 1..240. Slopes and residue labels accept every long long,
 * reduced before multiplication, including LLONG_MIN. Slopes must be
 * units at their original periods. Period one has its unique zero row.
 * All outputs are initialized GMP rationals; failure preserves them. */
int weighted_remainder_sawtooth_q(mpq_t out, unsigned period,
                                  long long slope, long long residue);
/* The unnormalized sum of midpoint-sawtooth products over all residues. */
int weighted_remainder_dedekind_q(mpq_t out, unsigned period, long long slope);
/* The exact Haar average for the two rows, with no coprimality condition
 * on the pair of periods. Computed on their gcd by the proved pairing. */
int weighted_remainder_sawtooth_gram_q(mpq_t out, unsigned first_period,
                                       long long first_slope,
                                       unsigned second_period,
                                       long long second_slope);
/* The actual conditional mean on residue mod q; q must divide period. */
int weighted_remainder_sawtooth_mean_q(mpq_t out, unsigned period,
                                       long long slope, unsigned q,
                                       long long residue);
int weighted_remainder_sawtooth_command(int argc, char **argv);

#endif
