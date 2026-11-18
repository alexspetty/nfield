#ifndef NFIELD_WEIGHTED_REMAINDER_POWER_H
#define NFIELD_WEIGHTED_REMAINDER_POWER_H

#include "weighted_remainder_constants.h"

/* Exact rational enclosure of n^(-s), n=1..240, canonical GMP rational
 * 0<=s<=12, numerator and denominator at most 256 bits each. Integer s
 * is exact. Otherwise use the proved logarithm interval, degree-23 exp
 * polynomial after division by 128, and seven outward-rounded squarings.
 * Exp steps use a 10^-24 grid; final reciprocals are rounded outward on
 * a 10^-48 grid to keep positive series sums tractable. Initialized outputs must be distinct;
 * either may alias s. Invalid input preserves both outputs. */
int weighted_remainder_power_interval_q(mpq_t lower, mpq_t upper,
                                        unsigned n, const mpq_t s);

/* Enclose exp(x) for every x in [a,b], with canonical rational
 * 0<=a<=b<=1, at most 256 bits per numerator/denominator. The proved
 * degree-23 polynomial and exact uniform remainder are rounded outward
 * on grid 10^-24, with the lower endpoint at least one. Distinct
 * initialized outputs may alias inputs. Failures preserve both outputs. */
int weighted_remainder_small_exp_interval_q(mpq_t lower,mpq_t upper,
    const mpq_t a,const mpq_t b);

#endif
