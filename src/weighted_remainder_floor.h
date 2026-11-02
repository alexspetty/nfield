#ifndef NFIELD_WEIGHTED_REMAINDER_FLOOR_H
#define NFIELD_WEIGHTED_REMAINDER_FLOOR_H

#include "weighted_remainder_exact.h"

/* Exact F_p([address]_(p^2)) from the original two floor lists.
 * Prime p is 2..239; addresses accept every signed long long and are
 * reduced before multiplication. Nonunits and midpoint jump values are
 * retained. Initialize the GMP output; invalid input preserves it. */
int weighted_remainder_floor_q(mpq_t out, unsigned prime, long long address);

/* Separately compute F_p([(1-p)*address]_(p^2)) and
 * 2*sum_(1<=r<p) saw(r*address/p^2). Outputs must be distinct initialized
 * GMP rationals. Invalid input preserves both. The p=2 case extends the
 * paper's odd-prime domain and is covered by the same Lean theorem. */
int weighted_remainder_straightening_q(mpq_t floor_value, mpq_t midpoint_value,
                                       unsigned prime, long long address);
int weighted_remainder_floor_command(int argc, char **argv);

#endif
