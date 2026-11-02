#ifndef NFIELD_WEIGHTED_REMAINDER_PRIMITIVE_H
#define NFIELD_WEIGHTED_REMAINDER_PRIMITIVE_H

#include "weighted_remainder_exact.h"

/* Finite resource limit: 240. All rational outputs must be initialized.
 * Multiple outputs must be distinct. Failure preserves every output.
 * Node coordinates and box cutoffs are 1..240. Local node conservation
 * also holds for noncoprime coordinates. Box traversal starts at (1,1).
 * The optional node_count pointer receives the number of interior nodes. */
int weighted_remainder_tree_node_q(mpq_t potential, mpq_t left, mpq_t right,
                                   mpq_t loss, unsigned first, unsigned second);
/* The oriented address term 1/(a*(a+b)^2), for a,b=1..240. */
int weighted_remainder_tree_address_q(mpq_t out, unsigned first, unsigned second);
int weighted_remainder_tree_box_q(mpq_t mass, mpq_t frontier, mpq_t upper,
                                  unsigned cutoff, unsigned *node_count);

/* Budget: sum_{k|n} k^3*w_k, n=1..240. The inverse uses the finite
 * Mobius transform of d*H_(d-1), divided by n^3; indices 0,1 give zero. */
int weighted_remainder_budget_q(mpq_t out, unsigned resolution);
int weighted_remainder_weight_inverse_q(mpq_t out, unsigned period);
/* cutoff=0..240. Omitted mass is exactly 1 minus the retained mass;
 * the infinite unit normalization and convergence are Lean theorems. */
int weighted_remainder_mass_q(mpq_t retained, mpq_t omitted, unsigned cutoff);
/* Also return sum_{k<=M} k*w_k and the exact bound
 * (2/3)*(sum_{k<=M} k*w_k + M*omitted_mass) on D_M. */
int weighted_remainder_mass_budget_q(mpq_t retained, mpq_t omitted,
                                     mpq_t weighted_mass, mpq_t deficit_upper,
                                     unsigned cutoff);
int weighted_remainder_primitive_command(int argc, char **argv);

#endif
