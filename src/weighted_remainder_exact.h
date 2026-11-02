#ifndef NFIELD_WEIGHTED_REMAINDER_EXACT_H
#define NFIELD_WEIGHTED_REMAINDER_EXACT_H

#include <gmp.h>

/* Resource bound for these finite algorithms, not a mathematical restriction.
 * mpq outputs must be initialized by the caller. Failure leaves them unchanged. */
#define WEIGHTED_REMAINDER_EXACT_MAX 240

typedef int (*WeightedBoundaryVisitor)(unsigned numerator, unsigned denominator,
                                      unsigned multiplicity, void *context);

int weighted_remainder_weight_q(mpq_t out, unsigned period);
int weighted_remainder_capacity_q(mpq_t out, unsigned resolution);
int weighted_remainder_ramp_overlap_q(mpq_t out, unsigned first, unsigned second);
int weighted_remainder_midpoint_q(mpq_t out, unsigned period, const mpq_t phase);
int weighted_remainder_response_q(mpq_t out, unsigned resolution, const mpq_t phase);
/* Enclose the full infinite amplitude using exact omitted unit mass.
 * 2<=conductor,cutoff<=240; conductor may exceed cutoff. Output objects
 * must be distinct and initialized. Failure preserves both outputs. */
int weighted_remainder_amplitude_interval_q(mpq_t lower, mpq_t upper,
                                            unsigned conductor, unsigned cutoff);
/* Enumerate distinct rational atoms j/r in denominator/numerator order.
 * A visitor returning zero stops enumeration and makes the function fail. */
int weighted_remainder_boundary_visit(unsigned resolution,
                                     WeightedBoundaryVisitor visit, void *context);
int weighted_remainder_exact_command(int argc, char **argv);

#endif
