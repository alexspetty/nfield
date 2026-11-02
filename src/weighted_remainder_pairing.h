#ifndef NFIELD_WEIGHTED_REMAINDER_PAIRING_H
#define NFIELD_WEIGHTED_REMAINDER_PAIRING_H

#include "weighted_remainder_exact.h"

/* Exact positive-integer boundary increment g(n), for 1<=n<=240. */
int weighted_remainder_reset_q(mpq_t out, unsigned n);

/* Test tables have period entries, indexed by n mod period. Entries must
 * be initialized canonical GMP rationals with positive denominators.
 * The imaginary sign implements conjugation of the complex test.
 * All output objects must be initialized and pairwise distinct. Outputs
 * may alias table entries. Every failure leaves every output unchanged.
 * 1<=length,period<=240. */
int weighted_remainder_boundary_test_q(mpq_t real, mpq_t imag,
                                      unsigned length, unsigned period,
                                      const mpq_t *real_values,
                                      const mpq_t *imag_values);

/* Exact center and separate real/imaginary error radii for the full Haar
 * pairing. The constant term is retained in full; reset terms are kept
 * through cutoff. Each radius is (2/3)*max_abs_component*omitted_unit_mass.
 * The same table/output contract applies; 1<=period<=240, 2<=cutoff<=240. */
int weighted_remainder_haar_test_q(mpq_t real, mpq_t imag,
                                  mpq_t real_radius, mpq_t imag_radius,
                                  unsigned period, unsigned cutoff,
                                  const mpq_t *real_values,
                                  const mpq_t *imag_values);

int weighted_remainder_pairing_command(int argc, char **argv);

#endif
