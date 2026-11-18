#ifndef NFIELD_WEIGHTED_REMAINDER_COMPLEX_H
#define NFIELD_WEIGHTED_REMAINDER_COMPLEX_H

#include "weighted_remainder_fourier.h"

typedef struct {
    mpq_t real_lower, real_upper, imag_lower, imag_upper;
} WeightedRemainderComplex;

void weighted_remainder_complex_init(WeightedRemainderComplex *out);
void weighted_remainder_complex_clear(WeightedRemainderComplex *out);

/* Actual exp(2*pi*i*a/q) in a rational coordinate rectangle. q=1..240,
 * 0<=a<q. Phase zero is exact; other phases use the proved half-angle
 * trigonometric kernel and signed double-angle interval arithmetic.
 * All four initialized outputs must be distinct. Every rejected input
 * preserves all outputs. No floating number supplies an endpoint. */
int weighted_remainder_complex_phase_q(mpq_t real_lower, mpq_t real_upper,
    mpq_t imag_lower, mpq_t imag_upper, unsigned q, unsigned a);

#endif
