#ifndef NFIELD_WEIGHTED_REMAINDER_FOURIER_H
#define NFIELD_WEIGHTED_REMAINDER_FOURIER_H

#include "weighted_remainder_exact.h"

/* Rational enclosures, using the proved degree-23 quarter-angle exponential
 * polynomial, two squarings, and the proved 20-decimal pi bracket. Only the
 * sine/cosine endpoints are rounded, outward to a 10^-18 grid. Every later
 * operation is exact rational interval arithmetic. No floating endpoints.
 * Frequencies are reduced modulo q from arbitrary signed GMP integers.
 * Kernel: 2<=q<=240, residue nonzero (nonunits allowed). At a/q=1/2 the
 * exact values are used. Initialize/clear once. Failure preserves outputs;
 * input addresses may occupy any output rational numerator/denominator. */
#define WEIGHTED_REMAINDER_FOURIER_DECIMALS 18
typedef struct {
    unsigned conductor, residue;
    mpq_t sin_lower, sin_upper, cos_lower, cos_upper;
    mpq_t cot_lower, cot_upper, csc_squared_lower, csc_squared_upper;
} WeightedRemainderTrig;

void weighted_remainder_trig_init(WeightedRemainderTrig *out);
void weighted_remainder_trig_clear(WeightedRemainderTrig *out);
int weighted_remainder_trig_compute(WeightedRemainderTrig *out,
                                     unsigned q, const mpz_t frequency);

/* Primitive reduced frequency a/q only: gcd(a,q)=1, q>=2. Bounds enclose
 * ghat=-2*amplitude/3, Yhat=-amplitude/3+i*amplitude*cot(pi*a/q)/3,
 * and their squared moduli. Supplied amplitude intervals may be signed.
 * mode: 0 supplied interval, 1 finite masses, 2 full collision amplitude.
 * Finite and full collision cutoffs are 2..240; q may exceed cutoff.
 * Initialized output and all input rationals may overlap. Invalid calls
 * preserve the entire output; canonical rational inputs are required. */
typedef struct {
    unsigned cutoff, mode;
    WeightedRemainderTrig trig;
    mpq_t amplitude_lower, amplitude_upper, g_lower, g_upper;
    mpq_t y_real_lower, y_real_upper, y_imag_lower, y_imag_upper;
    mpq_t g_mass_lower, g_mass_upper, y_mass_lower, y_mass_upper;
} WeightedRemainderFourier;

void weighted_remainder_fourier_init(WeightedRemainderFourier *out);
void weighted_remainder_fourier_clear(WeightedRemainderFourier *out);
int weighted_remainder_fourier_interval_compute(WeightedRemainderFourier *out,
    unsigned q, const mpz_t frequency, const mpq_t lower, const mpq_t upper);
int weighted_remainder_fourier_finite_compute(WeightedRemainderFourier *out,
    unsigned M, unsigned q, const mpz_t frequency, const mpq_t *weights);
int weighted_remainder_fourier_collision_compute(WeightedRemainderFourier *out,
    unsigned M, unsigned q, const mpz_t frequency, int full);

/* Fourier coefficient of the actual conductor-p rows at primitive a/q.
 * p,q in 2..240. P's real part and c's real coefficient are exact; both
 * P and R have imaginary part in [imag_lower,imag_upper]. R's real part
 * and c's imaginary part are zero. All vanish when p!=q. Four initialized
 * outputs must be distinct; frequency/output-limb overlap is allowed. */
int weighted_remainder_row_fourier_q(mpq_t p_real, mpq_t imag_lower,
    mpq_t imag_upper, mpq_t c_real, unsigned p, unsigned q,
    const mpz_t frequency);

int weighted_remainder_fourier_command(int argc, char **argv);

#endif
