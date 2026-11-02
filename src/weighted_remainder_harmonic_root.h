#ifndef NFIELD_WEIGHTED_REMAINDER_HARMONIC_ROOT_H
#define NFIELD_WEIGHTED_REMAINDER_HARMONIC_ROOT_H

#include "weighted_remainder_complex.h"

/* Rational z in the closed unit disk. Each canonical input numerator and
 * positive denominator has at most 63 bits; N=1..240. The finite power
 * series is exact, while the separate binary logarithmic tail encloses
 * the full harmonic polylogarithm. z=0 is exactly zero. Input mpq values
 * may alias output fields. Rejections preserve the whole initialized out. */
typedef struct {
    unsigned cutoff,binary_exponent;
    mpq_t z_real,z_imag,tail_upper;
    WeightedRemainderComplex prefix,value;
} WeightedRemainderHarmonicPolylog;
void weighted_remainder_harmonic_polylog_init(WeightedRemainderHarmonicPolylog *out);
void weighted_remainder_harmonic_polylog_clear(WeightedRemainderHarmonicPolylog *out);
int weighted_remainder_harmonic_polylog_compute(WeightedRemainderHarmonicPolylog *out,
    const mpq_t z_real,const mpq_t z_imag,unsigned N);

/* Root exp(2*pi*i*a/q), q=1..240, 0<=a<q, N,K=1..240 independent.
 * Harmonic, cubic cosine and quadratic sine prefixes and full intervals.
 * The root-identity RHS is evaluated separately with zeta cutoff K.
 * Angles are represented by the exact rational phase a/q, including
 * a=0. No branch-dependent logarithm is evaluated by this interface. */
typedef struct {
    unsigned denominator,numerator,cutoff,zeta_cutoff,binary_exponent;
    WeightedRemainderComplex phase,harmonic_prefix,harmonic;
    mpq_t harmonic_tail_upper,cubic_prefix_lower,cubic_prefix_upper,cubic_tail_upper;
    mpq_t cubic_lower,cubic_upper,sine_prefix_lower,sine_prefix_upper,sine_tail_upper,sine_lower,sine_upper;
    mpq_t zeta_lower,zeta_upper,angle_weight_lower,angle_weight_upper,identity_lower,identity_upper;
} WeightedRemainderHarmonicRoot;
void weighted_remainder_harmonic_root_init(WeightedRemainderHarmonicRoot *out);
void weighted_remainder_harmonic_root_clear(WeightedRemainderHarmonicRoot *out);
int weighted_remainder_harmonic_root_compute(WeightedRemainderHarmonicRoot *out,
    unsigned q,unsigned a,unsigned N,unsigned K);

/* Actual finite root average of the harmonic prefix, retaining its raw
 * complex rectangle, and the exact root-selected positive prefix F_N(q).
 * Full F(q) interval uses positivity and the harmonic tail separately.
 * q,N=1..240. Every failure preserves the initialized output. */
typedef struct {
    unsigned modulus,cutoff,binary_exponent;
    WeightedRemainderComplex root_average_prefix;
    mpq_t selected_prefix,tail_upper,lower,upper;
} WeightedRemainderHarmonicRootAverage;
void weighted_remainder_harmonic_root_average_init(WeightedRemainderHarmonicRootAverage *out);
void weighted_remainder_harmonic_root_average_clear(WeightedRemainderHarmonicRootAverage *out);
int weighted_remainder_harmonic_root_average_compute(WeightedRemainderHarmonicRootAverage *out,
    unsigned q,unsigned N);

/* Literal finite sine transform and separate cotangent RHS; q=1..240,
 * arbitrary signed GMP frequency reduced modulo q. All four outputs must
 * be distinct, initialized; rejection preserves them. Multiples of q,
 * including every frequency at q=1, yield exact zeros on both sides. */
int weighted_remainder_sine_transform_q(mpq_t lower,mpq_t upper,
    mpq_t rhs_lower,mpq_t rhs_upper,unsigned q,const mpz_t frequency);

#endif
