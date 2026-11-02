#ifndef NFIELD_WEIGHTED_REMAINDER_SPECTRAL_H
#define NFIELD_WEIGHTED_REMAINDER_SPECTRAL_H

#include "weighted_remainder_constants.h"

/* Exact local h(p) and Euler factor 1+(h(p)-1)/p; p must be prime, 2..240.
 * Paired initialized outputs must be distinct. Failure preserves both. */
int weighted_remainder_spectral_factors_q(mpq_t local, mpq_t euler, unsigned p);

/* Exact h(n)=J2(n)*rho(n)^2/n^2 and its divisor-convolution correction c(n).
 * n=0..240; h(0)=c(0)=0, h(1)=c(1)=1. c is supported on squarefree n.
 * Paired initialized outputs must be distinct. Failure preserves both. */
int weighted_remainder_spectral_arithmetic_q(mpq_t h, mpq_t c, unsigned n);

/* Actual infinite C_sp is in [max(0,product_{p<=P}-2/P),product_{p<=P}].
 * P=1..240 is the prime cutoff, not a period or conductor projection.
 * Paired initialized outputs must be distinct. Failure preserves both. */
int weighted_remainder_spectral_product_q(mpq_t lower, mpq_t upper, unsigned P);

/* Literal h and signed c floor identity at canonical rational x in [1,240]
 * (numerator/denominator at most 255 bits). The sums end at floor(x) and
 * their means divide by x. P=1..240 independently truncates the Euler
 * product and both prime moments. The correction_series_prefix is signed
 * finite data, not an enclosure of its infinite series. All bounds are
 * exact rationals. nu moments are finite; the two prime moments are full
 * convergent series enclosed with their displayed omitted-tail bounds.
 * Initialize/clear once. Invalid calls preserve the whole output. x may
 * alias any rational field of out; it is consumed before replacement. */
typedef struct {
    unsigned floor_x, prime_cutoff, prime_tail_binary_exponent;
    mpq_t x, h_sum, h_mean, correction_floor_sum, correction_floor_mean;
    mpq_t correction_series_prefix, product_lower, product_upper;
    mpq_t nu_sum_lower, nu_sum_upper, nu_square_sum_lower, nu_square_sum_upper;
    mpq_t nu_mean_lower, nu_mean_upper, nu_square_mean_lower, nu_square_mean_upper;
    mpq_t first_prefix_lower, first_prefix_upper, first_tail_upper, first_lower, first_upper;
    mpq_t second_prefix_lower, second_prefix_upper, second_tail_upper, second_lower, second_upper;
    mpq_t nu_first_mean_bound, nu_second_mean_bound;
} WeightedRemainderSpectralMean;

void weighted_remainder_spectral_mean_init(WeightedRemainderSpectralMean *out);
void weighted_remainder_spectral_mean_clear(WeightedRemainderSpectralMean *out);
int weighted_remainder_spectral_mean_compute(WeightedRemainderSpectralMean *out,
                                             const mpq_t x, unsigned P);

/* Full amplitude and conductor energy J2(q)*eta_q^2/27. q,M=2..240.
 * The amplitude lower endpoint is its exact finite period prefix. Its
 * upper endpoint intersects omitted unit mass, the proved period error,
 * and 4*(1+log(q))/q^2 using the rational log upper bound. All four
 * initialized outputs must be distinct; failure preserves every output. */
int weighted_remainder_spectral_energy_q(mpq_t amplitude_lower, mpq_t amplitude_upper,
    mpq_t energy_lower, mpq_t energy_upper, unsigned q, unsigned M);

/* Full conductor tail above Q, using band Q<q<=B and periods through M.
 * 1<=Q<=B<=240, B>=4, M=2..240. P=1..240 is the independent prime-product
 * cutoff; N=1..240 is the independent leading-amplitude constant cutoff.
 * The infinite weighted log tail and squared orthogonal projection error
 * have certified lower/upper endpoints. The finite energy band equals
 * energy_band_lower. Leading terms describe the separately proved sharp
 * asymptotic; they are NOT error bounds for either full tail.
 * Initialize/clear once. Invalid calls preserve the whole output. */
typedef struct {
    unsigned cutoff, band_cutoff, period_cutoff, prime_cutoff, constant_cutoff;
    unsigned period_binary_exponent;
    mpq_t product_lower, product_upper, amplitude_leading_lower, amplitude_leading_upper;
    mpq_t log_q_lower, log_q_upper, log_b_lower, log_b_upper;
    mpq_t weighted_band_lower, weighted_band_upper, weighted_remainder_upper;
    mpq_t weighted_tail_lower, weighted_tail_upper;
    mpq_t energy_band_lower, energy_band_upper, energy_remainder_upper;
    mpq_t projection_tail_lower, projection_tail_upper;
    mpq_t weighted_leading_lower, weighted_leading_upper, energy_leading_lower, energy_leading_upper;
} WeightedRemainderSpectralTail;

void weighted_remainder_spectral_tail_init(WeightedRemainderSpectralTail *out);
void weighted_remainder_spectral_tail_clear(WeightedRemainderSpectralTail *out);
int weighted_remainder_spectral_tail_compute(WeightedRemainderSpectralTail *out,
    unsigned Q, unsigned B, unsigned M, unsigned P, unsigned N);

int weighted_remainder_spectral_command(int argc, char **argv);

#endif
