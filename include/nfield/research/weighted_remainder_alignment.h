#ifndef NFIELD_WEIGHTED_REMAINDER_ALIGNMENT_H
#define NFIELD_WEIGHTED_REMAINDER_ALIGNMENT_H
#include "weighted_remainder_alignment_local.h"
#include "weighted_remainder_constants.h"

/* Positive GMP modulus, at most 4096 bits, all prime factors <=240 and
 * every valuation <=240. The factorization is checked, never supplied
 * as an unverified hypothesis. M=2..240 is the weight/error prefix;
 * N=1..240 is the independent constant cutoff; P=1..240 is the
 * independent absent-prime logarithmic prefix. No period enumeration.
 * Exact rational endpoints enclose the infinite observables by proved
 * Euler formulas and explicit harmonic and prime-series remainders.
 * reset_exact is set precisely when modulus<=M. triangular_available
 * is set when modulus<=240. Otherwise those exact fields are zero.
 * Initialize/clear once. Rejected calls preserve the complete output;
 * the input modulus may alias out->modulus. */
typedef struct {
    mpz_t modulus;
    unsigned period_cutoff,constant_cutoff,prime_cutoff;
    unsigned valuations[241],prime_count,reset_exact,triangular_available;
    WeightedRemainderConstants constants;
    mpq_t log_modulus_lower,log_modulus_upper;
    mpq_t reset_product,reset_log_lower,reset_log_upper;
    mpq_t alignment_factor_correction,alignment_product_lower,alignment_product_upper;
    mpq_t alignment_log_correction_lower,alignment_log_correction_upper;
    mpq_t base_log_prefix_lower,base_log_prefix_upper,base_log_tail_upper;
    mpq_t alignment_log_lower,alignment_log_upper;
    mpq_t reset_prefix,alignment_prefix,retained_mass,finite_g,exact_reset,triangular_sum;
    mpq_t error_bound_prefix,error_tail_upper;
    mpq_t reset_main_lower,reset_main_upper,alignment_main_lower,alignment_main_upper;
    mpq_t reset_error_prefix_lower,reset_error_prefix_upper;
    mpq_t alignment_error_prefix_lower,alignment_error_prefix_upper;
    mpq_t reset_raw_lower,reset_raw_upper,alignment_raw_lower,alignment_raw_upper;
    mpq_t reset_refined_lower,reset_refined_upper,alignment_refined_lower,alignment_refined_upper;
    mpq_t reset_lower,reset_upper,alignment_lower,alignment_upper,full_g_lower,full_g_upper;
    mpq_t limiting_factor_product,reset_factor_loss_sum,alignment_factor_loss_sum;
    mpq_t reset_log_loss_lower,reset_log_loss_upper,alignment_log_loss_lower,alignment_log_loss_upper;
} WeightedRemainderAlignment;

void weighted_remainder_alignment_init(WeightedRemainderAlignment *out);
void weighted_remainder_alignment_clear(WeightedRemainderAlignment *out);
int weighted_remainder_alignment_compute(WeightedRemainderAlignment *out,
    const mpz_t modulus,unsigned M,unsigned N,unsigned P);

/* Exact LCM(1,...,m), m=1..240, using GMP. Invalid inputs preserve out. */
int weighted_remainder_alignment_lcm_z(mpz_t out,unsigned m);

/* Literal a_k=k*w_k, harmonic main, signed error, Mobius linear
 * cancellation and sigma_1/(12*k^3), for k=2..240; N=1..240. */
typedef struct {
    unsigned period,constant_cutoff;
    mpq_t coefficient,main_lower,main_upper,error_lower,error_upper,error_bound;
    mpq_t log_lower,log_upper,nu_lower,nu_upper,gamma_lower,gamma_upper;
    mpq_t totient_ratio,mobius_sum;
} WeightedRemainderHarmonicLocal;
void weighted_remainder_harmonic_local_init(WeightedRemainderHarmonicLocal *out);
void weighted_remainder_harmonic_local_clear(WeightedRemainderHarmonicLocal *out);
int weighted_remainder_harmonic_local_compute(WeightedRemainderHarmonicLocal *out,
    unsigned k,unsigned N);
#endif
