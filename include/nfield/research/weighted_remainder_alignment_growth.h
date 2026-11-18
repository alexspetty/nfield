#ifndef NFIELD_WEIGHTED_REMAINDER_ALIGNMENT_GROWTH_H
#define NFIELD_WEIGHTED_REMAINDER_ALIGNMENT_GROWTH_H
#include "weighted_remainder_alignment.h"
#include "weighted_remainder_power.h"

/* Finite growth readouts, not tests of an all-scale asymptotic. The
 * modulus and M/N/P domains are those of alignment_compute; the
 * independent comparison scale m is 1..240. The exact LCM at m is
 * returned and compared with the supplied modulus. Normalized values
 * are available precisely for modulus>=3. LCM loss bounds require that
 * equality and m>=4; tower bounds require exactly one prime factor.
 * Unavailable fields are zero and have explicit flags. Failure preserves
 * the whole initialized output. Input may alias out->values.modulus. */
typedef struct {
    WeightedRemainderAlignment values;
    mpz_t lcm;
    unsigned scale,lcm_match,normalized_available,lcm_bounds_available,tower_prime,sqrt_floor;
    mpq_t exp_gamma_lower,exp_gamma_upper,kappa_lower,kappa_upper,Gamma_lower,Gamma_upper;
    mpq_t log_scale_lower,log_scale_upper,reset_leading_lower,reset_leading_upper;
    mpq_t alignment_leading_lower,alignment_leading_upper;
    mpq_t log_log_lower,log_log_upper,normalizer_lower,normalizer_upper;
    mpq_t normalized_reset_lower,normalized_reset_upper,normalized_alignment_lower,normalized_alignment_upper;
    mpq_t normalized_negative_g_lower,normalized_negative_g_upper;
    mpq_t mertens_inverse_product,mertens_plus_product,mertens_prime_log_lower,mertens_prime_log_upper;
    mpq_t limiting_prime_log_lower,limiting_prime_log_upper;
    mpq_t finite_alignment_product,reset_relative_product_loss,alignment_relative_product_loss;
    mpq_t lcm_factor_loss_upper,lcm_log_loss_upper;
    mpq_t amplitude_log_constant_upper,tower_reset_upper,tower_alignment_upper,tower_combined_upper;
} WeightedRemainderAlignmentGrowth;
void weighted_remainder_alignment_growth_init(WeightedRemainderAlignmentGrowth *out);
void weighted_remainder_alignment_growth_clear(WeightedRemainderAlignmentGrowth *out);
int weighted_remainder_alignment_growth_compute(WeightedRemainderAlignmentGrowth *out,
    const mpz_t modulus,unsigned m,unsigned M,unsigned N,unsigned P);
#endif
