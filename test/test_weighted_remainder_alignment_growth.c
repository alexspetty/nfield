#include "weighted_remainder_alignment_growth.h"
#include <stdio.h>
#include <stdlib.h>
#define CHECK(ok) do { if (!(ok)) { fprintf(stderr,"growth assertion at %d\n",__LINE__); exit(1); } } while (0)
int main(void)
{
    WeightedRemainderAlignmentGrowth s; weighted_remainder_alignment_growth_init(&s);
    mpz_t n; mpz_init_set_ui(n,12);
    CHECK(weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12));
    CHECK(s.lcm_match && s.lcm_bounds_available && s.normalized_available && !s.tower_prime);
    CHECK(weighted_remainder_alignment_growth_compute(&s,s.values.modulus,4,12,12,12));
    CHECK(!mpz_cmp_ui(s.values.modulus,12));
    /* Reject unsupported factors without replacing the initialized result. */
    mpz_set_ui(n,241);
    CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12));
    CHECK(!mpz_cmp_ui(s.values.modulus,12) && s.lcm_match && s.scale==4);
    CHECK(!weighted_remainder_alignment_growth_compute(NULL,n,4,12,12,12));
    CHECK(!weighted_remainder_alignment_growth_compute(&s,NULL,4,12,12,12));
    CHECK(!weighted_remainder_alignment_growth_compute(&s,s.values.modulus,0,12,12,12));
    CHECK(!weighted_remainder_alignment_growth_compute(&s,s.values.modulus,241,12,12,12));
    mpq_t before; mpq_init(before);
    mpq_set(before,s.exp_gamma_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.exp_gamma_lower));
    mpq_set(before,s.exp_gamma_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.exp_gamma_upper));
    mpq_set(before,s.kappa_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.kappa_lower));
    mpq_set(before,s.kappa_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.kappa_upper));
    mpq_set(before,s.Gamma_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.Gamma_lower));
    mpq_set(before,s.Gamma_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.Gamma_upper));
    mpq_set(before,s.log_scale_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.log_scale_lower));
    mpq_set(before,s.log_scale_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.log_scale_upper));
    mpq_set(before,s.reset_leading_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.reset_leading_lower));
    mpq_set(before,s.reset_leading_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.reset_leading_upper));
    mpq_set(before,s.alignment_leading_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.alignment_leading_lower));
    mpq_set(before,s.alignment_leading_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.alignment_leading_upper));
    mpq_set(before,s.log_log_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.log_log_lower));
    mpq_set(before,s.log_log_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.log_log_upper));
    mpq_set(before,s.normalizer_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalizer_lower));
    mpq_set(before,s.normalizer_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalizer_upper));
    mpq_set(before,s.normalized_reset_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalized_reset_lower));
    mpq_set(before,s.normalized_reset_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalized_reset_upper));
    mpq_set(before,s.normalized_alignment_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalized_alignment_lower));
    mpq_set(before,s.normalized_alignment_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalized_alignment_upper));
    mpq_set(before,s.normalized_negative_g_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalized_negative_g_lower));
    mpq_set(before,s.normalized_negative_g_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.normalized_negative_g_upper));
    mpq_set(before,s.mertens_inverse_product); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.mertens_inverse_product));
    mpq_set(before,s.mertens_plus_product); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.mertens_plus_product));
    mpq_set(before,s.mertens_prime_log_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.mertens_prime_log_lower));
    mpq_set(before,s.mertens_prime_log_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.mertens_prime_log_upper));
    mpq_set(before,s.limiting_prime_log_lower); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.limiting_prime_log_lower));
    mpq_set(before,s.limiting_prime_log_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.limiting_prime_log_upper));
    mpq_set(before,s.finite_alignment_product); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.finite_alignment_product));
    mpq_set(before,s.reset_relative_product_loss); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.reset_relative_product_loss));
    mpq_set(before,s.alignment_relative_product_loss); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.alignment_relative_product_loss));
    mpq_set(before,s.lcm_factor_loss_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.lcm_factor_loss_upper));
    mpq_set(before,s.lcm_log_loss_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.lcm_log_loss_upper));
    mpq_set(before,s.amplitude_log_constant_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.amplitude_log_constant_upper));
    mpq_set(before,s.tower_reset_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.tower_reset_upper));
    mpq_set(before,s.tower_alignment_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.tower_alignment_upper));
    mpq_set(before,s.tower_combined_upper); CHECK(!weighted_remainder_alignment_growth_compute(&s,n,4,12,12,12)); CHECK(!mpq_cmp(before,s.tower_combined_upper));
    mpz_set_ui(n,1); CHECK(weighted_remainder_alignment_growth_compute(&s,n,1,2,1,1));
    CHECK(!s.normalized_available && !s.lcm_bounds_available && !s.tower_prime && s.lcm_match);
    CHECK(!mpq_sgn(s.normalizer_lower) && !mpq_sgn(s.normalized_alignment_upper) && !mpq_sgn(s.tower_combined_upper));
    mpz_set_ui(n,2); CHECK(weighted_remainder_alignment_growth_compute(&s,n,240,240,240,240));
    CHECK(s.tower_prime==2 && !s.normalized_available && !s.lcm_match);
    mpz_ui_pow_ui(n,239,240); CHECK(weighted_remainder_alignment_growth_compute(&s,n,239,2,1,1));
    CHECK(s.tower_prime==239 && s.normalized_available && !s.lcm_match);
    mpq_clear(before); mpz_clear(n); weighted_remainder_alignment_growth_clear(&s);
    puts("PASS growth admission, upper-domain, alias and output-preservation checks"); return 0;
}
