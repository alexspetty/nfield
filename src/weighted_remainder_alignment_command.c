#include "weighted_remainder_alignment_command.h"
#include "weighted_remainder_alignment_growth.h"
#include <stdio.h>
#include <string.h>

static int index_arg(const char *p, unsigned lower, unsigned *out)
{
    if (!p || !*p) return 0;
    unsigned n=0;
    for (; *p; ++p) {
        if (*p<'0' || *p>'9') return 0;
        n=10*n+(unsigned)(*p-'0');
        if (n>WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    }
    if (n<lower) return 0;
    *out=n; return 1;
}
static int modulus_arg(mpz_t out, const char *p)
{
    if (!p || !*p || strlen(p)>1234) return 0;
    for (const char *q=p; *q; ++q) if (*q<'0' || *q>'9') return 0;
    return mpz_set_str(out,p,10)==0 && mpz_sgn(out)>0 && mpz_sizeinbase(out,2)<=4096;
}

static void print_local(const WeightedRemainderAlignmentLocal *s)
{
    printf("prime=%u\nvaluation=%u\n",s->prime,s->valuation);
    gmp_printf("reset_factor=%Qd\n",s->reset_factor);
    gmp_printf("reset_numerator=%Qd\n",s->reset_numerator);
    gmp_printf("reset_average=%Qd\n",s->reset_average);
    gmp_printf("alignment_factor=%Qd\n",s->alignment_factor);
    gmp_printf("alignment_numerator=%Qd\n",s->alignment_numerator);
    gmp_printf("alignment_average=%Qd\n",s->alignment_average);
    gmp_printf("alignment_tail=%Qd\n",s->alignment_tail);
    gmp_printf("limiting_factor=%Qd\n",s->limiting_factor);
    gmp_printf("limiting_average=%Qd\n",s->limiting_average);
    gmp_printf("reset_factor_relative_loss=%Qd\n",s->reset_factor_relative_loss);
    gmp_printf("reset_average_loss=%Qd\n",s->reset_average_loss);
    gmp_printf("alignment_factor_relative_loss=%Qd\n",s->alignment_factor_relative_loss);
    gmp_printf("alignment_average_loss=%Qd\n",s->alignment_average_loss);
    gmp_printf("absent_factor=%Qd\n",s->absent_factor);
    gmp_printf("absent_average=%Qd\n",s->absent_average);
}

static void print_harmonic(const WeightedRemainderHarmonicLocal *s)
{
    printf("period=%u\nconstant_cutoff=%u\n",s->period,s->constant_cutoff);
    gmp_printf("coefficient=%Qd\n",s->coefficient);
    gmp_printf("main_lower=%Qd\n",s->main_lower);
    gmp_printf("main_upper=%Qd\n",s->main_upper);
    gmp_printf("error_lower=%Qd\n",s->error_lower);
    gmp_printf("error_upper=%Qd\n",s->error_upper);
    gmp_printf("error_bound=%Qd\n",s->error_bound);
    gmp_printf("log_lower=%Qd\n",s->log_lower);
    gmp_printf("log_upper=%Qd\n",s->log_upper);
    gmp_printf("nu_lower=%Qd\n",s->nu_lower);
    gmp_printf("nu_upper=%Qd\n",s->nu_upper);
    gmp_printf("gamma_lower=%Qd\n",s->gamma_lower);
    gmp_printf("gamma_upper=%Qd\n",s->gamma_upper);
    gmp_printf("totient_ratio=%Qd\n",s->totient_ratio);
    gmp_printf("mobius_sum=%Qd\n",s->mobius_sum);
}

static void print_alignment(const WeightedRemainderAlignment *s)
{
    gmp_printf("modulus=%Zd\n",s->modulus);
    printf("period_cutoff=%u\nconstant_cutoff=%u\nprime_cutoff=%u\nprime_count=%u\nreset_exact=%u\ntriangular_available=%u\n",
           s->period_cutoff,s->constant_cutoff,s->prime_cutoff,s->prime_count,s->reset_exact,s->triangular_available);
    for (unsigned p=2;p<=240;++p) if (s->valuations[p]) printf("valuation_%u=%u\n",p,s->valuations[p]);
    gmp_printf("log_modulus_lower=%Qd\n",s->log_modulus_lower);
    gmp_printf("log_modulus_upper=%Qd\n",s->log_modulus_upper);
    gmp_printf("reset_product=%Qd\n",s->reset_product);
    gmp_printf("reset_log_lower=%Qd\n",s->reset_log_lower);
    gmp_printf("reset_log_upper=%Qd\n",s->reset_log_upper);
    gmp_printf("alignment_factor_correction=%Qd\n",s->alignment_factor_correction);
    gmp_printf("alignment_product_lower=%Qd\n",s->alignment_product_lower);
    gmp_printf("alignment_product_upper=%Qd\n",s->alignment_product_upper);
    gmp_printf("alignment_log_correction_lower=%Qd\n",s->alignment_log_correction_lower);
    gmp_printf("alignment_log_correction_upper=%Qd\n",s->alignment_log_correction_upper);
    gmp_printf("base_log_prefix_lower=%Qd\n",s->base_log_prefix_lower);
    gmp_printf("base_log_prefix_upper=%Qd\n",s->base_log_prefix_upper);
    gmp_printf("base_log_tail_upper=%Qd\n",s->base_log_tail_upper);
    gmp_printf("alignment_log_lower=%Qd\n",s->alignment_log_lower);
    gmp_printf("alignment_log_upper=%Qd\n",s->alignment_log_upper);
    gmp_printf("reset_prefix=%Qd\n",s->reset_prefix);
    gmp_printf("alignment_prefix=%Qd\n",s->alignment_prefix);
    gmp_printf("retained_mass=%Qd\n",s->retained_mass);
    gmp_printf("finite_g=%Qd\n",s->finite_g);
    gmp_printf("exact_reset=%Qd\n",s->exact_reset);
    gmp_printf("triangular_sum=%Qd\n",s->triangular_sum);
    gmp_printf("error_bound_prefix=%Qd\n",s->error_bound_prefix);
    gmp_printf("error_tail_upper=%Qd\n",s->error_tail_upper);
    gmp_printf("reset_main_lower=%Qd\n",s->reset_main_lower);
    gmp_printf("reset_main_upper=%Qd\n",s->reset_main_upper);
    gmp_printf("alignment_main_lower=%Qd\n",s->alignment_main_lower);
    gmp_printf("alignment_main_upper=%Qd\n",s->alignment_main_upper);
    gmp_printf("reset_error_prefix_lower=%Qd\n",s->reset_error_prefix_lower);
    gmp_printf("reset_error_prefix_upper=%Qd\n",s->reset_error_prefix_upper);
    gmp_printf("alignment_error_prefix_lower=%Qd\n",s->alignment_error_prefix_lower);
    gmp_printf("alignment_error_prefix_upper=%Qd\n",s->alignment_error_prefix_upper);
    gmp_printf("reset_raw_lower=%Qd\n",s->reset_raw_lower);
    gmp_printf("reset_raw_upper=%Qd\n",s->reset_raw_upper);
    gmp_printf("alignment_raw_lower=%Qd\n",s->alignment_raw_lower);
    gmp_printf("alignment_raw_upper=%Qd\n",s->alignment_raw_upper);
    gmp_printf("reset_refined_lower=%Qd\n",s->reset_refined_lower);
    gmp_printf("reset_refined_upper=%Qd\n",s->reset_refined_upper);
    gmp_printf("alignment_refined_lower=%Qd\n",s->alignment_refined_lower);
    gmp_printf("alignment_refined_upper=%Qd\n",s->alignment_refined_upper);
    gmp_printf("reset_lower=%Qd\n",s->reset_lower);
    gmp_printf("reset_upper=%Qd\n",s->reset_upper);
    gmp_printf("alignment_lower=%Qd\n",s->alignment_lower);
    gmp_printf("alignment_upper=%Qd\n",s->alignment_upper);
    gmp_printf("full_g_lower=%Qd\n",s->full_g_lower);
    gmp_printf("full_g_upper=%Qd\n",s->full_g_upper);
    gmp_printf("limiting_factor_product=%Qd\n",s->limiting_factor_product);
    gmp_printf("reset_factor_loss_sum=%Qd\n",s->reset_factor_loss_sum);
    gmp_printf("alignment_factor_loss_sum=%Qd\n",s->alignment_factor_loss_sum);
    gmp_printf("reset_log_loss_lower=%Qd\n",s->reset_log_loss_lower);
    gmp_printf("reset_log_loss_upper=%Qd\n",s->reset_log_loss_upper);
    gmp_printf("alignment_log_loss_lower=%Qd\n",s->alignment_log_loss_lower);
    gmp_printf("alignment_log_loss_upper=%Qd\n",s->alignment_log_loss_upper);
}

static void print_growth(const WeightedRemainderAlignmentGrowth *s)
{
    print_alignment(&s->values);
    gmp_printf("lcm=%Zd\n",s->lcm);
    printf("scale=%u\nlcm_match=%u\nnormalized_available=%u\nlcm_bounds_available=%u\ntower_prime=%u\nsqrt_floor=%u\n",
           s->scale,s->lcm_match,s->normalized_available,s->lcm_bounds_available,s->tower_prime,s->sqrt_floor);
    gmp_printf("exp_gamma_lower=%Qd\n",s->exp_gamma_lower);
    gmp_printf("exp_gamma_upper=%Qd\n",s->exp_gamma_upper);
    gmp_printf("kappa_lower=%Qd\n",s->kappa_lower);
    gmp_printf("kappa_upper=%Qd\n",s->kappa_upper);
    gmp_printf("Gamma_lower=%Qd\n",s->Gamma_lower);
    gmp_printf("Gamma_upper=%Qd\n",s->Gamma_upper);
    gmp_printf("log_scale_lower=%Qd\n",s->log_scale_lower);
    gmp_printf("log_scale_upper=%Qd\n",s->log_scale_upper);
    gmp_printf("reset_leading_lower=%Qd\n",s->reset_leading_lower);
    gmp_printf("reset_leading_upper=%Qd\n",s->reset_leading_upper);
    gmp_printf("alignment_leading_lower=%Qd\n",s->alignment_leading_lower);
    gmp_printf("alignment_leading_upper=%Qd\n",s->alignment_leading_upper);
    gmp_printf("log_log_lower=%Qd\n",s->log_log_lower);
    gmp_printf("log_log_upper=%Qd\n",s->log_log_upper);
    gmp_printf("normalizer_lower=%Qd\n",s->normalizer_lower);
    gmp_printf("normalizer_upper=%Qd\n",s->normalizer_upper);
    gmp_printf("normalized_reset_lower=%Qd\n",s->normalized_reset_lower);
    gmp_printf("normalized_reset_upper=%Qd\n",s->normalized_reset_upper);
    gmp_printf("normalized_alignment_lower=%Qd\n",s->normalized_alignment_lower);
    gmp_printf("normalized_alignment_upper=%Qd\n",s->normalized_alignment_upper);
    gmp_printf("normalized_negative_g_lower=%Qd\n",s->normalized_negative_g_lower);
    gmp_printf("normalized_negative_g_upper=%Qd\n",s->normalized_negative_g_upper);
    gmp_printf("mertens_inverse_product=%Qd\n",s->mertens_inverse_product);
    gmp_printf("mertens_plus_product=%Qd\n",s->mertens_plus_product);
    gmp_printf("mertens_prime_log_lower=%Qd\n",s->mertens_prime_log_lower);
    gmp_printf("mertens_prime_log_upper=%Qd\n",s->mertens_prime_log_upper);
    gmp_printf("limiting_prime_log_lower=%Qd\n",s->limiting_prime_log_lower);
    gmp_printf("limiting_prime_log_upper=%Qd\n",s->limiting_prime_log_upper);
    gmp_printf("finite_alignment_product=%Qd\n",s->finite_alignment_product);
    gmp_printf("reset_relative_product_loss=%Qd\n",s->reset_relative_product_loss);
    gmp_printf("alignment_relative_product_loss=%Qd\n",s->alignment_relative_product_loss);
    gmp_printf("lcm_factor_loss_upper=%Qd\n",s->lcm_factor_loss_upper);
    gmp_printf("lcm_log_loss_upper=%Qd\n",s->lcm_log_loss_upper);
    gmp_printf("amplitude_log_constant_upper=%Qd\n",s->amplitude_log_constant_upper);
    gmp_printf("tower_reset_upper=%Qd\n",s->tower_reset_upper);
    gmp_printf("tower_alignment_upper=%Qd\n",s->tower_alignment_upper);
    gmp_printf("tower_combined_upper=%Qd\n",s->tower_combined_upper);
}

int weighted_remainder_alignment_command(int argc, char **argv)
{
    unsigned p,v,k,m,M,N,P;
    if (argc<3) return 1;
    if (!strcmp(argv[2],"alignment-local")) {
        if (argc!=5 || !index_arg(argv[3],2,&p) || !index_arg(argv[4],0,&v)) goto bad;
        WeightedRemainderAlignmentLocal s; weighted_remainder_alignment_local_init(&s);
        int ok=weighted_remainder_alignment_local_compute(&s,p,v);
        if (ok) { puts("Reset and alignment local factors"); print_local(&s); }
        weighted_remainder_alignment_local_clear(&s); if (!ok) goto bad;
    } else if (!strcmp(argv[2],"harmonic-local")) {
        if (argc!=5 || !index_arg(argv[3],2,&k) || !index_arg(argv[4],1,&N)) goto bad;
        WeightedRemainderHarmonicLocal s; weighted_remainder_harmonic_local_init(&s);
        int ok=weighted_remainder_harmonic_local_compute(&s,k,N);
        if (ok) { puts("Harmonic coefficient and signed remainder"); print_harmonic(&s); }
        weighted_remainder_harmonic_local_clear(&s); if (!ok) goto bad;
    } else if (!strcmp(argv[2],"alignment")) {
        if (argc!=7 || !index_arg(argv[4],2,&M) || !index_arg(argv[5],1,&N) || !index_arg(argv[6],1,&P)) goto bad;
        mpz_t n; mpz_init(n); WeightedRemainderAlignment s; weighted_remainder_alignment_init(&s);
        int ok=modulus_arg(n,argv[3]) && weighted_remainder_alignment_compute(&s,n,M,N,P);
        if (ok) { puts("Reset and full alignment bounds"); print_alignment(&s); }
        weighted_remainder_alignment_clear(&s); mpz_clear(n); if (!ok) goto bad;
    } else if (!strcmp(argv[2],"alignment-growth") || !strcmp(argv[2],"alignment-lcm")) {
        int lcm=!strcmp(argv[2],"alignment-lcm"), offset=lcm?0:1;
        if (argc!=7+offset || !index_arg(argv[3+offset],1,&m) || !index_arg(argv[4+offset],2,&M) ||
            !index_arg(argv[5+offset],1,&N) || !index_arg(argv[6+offset],1,&P)) goto bad;
        mpz_t n; mpz_init(n); WeightedRemainderAlignmentGrowth s; weighted_remainder_alignment_growth_init(&s);
        int ok=lcm?weighted_remainder_alignment_lcm_z(n,m):modulus_arg(n,argv[3]);
        ok=ok && weighted_remainder_alignment_growth_compute(&s,n,m,M,N,P);
        if (ok) { puts("Finite alignment growth and prime products"); print_growth(&s); }
        weighted_remainder_alignment_growth_clear(&s); mpz_clear(n); if (!ok) goto bad;
        puts("Leading terms are asymptotic comparisons. Availability flags govern normalized, LCM-loss and prime-tower fields; unavailable fields are zero.");
    } else return 1;
    puts("Exact rational endpoints. M retains periods, N controls constants and P controls the absent-prime logarithmic tail. No period enumeration or all-scale inference.");
    return 0;
bad:
    fputs("Use alignment n M N P; alignment-local p v; harmonic-local k N; alignment-lcm m M N P; alignment-growth n m M N P. "
          "Require M,k=2..240, m,N,P=1..240, prime p=2..239 and v=0..240. "
          "n is a positive decimal integer of at most 4096 bits, with prime factors at most 239 and valuations at most 240.\n",stderr);
    return 1;
}
