#include "weighted_remainder_alignment.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FIELDS(X) X(log_modulus_lower) X(log_modulus_upper) X(reset_product) X(reset_log_lower) X(reset_log_upper) \
 X(alignment_factor_correction) X(alignment_product_lower) X(alignment_product_upper) \
 X(alignment_log_correction_lower) X(alignment_log_correction_upper) X(base_log_prefix_lower) X(base_log_prefix_upper) \
 X(base_log_tail_upper) X(alignment_log_lower) X(alignment_log_upper) \
 X(reset_prefix) X(alignment_prefix) X(retained_mass) X(finite_g) X(exact_reset) X(triangular_sum) \
 X(error_bound_prefix) X(error_tail_upper) X(reset_main_lower) X(reset_main_upper) X(alignment_main_lower) X(alignment_main_upper) \
 X(reset_error_prefix_lower) X(reset_error_prefix_upper) X(alignment_error_prefix_lower) X(alignment_error_prefix_upper) \
 X(reset_raw_lower) X(reset_raw_upper) X(alignment_raw_lower) X(alignment_raw_upper) \
 X(reset_refined_lower) X(reset_refined_upper) X(alignment_refined_lower) X(alignment_refined_upper) \
 X(reset_lower) X(reset_upper) X(alignment_lower) X(alignment_upper) X(full_g_lower) X(full_g_upper) \
 X(limiting_factor_product) X(reset_factor_loss_sum) X(alignment_factor_loss_sum) \
 X(reset_log_loss_lower) X(reset_log_loss_upper) X(alignment_log_loss_lower) X(alignment_log_loss_upper)
#define LOCAL_FIELDS(X) X(coefficient) X(main_lower) X(main_upper) X(error_lower) X(error_upper) X(error_bound) \
 X(log_lower) X(log_upper) X(nu_lower) X(nu_upper) X(gamma_lower) X(gamma_upper) X(totient_ratio) X(mobius_sum)
#define CONSTANT_FIELDS(X) X(pi_lower) X(pi_upper) X(zeta_two_lower) X(zeta_two_upper) X(zeta_three_lower) X(zeta_three_upper) \
 X(zeta_four_lower) X(zeta_four_upper) X(gamma_harmonic_prefix) X(log_n_lower) X(log_n_upper) X(gamma_lower) X(gamma_upper) \
 X(log_moment_prefix_lower) X(log_moment_prefix_upper) X(log_moment_tail_upper) X(log_moment_lower) X(log_moment_upper) \
 X(kappa_lower) X(kappa_upper) X(leading_lower) X(leading_upper)
static unsigned checks;
static void check(int ok) { ++checks;if (!ok) { fprintf(stderr,"alignment edge %u failed\n",checks);exit(1); } }
static void unchanged(const WeightedRemainderAlignment *s)
{
    check(!mpz_cmp_ui(s->modulus,77));
    check(s->period_cutoff==71 && s->constant_cutoff==72 && s->prime_cutoff==73 &&
      s->prime_count==74 && s->reset_exact==75 && s->triangular_available==76);
    check(s->constants.cutoff==77 && s->constants.log_tail_binary_exponent==78);
    for (unsigned p=0;p<=240;++p) check(s->valuations[p]==79);
#define SAME(f) check(!mpq_cmp_si(s->f,-13,11));
    FIELDS(SAME)
#undef SAME
#define SAME(f) check(!mpq_cmp_si(s->constants.f,-13,11));
    CONSTANT_FIELDS(SAME)
#undef SAME
}
static void edges(void)
{
    WeightedRemainderAlignment s;weighted_remainder_alignment_init(&s);mpz_set_ui(s.modulus,77);
    s.period_cutoff=71;s.constant_cutoff=72;s.prime_cutoff=73;s.prime_count=74;s.reset_exact=75;s.triangular_available=76;
    s.constants.cutoff=77;s.constants.log_tail_binary_exponent=78;
    for (unsigned p=0;p<=240;++p) s.valuations[p]=79;
#define SET(f) mpq_set_si(s.f,-13,11);
    FIELDS(SET)
#undef SET
#define SET(f) mpq_set_si(s.constants.f,-13,11);
    CONSTANT_FIELDS(SET)
#undef SET
    mpz_t n;mpz_init_set_ui(n,12);
    unsigned bad[][3]={{0,1,1},{1,1,1},{241,1,1},{2,0,1},{2,241,1},{2,1,0},{2,1,241},{~0u,1,1}};
    for (unsigned i=0;i<sizeof bad/sizeof bad[0];++i) {
        check(!weighted_remainder_alignment_compute(&s,n,bad[i][0],bad[i][1],bad[i][2]));unchanged(&s);
    }
    for (unsigned i=0;i<6;++i) {
        if (i<3) mpz_set_si(n,(long)i-1);
        else if (i==3) mpz_set_ui(n,241);
        else mpz_ui_pow_ui(n,2,i==4?241:4096);
        if (i==2) mpz_set_ui(n,2*257);
        check(!weighted_remainder_alignment_compute(&s,n,2,1,1));unchanged(&s);
    }
    check(!weighted_remainder_alignment_compute(&s,NULL,2,1,1));unchanged(&s);
    check(!weighted_remainder_alignment_compute(NULL,s.modulus,2,1,1));
    check(weighted_remainder_alignment_compute(&s,s.modulus,17,13,7));
    check(!mpz_cmp_ui(s.modulus,77) && s.valuations[7]==1 && s.valuations[11]==1 && s.prime_count==2);
    check(weighted_remainder_alignment_compute(&s,s.modulus,240,1,240));
    check(s.reset_exact && s.triangular_available && !mpq_cmp(s.reset_lower,s.reset_upper));
    mpz_set_ui(n,91);check(!weighted_remainder_alignment_lcm_z(n,0) && !mpz_cmp_ui(n,91));
    check(!weighted_remainder_alignment_lcm_z(n,241) && !mpz_cmp_ui(n,91));
    check(!weighted_remainder_alignment_lcm_z(NULL,3));
    weighted_remainder_alignment_clear(&s);mpz_clear(n);
    WeightedRemainderHarmonicLocal h;weighted_remainder_harmonic_local_init(&h);h.period=71;h.constant_cutoff=72;
#define SET(f) mpq_set_si(h.f,-13,11);
    LOCAL_FIELDS(SET)
#undef SET
    unsigned hb[][2]={{0,1},{1,1},{241,1},{2,0},{2,241},{~0u,1}};
    for (unsigned i=0;i<sizeof hb/sizeof hb[0];++i) {
        check(!weighted_remainder_harmonic_local_compute(&h,hb[i][0],hb[i][1]));
        check(h.period==71 && h.constant_cutoff==72);
#define SAME(f) check(!mpq_cmp_si(h.f,-13,11));
        LOCAL_FIELDS(SAME)
#undef SAME
    }
    check(!weighted_remainder_harmonic_local_compute(NULL,2,1));
    check(weighted_remainder_harmonic_local_compute(&h,240,1));
    check(!mpq_sgn(h.mobius_sum));weighted_remainder_harmonic_local_clear(&h);
}
int main(void)
{
    edges();printf("EDGES %u\n",checks);char op,number[1400];unsigned M,N,P;
    while (scanf(" %c",&op)==1) {
        if (op=='A') {
            if (scanf(" %1399s %u %u %u",number,&M,&N,&P)!=4) return 2;
            mpz_t n;mpz_init(n);if (mpz_set_str(n,number,10)) return 2;
            WeightedRemainderAlignment s;weighted_remainder_alignment_init(&s);
            int ok=weighted_remainder_alignment_compute(&s,n,M,N,P);printf("A %d",ok);
            if (ok) {
                gmp_printf(" %Zd %u %u %u %u %u %u",s.modulus,s.period_cutoff,s.constant_cutoff,s.prime_cutoff,
                  s.prime_count,s.reset_exact,s.triangular_available);
                for (unsigned p=0;p<=240;++p) printf(" %u",s.valuations[p]);
#define PRINT(f) gmp_printf(" %Qd",s.f);
                FIELDS(PRINT)
#undef PRINT
#define PRINT(f) gmp_printf(" %Qd",s.constants.f);
                CONSTANT_FIELDS(PRINT)
#undef PRINT
            }
            weighted_remainder_alignment_clear(&s);mpz_clear(n);
        } else if (op=='H') {
            if (scanf(" %u %u",&M,&N)!=2) return 2;
            WeightedRemainderHarmonicLocal s;weighted_remainder_harmonic_local_init(&s);
            int ok=weighted_remainder_harmonic_local_compute(&s,M,N);printf("H %d",ok);
            if (ok) {
                printf(" %u %u",s.period,s.constant_cutoff);
#define PRINT(f) gmp_printf(" %Qd",s.f);
                LOCAL_FIELDS(PRINT)
#undef PRINT
            }
            weighted_remainder_harmonic_local_clear(&s);
        } else if (op=='L') {
            if (scanf(" %u",&M)!=1) return 2;
            mpz_t n;mpz_init(n);int ok=weighted_remainder_alignment_lcm_z(n,M);printf("L %d",ok);
            if (ok) gmp_printf(" %Zd",n);
            mpz_clear(n);
        } else return 2;
        putchar('\n');
    }
    return ferror(stdin)?2:0;
}
