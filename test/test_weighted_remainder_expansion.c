#include "../src/weighted_remainder_expansion.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void fields(WeightedRemainderExpansion *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->delta,s->jordan_three,s->totient_ratio,s->rho,s->prime_factor_plus_product,
        s->log_lower,s->log_upper,s->nu_lower,s->nu_upper,s->mobius_inverse,s->mobius_log_lower,s->mobius_log_upper,
        s->harmonic_prefix,s->harmonic_error_raw_lower,s->harmonic_error_raw_upper,
        s->harmonic_error_lower,s->harmonic_error_upper,s->harmonic_error_bound,
        s->seed_main_lower,s->seed_main_upper,s->seed_error_bound,s->seed_lower,s->seed_upper,
        s->main_lower,s->main_upper,s->error_upper,s->amplitude_lower,s->amplitude_upper,
        s->prime_power_main_lower,s->prime_power_main_upper,s->prime_leading_lower,s->prime_leading_upper,
        s->constants.pi_lower,s->constants.pi_upper,s->constants.zeta_two_lower,s->constants.zeta_two_upper,
        s->constants.zeta_three_lower,s->constants.zeta_three_upper,s->constants.zeta_four_lower,s->constants.zeta_four_upper,
        s->constants.gamma_harmonic_prefix,s->constants.log_n_lower,s->constants.log_n_upper,s->constants.gamma_lower,s->constants.gamma_upper,
        s->constants.log_moment_prefix_lower,s->constants.log_moment_prefix_upper,s->constants.log_moment_tail_upper,
        s->constants.log_moment_lower,s->constants.log_moment_upper,s->constants.kappa_lower,s->constants.kappa_upper,
        s->constants.leading_lower,s->constants.leading_upper};
    for (unsigned i=0;i<54;++i) v[i]=a[i];
}

static int sentinel(WeightedRemainderExpansion *s)
{
    if (s->conductor!=11 || s->amplitude_expansion_available!=13 || s->prime_base!=17 ||
        s->prime_exponent!=19 || s->constants.cutoff!=23 || s->constants.log_tail_binary_exponent!=29) return 0;
    mpq_ptr v[54];fields(s,v);
    for (unsigned i=0;i<54;++i) if (mpq_cmp_ui(v[i],i+1,i+2)) return 0;
    return 1;
}

static void edge_checks(void)
{
    WeightedRemainderExpansion s;weighted_remainder_expansion_init(&s);
    s.conductor=11;s.amplitude_expansion_available=13;s.prime_base=17;s.prime_exponent=19;
    s.constants.cutoff=23;s.constants.log_tail_binary_exponent=29;
    mpq_ptr v[54];fields(&s,v);for (unsigned i=0;i<54;++i) mpq_set_ui(v[i],i+1,i+2);
    const unsigned invalid[][2]={{0,1},{241,1},{1,0},{1,241},{~0U,1},{1,~0U}};
    for (unsigned i=0;i<sizeof invalid/sizeof *invalid;++i) {
        CHECK(!weighted_remainder_expansion_compute(&s,invalid[i][0],invalid[i][1]));CHECK(sentinel(&s));
    }
    CHECK(!weighted_remainder_expansion_compute(NULL,1,1));
    CHECK(weighted_remainder_expansion_compute(&s,1,1));
    CHECK(s.conductor==1 && !s.amplitude_expansion_available && !s.prime_base && !s.prime_exponent);
    CHECK(!mpq_cmp_ui(s.delta,1,1) && !mpq_cmp_ui(s.jordan_three,1,1) && !mpq_cmp_ui(s.totient_ratio,1,1));
    CHECK(!mpq_cmp_ui(s.rho,1,1) && !mpq_cmp_ui(s.mobius_inverse,1,1) && !mpq_sgn(s.nu_lower));
    CHECK(!mpq_sgn(s.main_lower) && !mpq_sgn(s.main_upper) && !mpq_sgn(s.error_upper));
    CHECK(!mpq_sgn(s.amplitude_lower) && !mpq_sgn(s.amplitude_upper));
    CHECK(!mpq_cmp_ui(s.harmonic_error_bound,1,12));
    CHECK(weighted_remainder_expansion_compute(&s,8,2));
    CHECK(s.prime_base==2 && s.prime_exponent==3 && s.amplitude_expansion_available);
    CHECK(!mpq_cmp_ui(s.delta,7,8) && !mpq_cmp_ui(s.jordan_three,448,1));
    CHECK(!mpq_cmp_ui(s.rho,4,7) && !mpq_cmp_ui(s.prime_factor_plus_product,3,1));
    for (unsigned i=0;i<54;++i) mpq_set_ui(v[i],0,1);
    /* The pointer table still addresses the same struct fields after an
     * ownership transfer. Repeated calls exercise replacing live outputs. */
    for (unsigned n=1;n<=16;++n) {
        CHECK(weighted_remainder_expansion_compute(&s,n,2));
        CHECK(s.conductor==n && s.constants.cutoff==2);
    }
    weighted_remainder_expansion_clear(&s);printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();WeightedRemainderExpansion s;weighted_remainder_expansion_init(&s);
    mpq_ptr v[54];fields(&s,v);unsigned q,N;
    while (scanf("%u %u",&q,&N)==2) {
        int ok=weighted_remainder_expansion_compute(&s,q,N);printf("R %d",ok);
        if (ok) {
            printf(" %u %u %u %u %u %u",s.conductor,s.amplitude_expansion_available,
                s.prime_base,s.prime_exponent,s.constants.cutoff,s.constants.log_tail_binary_exponent);
            for (unsigned i=0;i<54;++i) gmp_printf(" %Qd",v[i]);
        }
        putchar('\n');
    }
    weighted_remainder_expansion_clear(&s);return 0;
}
