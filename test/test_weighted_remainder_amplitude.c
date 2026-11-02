#include "../src/weighted_remainder_amplitude.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void fields(WeightedRemainderAmplitude *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->delta,s->jordan_three,s->zeta_lower,s->zeta_upper,s->zeta_tail,
        s->retained_amplitude,s->amplitude_lower,s->amplitude_upper,s->conductor_upper,
        s->seed_prefix,s->seed_budget_lower,s->seed_lower,s->seed_upper,s->seed_tail_upper,
        s->refinement_numerator_lower,s->refinement_numerator_upper,s->refinement_lower,s->refinement_upper,
        s->jordan_sum_lower,s->jordan_sum_upper,s->jordan_rhs_lower,s->jordan_rhs_upper,
        s->mobius_prefix_lower,s->mobius_prefix_upper,s->mobius_tail_upper,
        s->mobius_lower,s->mobius_upper,s->prime_lower,s->prime_upper,s->period_tail_bound,s->period_tail_upper};
    for (unsigned i=0;i<31;++i) v[i]=a[i];
}

static int sentinel(WeightedRemainderAmplitude *s)
{
    if (s->conductor!=31 || s->period_cutoff!=37 || s->zeta_cutoff!=41 ||
        s->mobius_cutoff!=43 || s->binary_exponent!=47 || s->prime!=53 || s->period_binary_exponent!=59) return 0;
    mpq_ptr v[31];fields(s,v);
    for (unsigned i=0;i<31;++i) if (mpq_cmp_ui(v[i],i+1,i+2)) return 0;
    return 1;
}

static void edge_checks(void)
{
    mpq_t a,b;mpq_inits(a,b,NULL);mpq_set_ui(a,5,7);mpq_set_ui(b,11,13);
    CHECK(!weighted_remainder_amplitude_factors_q(a,b,0));
    CHECK(!weighted_remainder_amplitude_factors_q(a,b,241));
    CHECK(!weighted_remainder_amplitude_factors_q(a,a,6));
    CHECK(!weighted_remainder_amplitude_factors_q(NULL,b,6));
    CHECK(!weighted_remainder_amplitude_factors_q(a,NULL,6));
    CHECK(!mpq_cmp_ui(a,5,7) && !mpq_cmp_ui(b,11,13));
    CHECK(!weighted_remainder_zeta_three_interval_q(a,b,0));
    CHECK(!weighted_remainder_zeta_three_interval_q(a,b,241));
    CHECK(!weighted_remainder_zeta_three_interval_q(a,a,6));
    CHECK(!weighted_remainder_zeta_three_interval_q(NULL,b,6));
    CHECK(!weighted_remainder_zeta_three_interval_q(a,NULL,6));
    CHECK(!mpq_cmp_ui(a,5,7) && !mpq_cmp_ui(b,11,13));
    CHECK(!weighted_remainder_harmonic_seed_prefix_q(a,0,12));
    CHECK(!weighted_remainder_harmonic_seed_prefix_q(a,241,12));
    CHECK(!weighted_remainder_harmonic_seed_prefix_q(a,12,241));
    CHECK(!weighted_remainder_harmonic_seed_prefix_q(NULL,12,12));
    CHECK(!mpq_cmp_ui(a,5,7));
    CHECK(weighted_remainder_amplitude_factors_q(a,b,1));
    CHECK(!mpq_cmp_ui(a,1,1) && !mpq_cmp_ui(b,1,1));
    CHECK(weighted_remainder_zeta_three_interval_q(a,b,1));
    CHECK(!mpq_cmp_ui(a,1,1) && !mpq_cmp_ui(b,3,2));
    CHECK(weighted_remainder_harmonic_seed_prefix_q(a,1,0));CHECK(!mpq_sgn(a));
    CHECK(weighted_remainder_harmonic_seed_prefix_q(a,1,1));CHECK(!mpq_sgn(a));
    CHECK(weighted_remainder_harmonic_seed_prefix_q(a,1,2));CHECK(!mpq_cmp_ui(a,1,4));
    WeightedRemainderAmplitude s;weighted_remainder_amplitude_init(&s);
    s.conductor=31;s.period_cutoff=37;s.zeta_cutoff=41;s.mobius_cutoff=43;s.binary_exponent=47;s.prime=53;s.period_binary_exponent=59;
    mpq_ptr v[31];fields(&s,v);
    for (unsigned i=0;i<31;++i) { mpq_set_ui(v[i],i+1,i+2);mpq_canonicalize(v[i]); }
    const unsigned invalid[][4]={{0,2,1,1},{241,2,1,1},{1,0,1,1},{1,1,1,1},{1,241,1,1},
        {1,2,0,1},{1,2,241,1},{1,2,1,0},{1,2,1,241},{~0U,2,1,1},{1,~0U,1,1},{1,2,~0U,1},{1,2,1,~0U}};
    for (unsigned i=0;i<sizeof invalid/sizeof *invalid;++i) {
        CHECK(!weighted_remainder_amplitude_refinement_compute(&s,invalid[i][0],invalid[i][1],invalid[i][2],invalid[i][3]));
        CHECK(sentinel(&s));
    }
    CHECK(!weighted_remainder_amplitude_refinement_compute(NULL,1,2,1,1));
    CHECK(weighted_remainder_amplitude_refinement_compute(&s,1,2,1,1));
    CHECK(s.conductor==1 && s.period_cutoff==2 && s.zeta_cutoff==1 && s.mobius_cutoff==1 && s.binary_exponent==0 && !s.prime && s.period_binary_exponent==2);
    CHECK(!mpq_cmp_ui(s.retained_amplitude,1,4));
    CHECK(!mpq_cmp_ui(s.amplitude_lower,1,1) && !mpq_cmp_ui(s.amplitude_upper,1,1));
    CHECK(!mpq_cmp_ui(s.seed_lower,1,1) && !mpq_cmp_ui(s.seed_upper,3,2));
    CHECK(!mpq_cmp_ui(s.refinement_lower,2,3) && !mpq_cmp_ui(s.refinement_upper,3,2));
    CHECK(!mpq_cmp_ui(s.mobius_lower,1,4) && !mpq_cmp_ui(s.mobius_upper,9,4));
    CHECK(!mpq_cmp_ui(s.period_tail_bound,7,2));
    CHECK(!mpq_cmp_ui(s.period_tail_upper,3,4));
    CHECK(!mpq_sgn(s.prime_lower) && !mpq_sgn(s.prime_upper));
    weighted_remainder_amplitude_clear(&s);mpq_clears(a,b,NULL);
    printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();
    WeightedRemainderAmplitude s;weighted_remainder_amplitude_init(&s);
    mpq_t a,b;mpq_inits(a,b,NULL);mpq_ptr v[31];fields(&s,v);
    char line[256],op;unsigned q,M,N,D;
    while (fgets(line,sizeof line,stdin)) {
        int argc=sscanf(line," %c %u %u %u %u",&op,&q,&M,&N,&D),ok=0;
        if (argc==2 && op=='L') {
            ok=weighted_remainder_amplitude_factors_q(a,b,q);printf("L %d",ok);
            if (ok) gmp_printf(" %Qd %Qd",a,b);
        } else if (argc==2 && op=='Z') {
            ok=weighted_remainder_zeta_three_interval_q(a,b,q);printf("Z %d",ok);
            if (ok) gmp_printf(" %Qd %Qd",a,b);
        } else if (argc==3 && op=='S') {
            ok=weighted_remainder_harmonic_seed_prefix_q(a,q,M);printf("S %d",ok);
            if (ok) gmp_printf(" %Qd",a);
        } else if (argc==5 && op=='R') {
            ok=weighted_remainder_amplitude_refinement_compute(&s,q,M,N,D);printf("R %d",ok);
            if (ok) {
                printf(" %u %u %u %u %u %u %u",s.conductor,s.period_cutoff,s.zeta_cutoff,s.mobius_cutoff,s.binary_exponent,s.prime,s.period_binary_exponent);
                for (unsigned i=0;i<31;++i) gmp_printf(" %Qd",v[i]);
            }
        } else { fputs("invalid test query\n",stderr);return 2; }
        putchar('\n');
    }
    mpq_clears(a,b,NULL);weighted_remainder_amplitude_clear(&s);return 0;
}
