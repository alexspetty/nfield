#include "../src/weighted_remainder_constants.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void fields(WeightedRemainderConstants *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->pi_lower,s->pi_upper,s->zeta_two_lower,s->zeta_two_upper,
        s->zeta_three_lower,s->zeta_three_upper,s->zeta_four_lower,s->zeta_four_upper,
        s->gamma_harmonic_prefix,s->log_n_lower,s->log_n_upper,s->gamma_lower,s->gamma_upper,
        s->log_moment_prefix_lower,s->log_moment_prefix_upper,s->log_moment_tail_upper,
        s->log_moment_lower,s->log_moment_upper,s->kappa_lower,s->kappa_upper,
        s->leading_lower,s->leading_upper};
    for (unsigned i=0;i<22;++i) v[i]=a[i];
}

static int sentinel(WeightedRemainderConstants *s)
{
    if (s->cutoff!=17 || s->log_tail_binary_exponent!=19) return 0;
    mpq_ptr v[22];fields(s,v);
    for (unsigned i=0;i<22;++i) if (mpq_cmp_ui(v[i],i+1,i+2)) return 0;
    return 1;
}

static void edge_checks(void)
{
    mpq_t a,b;mpq_inits(a,b,NULL);mpq_set_ui(a,5,7);mpq_set_ui(b,11,13);
    CHECK(!weighted_remainder_log_interval_q(a,b,0));
    CHECK(!weighted_remainder_log_interval_q(a,b,241));
    CHECK(!weighted_remainder_log_interval_q(a,b,~0U));
    CHECK(!weighted_remainder_log_interval_q(a,a,2));
    CHECK(!weighted_remainder_log_interval_q(NULL,b,2));
    CHECK(!weighted_remainder_log_interval_q(a,NULL,2));
    CHECK(!mpq_cmp_ui(a,5,7) && !mpq_cmp_ui(b,11,13));
    CHECK(weighted_remainder_log_interval_q(a,b,1));
    CHECK(!mpq_sgn(a) && !mpq_sgn(b));
    WeightedRemainderConstants s;weighted_remainder_constants_init(&s);
    s.cutoff=17;s.log_tail_binary_exponent=19;mpq_ptr v[22];fields(&s,v);
    for (unsigned i=0;i<22;++i) mpq_set_ui(v[i],i+1,i+2);
    CHECK(!weighted_remainder_constants_compute(&s,0));CHECK(sentinel(&s));
    CHECK(!weighted_remainder_constants_compute(&s,241));CHECK(sentinel(&s));
    CHECK(!weighted_remainder_constants_compute(&s,~0U));CHECK(sentinel(&s));
    CHECK(!weighted_remainder_constants_compute(NULL,1));
    CHECK(weighted_remainder_constants_compute(&s,1));
    CHECK(s.cutoff==1 && s.log_tail_binary_exponent==1);
    CHECK(!mpq_cmp_ui(s.gamma_lower,1,2) && !mpq_cmp_ui(s.gamma_upper,7,12));
    CHECK(!mpq_cmp_ui(s.log_moment_lower,0,1) && !mpq_cmp_ui(s.log_moment_upper,5,1));
    CHECK(!mpq_sgn(s.gamma_harmonic_prefix));
    weighted_remainder_constants_clear(&s);mpq_clears(a,b,NULL);
    printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();mpq_t lo,hi;mpq_inits(lo,hi,NULL);
    WeightedRemainderConstants s;weighted_remainder_constants_init(&s);
    mpq_ptr v[22];fields(&s,v);char op;unsigned n;
    while (scanf(" %c %u",&op,&n)==2) {
        int ok;
        if (op=='L') {
            ok=weighted_remainder_log_interval_q(lo,hi,n);printf("L %d",ok);
            if (ok) gmp_printf(" %Qd %Qd",lo,hi);
        } else if (op=='C') {
            ok=weighted_remainder_constants_compute(&s,n);printf("C %d",ok);
            if (ok) {
                printf(" %u %u",s.cutoff,s.log_tail_binary_exponent);
                for (unsigned i=0;i<22;++i) gmp_printf(" %Qd",v[i]);
            }
        } else { fputs("invalid operation\n",stderr);return 2; }
        putchar('\n');
    }
    weighted_remainder_constants_clear(&s);mpq_clears(lo,hi,NULL);return 0;
}
