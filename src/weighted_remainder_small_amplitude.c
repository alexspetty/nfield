#include "weighted_remainder_small_amplitude.h"
#include "weighted_remainder_rect_internal.h"
#include "weighted_remainder_constants.h"

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };
#define FIELDS(X) X(three_prefix) X(three_lower) X(three_upper) X(catalan_prefix) X(catalan_lower) X(catalan_upper) \
    X(six_prefix) X(six_lower) X(six_upper) X(induced_prefix_rhs) X(induced_factor) X(induced_lower) X(induced_upper) \
    X(l_tail_upper) X(zeta_lower) X(zeta_upper) X(sqrt_three_lower) X(sqrt_three_upper) \
    X(eta_three_lower) X(eta_three_upper) X(eta_four_lower) X(eta_four_upper) \
    X(eta_six_direct_lower) X(eta_six_direct_upper) X(eta_six_relation_lower) X(eta_six_relation_upper)

void weighted_remainder_small_amplitude_init(WeightedRemainderSmallAmplitude *s)
{
    s->cutoff=s->zeta_cutoff=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}
void weighted_remainder_small_amplitude_clear(WeightedRemainderSmallAmplitude *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}
static int character(unsigned q,unsigned n)
{
    unsigned r=n%q;
    return r==1?1:r==q-1?-1:0;
}
static void prefix(mpq_t out,unsigned q,unsigned N)
{
    mpq_t c;mpq_init(c);
    for (unsigned n=1;n<=N;++n) {
        mpq_set_si(c,character(q,n),n*n);mpq_canonicalize(c);mpq_add(out,out,c);
    }
    mpq_clear(c);
}
static void half_minus_product(mpq_t outl,mpq_t outu,
    const mpq_t al,const mpq_t au,const mpq_t bl,const mpq_t bu)
{
    mpq_t l,u,c;mpq_inits(l,u,c,NULL);wr_product(l,u,al,au,bl,bu);mpq_set_ui(c,1,2);
    mpq_sub(outl,c,u);mpq_sub(outu,c,l);mpq_clears(l,u,c,NULL);
}
int weighted_remainder_small_amplitude_compute(WeightedRemainderSmallAmplitude *out,unsigned N,unsigned K)
{
    if (!out || N<1 || N>MAX || K<1 || K>MAX) return 0;
    WeightedRemainderSmallAmplitude s;weighted_remainder_small_amplitude_init(&s);s.cutoff=N;s.zeta_cutoff=K;
    prefix(s.three_prefix,3,N);prefix(s.catalan_prefix,4,N);prefix(s.six_prefix,6,N);
    mpq_set_ui(s.l_tail_upper,1,N);
    mpq_sub(s.three_lower,s.three_prefix,s.l_tail_upper);mpq_add(s.three_upper,s.three_prefix,s.l_tail_upper);
    mpq_sub(s.catalan_lower,s.catalan_prefix,s.l_tail_upper);mpq_add(s.catalan_upper,s.catalan_prefix,s.l_tail_upper);
    mpq_sub(s.six_lower,s.six_prefix,s.l_tail_upper);mpq_add(s.six_upper,s.six_prefix,s.l_tail_upper);
    mpq_t c,l,u,a,b;mpq_inits(c,l,u,a,b,NULL);prefix(l,3,N/2);mpq_div_2exp(l,l,2);
    mpq_add(s.induced_prefix_rhs,s.three_prefix,l);mpq_set_ui(s.induced_factor,5,4);
    mpq_mul(s.induced_lower,s.three_lower,s.induced_factor);mpq_mul(s.induced_upper,s.three_upper,s.induced_factor);
    WeightedRemainderConstants constants;weighted_remainder_constants_init(&constants);
    WeightedRemainderTrig trig;weighted_remainder_trig_init(&trig);mpz_t one;mpz_init_set_ui(one,1);
    int ok=weighted_remainder_constants_compute(&constants,1) &&
        weighted_remainder_trig_compute(&trig,6,one) &&
        weighted_remainder_zeta_three_interval_q(s.zeta_lower,s.zeta_upper,K);
    if (ok) {
        /* cot(pi/6)=sqrt(3), identified by an exact Lean theorem. */
        mpq_set(s.sqrt_three_lower,trig.cot_lower);mpq_set(s.sqrt_three_upper,trig.cot_upper);
        mpq_mul(a,s.sqrt_three_lower,constants.pi_lower);mpq_mul(b,s.sqrt_three_upper,constants.pi_upper);
        mpq_div(a,a,s.zeta_upper);mpq_div(b,b,s.zeta_lower);
        mpq_set_ui(c,3,52);mpq_mul(l,a,c);mpq_mul(u,b,c);
        half_minus_product(s.eta_three_lower,s.eta_three_upper,l,u,s.three_lower,s.three_upper);
        mpq_set_ui(c,9,91);mpq_mul(l,a,c);mpq_mul(u,b,c);
        half_minus_product(s.eta_six_direct_lower,s.eta_six_direct_upper,l,u,s.six_lower,s.six_upper);
        mpq_set_ui(c,1,7);mpq_div(l,constants.pi_lower,s.zeta_upper);mpq_div(u,constants.pi_upper,s.zeta_lower);
        mpq_mul(l,l,c);mpq_mul(u,u,c);
        half_minus_product(s.eta_four_lower,s.eta_four_upper,l,u,s.catalan_lower,s.catalan_upper);
        mpq_set_ui(c,15,7);mpq_mul(s.eta_six_relation_lower,s.eta_three_lower,c);
        mpq_mul(s.eta_six_relation_upper,s.eta_three_upper,c);mpq_set_ui(c,4,7);
        mpq_sub(s.eta_six_relation_lower,s.eta_six_relation_lower,c);
        mpq_sub(s.eta_six_relation_upper,s.eta_six_relation_upper,c);
        out->cutoff=N;out->zeta_cutoff=K;
#define COPY(f) mpq_set(out->f,s.f);
        FIELDS(COPY)
#undef COPY
    }
    weighted_remainder_trig_clear(&trig);weighted_remainder_constants_clear(&constants);mpz_clear(one);
    mpq_clears(c,l,u,a,b,NULL);weighted_remainder_small_amplitude_clear(&s);return ok;
}
