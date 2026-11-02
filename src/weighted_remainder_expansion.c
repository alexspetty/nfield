#include "weighted_remainder_expansion.h"

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };
#define FIELDS(X) X(delta) X(jordan_three) X(totient_ratio) X(rho) X(prime_factor_plus_product) \
    X(log_lower) X(log_upper) X(nu_lower) X(nu_upper) X(mobius_inverse) X(mobius_log_lower) X(mobius_log_upper) \
    X(harmonic_prefix) X(harmonic_error_raw_lower) X(harmonic_error_raw_upper) \
    X(harmonic_error_lower) X(harmonic_error_upper) X(harmonic_error_bound) \
    X(seed_main_lower) X(seed_main_upper) X(seed_error_bound) X(seed_lower) X(seed_upper) \
    X(main_lower) X(main_upper) X(error_upper) X(amplitude_lower) X(amplitude_upper) \
    X(prime_power_main_lower) X(prime_power_main_upper) X(prime_leading_lower) X(prime_leading_upper)

void weighted_remainder_expansion_init(WeightedRemainderExpansion *s)
{
    s->conductor=s->amplitude_expansion_available=s->prime_base=s->prime_exponent=0;
    weighted_remainder_constants_init(&s->constants);
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}

void weighted_remainder_expansion_clear(WeightedRemainderExpansion *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
    weighted_remainder_constants_clear(&s->constants);
}

static int moebius(unsigned n)
{
    int sign=1;
    for (unsigned p=2;p*p<=n;++p) if (n%p==0) {
        n/=p;sign=-sign;if (n%p==0) return 0;
    }
    return n>1 ? -sign : sign;
}

static void product(mpq_t lo,mpq_t hi,const mpq_t al,const mpq_t ah,
                      const mpq_t bl,const mpq_t bh)
{
    mpq_t l,h,t;mpq_inits(l,h,t,NULL);mpq_mul(l,al,bl);mpq_set(h,l);
    mpq_srcptr a[2]={al,ah},b[2]={bl,bh};
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_mul(t,a[i],b[j]);if (mpq_cmp(t,l)<0) mpq_set(l,t);
        if (mpq_cmp(t,h)>0) mpq_set(h,t);
    }
    mpq_set(lo,l);mpq_set(hi,h);mpq_clears(l,h,t,NULL);
}

int weighted_remainder_expansion_compute(WeightedRemainderExpansion *out,unsigned q,unsigned N)
{
    if (!out || q<1 || q>MAX || N<1 || N>MAX) return 0;
    WeightedRemainderExpansion s;weighted_remainder_expansion_init(&s);
    s.conductor=q;s.amplitude_expansion_available=q>=2;
    weighted_remainder_constants_compute(&s.constants,N);
    weighted_remainder_amplitude_factors_q(s.delta,s.jordan_three,q);
    weighted_remainder_log_interval_q(s.log_lower,s.log_upper,q);
    mpq_t c,t,u,ll,lh,al,ah,bl,bh,q2,q3,q4;
    mpq_inits(c,t,u,ll,lh,al,ah,bl,bh,q2,q3,q4,NULL);
    mpq_set_ui(q2,q*q,1);mpq_set_ui(q3,q*q*q,1);mpq_mul(q4,q2,q2);
    unsigned phi=q,n=q,plus=1,distinct=0;
    for (unsigned p=2;p<=n;++p) if (n%p==0) {
        phi-=phi/p;plus*=p+1;++distinct;s.prime_base=p;s.prime_exponent=0;
        do { n/=p;++s.prime_exponent; } while (n%p==0);
        weighted_remainder_log_interval_q(ll,lh,p);mpq_set_ui(c,1,p-1);
        mpq_mul(t,ll,c);mpq_add(s.nu_lower,s.nu_lower,t);
        mpq_mul(t,lh,c);mpq_add(s.nu_upper,s.nu_upper,t);
    }
    if (distinct!=1) s.prime_base=s.prime_exponent=0;
    mpq_set_ui(s.totient_ratio,phi,q);mpq_canonicalize(s.totient_ratio);
    mpq_div(s.rho,s.totient_ratio,s.delta);mpq_set_ui(s.prime_factor_plus_product,plus,1);
    for (unsigned d=1;d<=q;++d) {
        if (d<q) { mpq_set_ui(c,1,d);mpq_add(s.harmonic_prefix,s.harmonic_prefix,c); }
        if (q%d) continue;
        mpq_set_si(c,moebius(d),d);mpq_canonicalize(c);mpq_add(s.mobius_inverse,s.mobius_inverse,c);
        weighted_remainder_log_interval_q(ll,lh,d);mpq_mul(t,c,ll);mpq_mul(u,c,lh);
        if (mpq_cmp(t,u)>0) mpq_swap(t,u);
        mpq_add(s.mobius_log_lower,s.mobius_log_lower,t);mpq_add(s.mobius_log_upper,s.mobius_log_upper,u);
    }
    mpq_set_ui(c,1,2*q);
    mpq_sub(s.harmonic_error_raw_lower,s.harmonic_prefix,s.log_upper);
    mpq_sub(s.harmonic_error_raw_lower,s.harmonic_error_raw_lower,s.constants.gamma_upper);
    mpq_add(s.harmonic_error_raw_lower,s.harmonic_error_raw_lower,c);
    mpq_sub(s.harmonic_error_raw_upper,s.harmonic_prefix,s.log_lower);
    mpq_sub(s.harmonic_error_raw_upper,s.harmonic_error_raw_upper,s.constants.gamma_lower);
    mpq_add(s.harmonic_error_raw_upper,s.harmonic_error_raw_upper,c);
    mpq_set_ui(s.harmonic_error_bound,1,12*q*q);
    mpq_neg(t,s.harmonic_error_bound);
    mpq_set(s.harmonic_error_lower,mpq_cmp(s.harmonic_error_raw_lower,t)>0?s.harmonic_error_raw_lower:t);
    if (mpq_sgn(s.harmonic_error_raw_upper)<0) mpq_set(s.harmonic_error_upper,s.harmonic_error_raw_upper);
    mpq_add(bl,s.log_lower,s.constants.kappa_lower);mpq_add(bh,s.log_upper,s.constants.kappa_upper);
    product(s.seed_main_lower,s.seed_main_upper,s.constants.zeta_two_lower,s.constants.zeta_two_upper,bl,bh);
    mpq_div(s.seed_main_lower,s.seed_main_lower,q2);mpq_div(s.seed_main_upper,s.seed_main_upper,q2);
    mpq_set_ui(c,2,1);mpq_mul(t,q3,c);
    mpq_div(u,s.constants.zeta_three_upper,t);mpq_sub(s.seed_main_lower,s.seed_main_lower,u);
    mpq_div(u,s.constants.zeta_three_lower,t);mpq_sub(s.seed_main_upper,s.seed_main_upper,u);
    mpq_set_ui(c,12,1);mpq_mul(t,q4,c);mpq_div(s.seed_error_bound,s.constants.zeta_four_upper,t);
    mpq_sub(s.seed_lower,s.seed_main_lower,s.seed_error_bound);mpq_set(s.seed_upper,s.seed_main_upper);
    if (s.amplitude_expansion_available) {
        mpq_add(bl,bl,s.nu_lower);mpq_add(bh,bh,s.nu_upper);
        mpq_div(c,s.rho,q2);
        mpq_mul(al,s.constants.leading_lower,c);mpq_mul(ah,s.constants.leading_upper,c);
        product(s.main_lower,s.main_upper,al,ah,bl,bh);
        mpq_mul(t,t,s.constants.zeta_three_lower);mpq_mul(t,t,s.delta);
        mpq_div(s.error_upper,s.constants.zeta_four_upper,t);
        mpq_mul(s.error_upper,s.error_upper,s.prime_factor_plus_product);
        mpq_sub(s.amplitude_lower,s.main_lower,s.error_upper);mpq_add(s.amplitude_upper,s.main_upper,s.error_upper);
        if (s.prime_base) {
            weighted_remainder_log_interval_q(ll,lh,s.prime_base);
            mpq_set_ui(c,s.prime_exponent,1);mpq_mul(bl,ll,c);mpq_mul(bh,lh,c);
            mpq_add(bl,bl,s.constants.kappa_lower);mpq_add(bh,bh,s.constants.kappa_upper);
            mpq_set_ui(c,1,s.prime_base-1);mpq_mul(t,ll,c);mpq_mul(u,lh,c);
            mpq_add(bl,bl,t);mpq_add(bh,bh,u);
            product(s.prime_power_main_lower,s.prime_power_main_upper,al,ah,bl,bh);
            if (s.prime_exponent==1) {
                product(s.prime_leading_lower,s.prime_leading_upper,s.constants.leading_lower,s.constants.leading_upper,ll,lh);
                mpq_div(s.prime_leading_lower,s.prime_leading_lower,q2);mpq_div(s.prime_leading_upper,s.prime_leading_upper,q2);
            }
        }
    }
    mpq_clears(c,t,u,ll,lh,al,ah,bl,bh,q2,q3,q4,NULL);
    /* Transfer the completed GMP ownership only after every input read and
     * computation. The previous initialized output is cleared once. */
    WeightedRemainderExpansion previous=*out;*out=s;weighted_remainder_expansion_clear(&previous);
    return 1;
}
