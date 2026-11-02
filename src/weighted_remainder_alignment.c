#include "weighted_remainder_alignment.h"
#include <string.h>

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };
#define FIELDS(X) X(log_modulus_lower) X(log_modulus_upper) \
    X(reset_product) X(reset_log_lower) X(reset_log_upper) \
    X(alignment_factor_correction) X(alignment_product_lower) X(alignment_product_upper) \
    X(alignment_log_correction_lower) X(alignment_log_correction_upper) \
    X(base_log_prefix_lower) X(base_log_prefix_upper) X(base_log_tail_upper) \
    X(alignment_log_lower) X(alignment_log_upper) \
    X(reset_prefix) X(alignment_prefix) X(retained_mass) X(finite_g) X(exact_reset) X(triangular_sum) \
    X(error_bound_prefix) X(error_tail_upper) \
    X(reset_main_lower) X(reset_main_upper) X(alignment_main_lower) X(alignment_main_upper) \
    X(reset_error_prefix_lower) X(reset_error_prefix_upper) \
    X(alignment_error_prefix_lower) X(alignment_error_prefix_upper) \
    X(reset_raw_lower) X(reset_raw_upper) X(alignment_raw_lower) X(alignment_raw_upper) \
    X(reset_refined_lower) X(reset_refined_upper) X(alignment_refined_lower) X(alignment_refined_upper) \
    X(reset_lower) X(reset_upper) X(alignment_lower) X(alignment_upper) X(full_g_lower) X(full_g_upper) \
    X(limiting_factor_product) X(reset_factor_loss_sum) X(alignment_factor_loss_sum) \
    X(reset_log_loss_lower) X(reset_log_loss_upper) X(alignment_log_loss_lower) X(alignment_log_loss_upper)
#define LOCAL_FIELDS(X) X(coefficient) X(main_lower) X(main_upper) X(error_lower) X(error_upper) X(error_bound) \
    X(log_lower) X(log_upper) X(nu_lower) X(nu_upper) X(gamma_lower) X(gamma_upper) \
    X(totient_ratio) X(mobius_sum)

static unsigned gcd_u(unsigned a,unsigned b)
{
    while (b) { unsigned r=a%b;a=b;b=r; }return a;
}
static int prime_u(unsigned p)
{
    if (p<2) return 0;
    for (unsigned d=2;d<=p/d;++d) if (p%d==0) return 0;
    return 1;
}
static int moebius_u(unsigned n)
{
    int sign=1;
    for (unsigned p=2;p<=n/p;++p) if (n%p==0) {
        n/=p;sign=-sign;if (n%p==0) return 0;
    }
    return n>1 ? -sign : sign;
}
static void scale_add(mpq_t lo,mpq_t hi,const mpq_t a,const mpq_t b,const mpq_t c)
{
    mpq_t l,h;mpq_inits(l,h,NULL);mpq_mul(l,a,c);mpq_mul(h,b,c);
    if (mpq_sgn(c)<0) mpq_swap(l,h);
    mpq_add(lo,lo,l);mpq_add(hi,hi,h);mpq_clears(l,h,NULL);
}
static void product(mpq_t lo,mpq_t hi,const mpq_t al,const mpq_t ah,const mpq_t bl,const mpq_t bh)
{
    mpq_t l,h,t;mpq_inits(l,h,t,NULL);mpq_mul(l,al,bl);mpq_set(h,l);
    mpq_srcptr a[2]={al,ah},b[2]={bl,bh};
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_mul(t,a[i],b[j]);if (mpq_cmp(t,l)<0) mpq_set(l,t);
        if (mpq_cmp(t,h)>0) mpq_set(h,t);
    }
    mpq_set(lo,l);mpq_set(hi,h);mpq_clears(l,h,t,NULL);
}
static void bound_q(mpq_t out,unsigned k)
{
    unsigned sigma=0;for (unsigned d=1;d<=k;++d) if (k%d==0) sigma+=d;
    mpq_set_ui(out,sigma,12UL*k*k*k);mpq_canonicalize(out);
}
void weighted_remainder_harmonic_local_init(WeightedRemainderHarmonicLocal *s)
{
    s->period=s->constant_cutoff=0;
#define INIT(f) mpq_init(s->f);
    LOCAL_FIELDS(INIT)
#undef INIT
}
void weighted_remainder_harmonic_local_clear(WeightedRemainderHarmonicLocal *s)
{
#define CLEAR(f) mpq_clear(s->f);
    LOCAL_FIELDS(CLEAR)
#undef CLEAR
}
static void local_compute(WeightedRemainderHarmonicLocal *s,unsigned k,
                          const WeightedRemainderConstants *constants)
{
    s->period=k;s->constant_cutoff=constants->cutoff;
    mpq_t c,t,ll,lh;mpq_inits(c,t,ll,lh,NULL);
    weighted_remainder_weight_q(s->coefficient,k);
    mpq_set_ui(c,k,1);mpq_mul(s->coefficient,s->coefficient,c);
    weighted_remainder_log_interval_q(s->log_lower,s->log_upper,k);
    unsigned phi=k,n=k;
    for (unsigned p=2;p<=n;++p) if (n%p==0) {
        phi-=phi/p;do { n/=p; } while (n%p==0);
        weighted_remainder_log_interval_q(ll,lh,p);mpq_set_ui(c,1,p-1);
        scale_add(s->nu_lower,s->nu_upper,ll,lh,c);
    }
    mpq_set_ui(s->totient_ratio,phi,k*k);mpq_canonicalize(s->totient_ratio);
    for (unsigned d=1;d<=k;++d) if (k%d==0) {
        mpq_set_si(c,moebius_u(d),1);mpq_add(s->mobius_sum,s->mobius_sum,c);
    }
    mpq_set(s->gamma_lower,constants->gamma_lower);mpq_set(s->gamma_upper,constants->gamma_upper);
    mpq_add(s->main_lower,s->log_lower,s->gamma_lower);mpq_add(s->main_lower,s->main_lower,s->nu_lower);
    mpq_add(s->main_upper,s->log_upper,s->gamma_upper);mpq_add(s->main_upper,s->main_upper,s->nu_upper);
    mpq_mul(s->main_lower,s->main_lower,s->totient_ratio);mpq_mul(s->main_upper,s->main_upper,s->totient_ratio);
    mpq_sub(s->error_lower,s->coefficient,s->main_upper);mpq_sub(s->error_upper,s->coefficient,s->main_lower);
    bound_q(s->error_bound,k);
    mpq_clears(c,t,ll,lh,NULL);
}
int weighted_remainder_harmonic_local_compute(WeightedRemainderHarmonicLocal *out,unsigned k,unsigned N)
{
    if (!out || k<2 || k>MAX || N<1 || N>MAX) return 0;
    WeightedRemainderConstants c;weighted_remainder_constants_init(&c);
    weighted_remainder_constants_compute(&c,N);
    WeightedRemainderHarmonicLocal s;weighted_remainder_harmonic_local_init(&s);local_compute(&s,k,&c);
    WeightedRemainderHarmonicLocal old=*out;*out=s;weighted_remainder_harmonic_local_clear(&old);
    weighted_remainder_constants_clear(&c);return 1;
}
void weighted_remainder_alignment_init(WeightedRemainderAlignment *s)
{
    mpz_init(s->modulus);s->period_cutoff=s->constant_cutoff=s->prime_cutoff=0;
    memset(s->valuations,0,sizeof s->valuations);
    s->prime_count=s->reset_exact=s->triangular_available=0;
    weighted_remainder_constants_init(&s->constants);
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}
void weighted_remainder_alignment_clear(WeightedRemainderAlignment *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
    weighted_remainder_constants_clear(&s->constants);mpz_clear(s->modulus);
}
int weighted_remainder_alignment_lcm_z(mpz_t out,unsigned m)
{
    if (!out || m<1 || m>MAX) return 0;
    mpz_t a;mpz_init_set_ui(a,1);for (unsigned k=2;k<=m;++k) mpz_lcm_ui(a,a,k);
    mpz_set(out,a);mpz_clear(a);return 1;
}
static int factor(unsigned *valuation,unsigned *count,const mpz_t modulus)
{
    if (mpz_sgn(modulus)<=0 || mpz_sizeinbase(modulus,2)>4096) return 0;
    mpz_t a;mpz_init_set(a,modulus);*count=0;
    for (unsigned p=2;p<=MAX;++p) if (prime_u(p)) {
        unsigned v=0;
        while (mpz_divisible_ui_p(a,p)) {
            mpz_divexact_ui(a,a,p);if (++v>MAX) { mpz_clear(a);return 0; }
        }
        valuation[p]=v;if (v) ++*count;
    }
    int ok=mpz_cmp_ui(a,1)==0;mpz_clear(a);return ok;
}
int weighted_remainder_alignment_compute(WeightedRemainderAlignment *out,
    const mpz_t modulus,unsigned M,unsigned N,unsigned P)
{
    if (!out || !modulus || M<2 || M>MAX || N<1 || N>MAX || P<1 || P>MAX) return 0;
    unsigned valuations[241]={0},count;
    if (!factor(valuations,&count,modulus)) return 0;
    WeightedRemainderAlignment s;weighted_remainder_alignment_init(&s);
    s.period_cutoff=M;s.constant_cutoff=N;s.prime_cutoff=P;s.prime_count=count;
    memcpy(s.valuations,valuations,sizeof valuations);mpz_set(s.modulus,modulus);
    weighted_remainder_constants_compute(&s.constants,N);
    mpq_t c,t,u,ll,lh,al,ah,bl,bh,bound,one;
    mpq_inits(c,t,u,ll,lh,al,ah,bl,bh,bound,one,NULL);mpq_set_ui(one,1,1);
    mpq_set(s.reset_product,one);mpq_set(s.alignment_factor_correction,one);mpq_set(s.limiting_factor_product,one);
    WeightedRemainderAlignmentLocal loc;weighted_remainder_alignment_local_init(&loc);
    for (unsigned p=2;p<=MAX;++p) if (prime_u(p)) {
        if (!valuations[p] && p>P) continue;
        weighted_remainder_log_interval_q(ll,lh,p);
        if (p<=P) {
            mpq_set_ui(c,1,p*p-1);scale_add(s.base_log_prefix_lower,s.base_log_prefix_upper,ll,lh,c);
        }
        if (!valuations[p]) continue;
        weighted_remainder_alignment_local_compute(&loc,p,valuations[p]);
        mpq_set_ui(c,valuations[p],1);scale_add(s.log_modulus_lower,s.log_modulus_upper,ll,lh,c);
        mpq_mul(s.reset_product,s.reset_product,loc.reset_factor);
        scale_add(s.reset_log_lower,s.reset_log_upper,ll,lh,loc.reset_average);
        mpq_div(c,loc.alignment_factor,loc.absent_factor);
        mpq_mul(s.alignment_factor_correction,s.alignment_factor_correction,c);
        mpq_sub(c,loc.alignment_average,loc.absent_average);
        scale_add(s.alignment_log_correction_lower,s.alignment_log_correction_upper,ll,lh,c);
        mpq_mul(s.limiting_factor_product,s.limiting_factor_product,loc.limiting_factor);
        mpq_add(s.reset_factor_loss_sum,s.reset_factor_loss_sum,loc.reset_factor_relative_loss);
        mpq_add(s.alignment_factor_loss_sum,s.alignment_factor_loss_sum,loc.alignment_factor_relative_loss);
        scale_add(s.reset_log_loss_lower,s.reset_log_loss_upper,ll,lh,loc.reset_average_loss);
        scale_add(s.alignment_log_loss_lower,s.alignment_log_loss_upper,ll,lh,loc.alignment_average_loss);
    }
    weighted_remainder_alignment_local_clear(&loc);
    weighted_remainder_log_interval_q(ll,lh,P);
    mpq_set_ui(c,4,P);mpq_canonicalize(c);mpq_mul(s.base_log_tail_upper,lh,c);
    mpq_set_ui(c,6,P);mpq_canonicalize(c);mpq_add(s.base_log_tail_upper,s.base_log_tail_upper,c);
    mpq_mul(s.alignment_product_lower,s.constants.leading_lower,s.alignment_factor_correction);
    mpq_mul(s.alignment_product_upper,s.constants.leading_upper,s.alignment_factor_correction);
    mpq_add(s.alignment_log_lower,s.base_log_prefix_lower,s.alignment_log_correction_lower);
    mpq_add(s.alignment_log_upper,s.base_log_prefix_upper,s.alignment_log_correction_upper);
    mpq_add(s.alignment_log_upper,s.alignment_log_upper,s.base_log_tail_upper);
    mpq_mul(bound,s.constants.zeta_two_upper,s.constants.zeta_three_upper);
    mpq_set_ui(c,1,12);mpq_mul(bound,bound,c);mpq_set_ui(s.error_bound_prefix,1,12);
    for (unsigned k=2;k<=M;++k) {
        WeightedRemainderHarmonicLocal h;weighted_remainder_harmonic_local_init(&h);local_compute(&h,k,&s.constants);
        mpq_set_ui(c,1,k);mpq_mul(t,h.coefficient,c);mpq_add(s.retained_mass,s.retained_mass,t);
        unsigned d=gcd_u(k,(unsigned)mpz_fdiv_ui(s.modulus,k));
        mpq_set_ui(c,d-1,3);mpq_canonicalize(c);mpq_mul(u,t,c);mpq_add(s.alignment_prefix,s.alignment_prefix,u);
        if (mpz_divisible_ui_p(s.modulus,k)) {
            mpq_add(s.reset_prefix,s.reset_prefix,h.coefficient);
            mpq_add(s.reset_error_prefix_lower,s.reset_error_prefix_lower,h.error_lower);
            mpq_add(s.reset_error_prefix_upper,s.reset_error_prefix_upper,h.error_upper);
        }
        mpq_set_ui(c,d,k);mpq_canonicalize(c);
        scale_add(s.alignment_error_prefix_lower,s.alignment_error_prefix_upper,h.error_lower,h.error_upper,c);
        mpq_add(s.error_bound_prefix,s.error_bound_prefix,h.error_bound);
        weighted_remainder_harmonic_local_clear(&h);
    }
    mpq_sub(s.error_tail_upper,bound,s.error_bound_prefix);
    mpq_sub(s.finite_g,s.retained_mass,s.reset_prefix);mpq_set_ui(c,2,3);mpq_mul(s.finite_g,s.finite_g,c);
    s.reset_exact=mpz_cmp_ui(s.modulus,M)<=0;
    if (s.reset_exact) mpq_set(s.exact_reset,s.reset_prefix);
    s.triangular_available=mpz_cmp_ui(s.modulus,MAX)<=0;
    if (s.triangular_available) {
        unsigned n=(unsigned)mpz_get_ui(s.modulus);
        for (unsigned j=1;j<=n;++j) {
            unsigned d=gcd_u(j,n);mpq_set_ui(t,d*d,j*n);mpq_canonicalize(t);
            mpq_add(s.triangular_sum,s.triangular_sum,t);
        }
    }
    mpq_add(bl,s.constants.gamma_lower,s.reset_log_lower);mpq_add(bh,s.constants.gamma_upper,s.reset_log_upper);
    mpq_mul(s.reset_main_lower,s.reset_product,bl);mpq_mul(s.reset_main_upper,s.reset_product,bh);
    mpq_sub(s.reset_main_lower,s.reset_main_lower,s.constants.gamma_upper);
    mpq_sub(s.reset_main_upper,s.reset_main_upper,s.constants.gamma_lower);
    mpq_add(bl,s.constants.gamma_lower,s.alignment_log_lower);mpq_add(bh,s.constants.gamma_upper,s.alignment_log_upper);
    product(s.alignment_main_lower,s.alignment_main_upper,s.alignment_product_lower,s.alignment_product_upper,bl,bh);
    mpq_sub(s.alignment_main_lower,s.alignment_main_lower,s.constants.gamma_upper);
    mpq_sub(s.alignment_main_upper,s.alignment_main_upper,s.constants.gamma_lower);
    mpq_sub(s.reset_raw_lower,s.reset_main_lower,bound);mpq_add(s.reset_raw_upper,s.reset_main_upper,bound);
    mpq_sub(s.alignment_raw_lower,s.alignment_main_lower,bound);mpq_add(s.alignment_raw_upper,s.alignment_main_upper,bound);
    mpq_sub(s.alignment_raw_lower,s.alignment_raw_lower,one);mpq_sub(s.alignment_raw_upper,s.alignment_raw_upper,one);
    mpq_set_ui(c,1,3);mpq_mul(s.alignment_raw_lower,s.alignment_raw_lower,c);mpq_mul(s.alignment_raw_upper,s.alignment_raw_upper,c);
    mpq_add(s.reset_refined_lower,s.reset_main_lower,s.reset_error_prefix_lower);
    mpq_sub(s.reset_refined_lower,s.reset_refined_lower,s.error_tail_upper);
    mpq_add(s.reset_refined_upper,s.reset_main_upper,s.reset_error_prefix_upper);
    mpq_add(s.reset_refined_upper,s.reset_refined_upper,s.error_tail_upper);
    mpq_add(s.alignment_refined_lower,s.alignment_main_lower,s.alignment_error_prefix_lower);
    mpq_sub(s.alignment_refined_lower,s.alignment_refined_lower,s.error_tail_upper);
    mpq_sub(s.alignment_refined_lower,s.alignment_refined_lower,one);mpq_mul(s.alignment_refined_lower,s.alignment_refined_lower,c);
    mpq_add(s.alignment_refined_upper,s.alignment_main_upper,s.alignment_error_prefix_upper);
    mpq_add(s.alignment_refined_upper,s.alignment_refined_upper,s.error_tail_upper);
    mpq_sub(s.alignment_refined_upper,s.alignment_refined_upper,one);mpq_mul(s.alignment_refined_upper,s.alignment_refined_upper,c);
    mpq_set(s.reset_lower,s.reset_prefix);mpq_set(s.reset_upper,s.reset_raw_upper);
    if (mpq_cmp(s.reset_refined_lower,s.reset_lower)>0) mpq_set(s.reset_lower,s.reset_refined_lower);
    if (mpq_cmp(s.reset_raw_lower,s.reset_lower)>0) mpq_set(s.reset_lower,s.reset_raw_lower);
    if (mpq_cmp(s.reset_refined_upper,s.reset_upper)<0) mpq_set(s.reset_upper,s.reset_refined_upper);
    if (s.reset_exact) { mpq_set(s.reset_lower,s.exact_reset);mpq_set(s.reset_upper,s.exact_reset); }
    mpq_set(s.alignment_lower,s.alignment_prefix);mpq_set(s.alignment_upper,s.alignment_raw_upper);
    if (mpq_cmp(s.alignment_refined_lower,s.alignment_lower)>0) mpq_set(s.alignment_lower,s.alignment_refined_lower);
    if (mpq_cmp(s.alignment_raw_lower,s.alignment_lower)>0) mpq_set(s.alignment_lower,s.alignment_raw_lower);
    if (mpq_cmp(s.alignment_refined_upper,s.alignment_upper)<0) mpq_set(s.alignment_upper,s.alignment_refined_upper);
    if (mpz_cmp_ui(s.modulus,1)==0) { mpq_set_ui(s.alignment_lower,0,1);mpq_set_ui(s.alignment_upper,0,1); }
    mpq_sub(s.full_g_lower,one,s.reset_upper);mpq_sub(s.full_g_upper,one,s.reset_lower);
    mpq_set_ui(c,2,3);mpq_mul(s.full_g_lower,s.full_g_lower,c);mpq_mul(s.full_g_upper,s.full_g_upper,c);
    mpq_clears(c,t,u,ll,lh,al,ah,bl,bh,bound,one,NULL);
    WeightedRemainderAlignment old=*out;*out=s;weighted_remainder_alignment_clear(&old);return 1;
}
