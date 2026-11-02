#include "weighted_remainder_alignment_growth.h"

#define FIELDS(X) X(exp_gamma_lower) X(exp_gamma_upper) X(kappa_lower) X(kappa_upper) X(Gamma_lower) X(Gamma_upper) \
 X(log_scale_lower) X(log_scale_upper) X(reset_leading_lower) X(reset_leading_upper) X(alignment_leading_lower) X(alignment_leading_upper) \
 X(log_log_lower) X(log_log_upper) X(normalizer_lower) X(normalizer_upper) \
 X(normalized_reset_lower) X(normalized_reset_upper) X(normalized_alignment_lower) X(normalized_alignment_upper) \
 X(normalized_negative_g_lower) X(normalized_negative_g_upper) \
 X(mertens_inverse_product) X(mertens_plus_product) X(mertens_prime_log_lower) X(mertens_prime_log_upper) \
 X(limiting_prime_log_lower) X(limiting_prime_log_upper) X(finite_alignment_product) \
 X(reset_relative_product_loss) X(alignment_relative_product_loss) X(lcm_factor_loss_upper) X(lcm_log_loss_upper) \
 X(amplitude_log_constant_upper) X(tower_reset_upper) X(tower_alignment_upper) X(tower_combined_upper)

void weighted_remainder_alignment_growth_init(WeightedRemainderAlignmentGrowth *s)
{
    weighted_remainder_alignment_init(&s->values);mpz_init(s->lcm);
    s->scale=s->lcm_match=s->normalized_available=s->lcm_bounds_available=s->tower_prime=s->sqrt_floor=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}
void weighted_remainder_alignment_growth_clear(WeightedRemainderAlignmentGrowth *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
    weighted_remainder_alignment_clear(&s->values);mpz_clear(s->lcm);
}
static int prime(unsigned p)
{
    if (p<2) return 0;
    for (unsigned d=2;d<=p/d;++d) if (p%d==0) return 0;
    return 1;
}
static void add_scaled(mpq_t lo,mpq_t hi,const mpq_t l,const mpq_t h,const mpq_t c)
{
    mpq_t a,b;mpq_inits(a,b,NULL);mpq_mul(a,l,c);mpq_mul(b,h,c);
    mpq_add(lo,lo,a);mpq_add(hi,hi,b);mpq_clears(a,b,NULL);
}
static void divide_positive(mpq_t lo,mpq_t hi,const mpq_t al,const mpq_t ah,const mpq_t dl,const mpq_t dh)
{
    mpq_t a,b,t;mpq_inits(a,b,t,NULL);mpq_div(a,al,dl);mpq_set(b,a);
    mpq_srcptr x[2]={al,ah},y[2]={dl,dh};
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_div(t,x[i],y[j]);if (mpq_cmp(t,a)<0) mpq_set(a,t);if (mpq_cmp(t,b)>0) mpq_set(b,t);
    }
    mpq_set(lo,a);mpq_set(hi,b);mpq_clears(a,b,t,NULL);
}
/* Harmonic denominators can exceed the exponential helper's 256-bit
 * input domain at large N. Round outward before calling that helper;
 * the exact gamma enclosure is retained, with at most 10^-24 added
 * at either endpoint. The resulting components fit its public domain. */
static void gamma_grid(mpq_t out,const mpq_t x,int upward)
{
    mpz_t grid,n;mpz_inits(grid,n,NULL);mpz_ui_pow_ui(grid,10,24);
    mpz_mul(n,mpq_numref(x),grid);
    if (upward) mpz_cdiv_q(n,n,mpq_denref(x));
    else mpz_fdiv_q(n,n,mpq_denref(x));
    mpq_set_num(out,n);mpq_set_den(out,grid);mpq_canonicalize(out);
    mpz_clears(grid,n,NULL);
}
int weighted_remainder_alignment_growth_compute(WeightedRemainderAlignmentGrowth *out,
    const mpz_t modulus,unsigned m,unsigned M,unsigned N,unsigned P)
{
    if (!out || m<1 || m>WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    WeightedRemainderAlignmentGrowth s;weighted_remainder_alignment_growth_init(&s);
    if (!weighted_remainder_alignment_compute(&s.values,modulus,M,N,P)) {
        weighted_remainder_alignment_growth_clear(&s);return 0;
    }
    s.scale=m;weighted_remainder_alignment_lcm_z(s.lcm,m);s.lcm_match=mpz_cmp(s.lcm,s.values.modulus)==0;
    s.normalized_available=mpz_cmp_ui(s.values.modulus,3)>=0;s.lcm_bounds_available=s.lcm_match && m>=4;
    while ((s.sqrt_floor+1)*(s.sqrt_floor+1)<=m) ++s.sqrt_floor;
    WeightedRemainderConstants *ct=&s.values.constants;
    mpq_t gamma_lo,gamma_hi;mpq_inits(gamma_lo,gamma_hi,NULL);
    gamma_grid(gamma_lo,ct->gamma_lower,0);gamma_grid(gamma_hi,ct->gamma_upper,1);
    int exp_ok=weighted_remainder_small_exp_interval_q(s.exp_gamma_lower,s.exp_gamma_upper,gamma_lo,gamma_hi);
    mpq_clears(gamma_lo,gamma_hi,NULL);
    if (!exp_ok) {
        weighted_remainder_alignment_growth_clear(&s);return 0;
    }
    mpq_t c,t,u,ll,lh,one,al,ah;mpq_inits(c,t,u,ll,lh,one,al,ah,NULL);mpq_set_ui(one,1,1);
    mpq_div(s.kappa_lower,s.exp_gamma_lower,ct->zeta_two_upper);
    mpq_div(s.kappa_upper,s.exp_gamma_upper,ct->zeta_two_lower);
    mpq_set_ui(c,1,3);mpq_mul(s.Gamma_lower,s.kappa_lower,c);mpq_mul(s.Gamma_upper,s.kappa_upper,c);
    weighted_remainder_log_interval_q(s.log_scale_lower,s.log_scale_upper,m);
    mpq_mul(t,s.log_scale_lower,s.log_scale_lower);mpq_mul(u,s.log_scale_upper,s.log_scale_upper);
    mpq_mul(s.reset_leading_lower,t,s.kappa_lower);mpq_mul(s.reset_leading_upper,u,s.kappa_upper);
    mpq_mul(s.alignment_leading_lower,t,s.Gamma_lower);mpq_mul(s.alignment_leading_upper,u,s.Gamma_upper);
    if (s.normalized_available) {
        int ok=weighted_remainder_rational_log_interval_q(s.log_log_lower,t,s.values.log_modulus_lower) &&
          weighted_remainder_rational_log_interval_q(u,s.log_log_upper,s.values.log_modulus_upper);
        if (!ok || mpq_sgn(s.log_log_lower)<=0) {
            mpq_clears(c,t,u,ll,lh,one,al,ah,NULL);weighted_remainder_alignment_growth_clear(&s);return 0;
        }
        mpq_mul(s.normalizer_lower,s.log_log_lower,s.log_log_lower);mpq_mul(s.normalizer_upper,s.log_log_upper,s.log_log_upper);
        divide_positive(s.normalized_reset_lower,s.normalized_reset_upper,s.values.reset_lower,s.values.reset_upper,s.normalizer_lower,s.normalizer_upper);
        divide_positive(s.normalized_alignment_lower,s.normalized_alignment_upper,s.values.alignment_lower,s.values.alignment_upper,s.normalizer_lower,s.normalizer_upper);
        mpq_neg(al,s.values.full_g_upper);mpq_neg(ah,s.values.full_g_lower);
        divide_positive(s.normalized_negative_g_lower,s.normalized_negative_g_upper,al,ah,s.normalizer_lower,s.normalizer_upper);
    }
    mpq_set(s.mertens_inverse_product,one);mpq_set(s.mertens_plus_product,one);mpq_set(s.finite_alignment_product,one);
    for (unsigned p=2;p<=WEIGHTED_REMAINDER_EXACT_MAX;++p) if (prime(p)) {
        if (p<=m) {
            mpq_set_ui(c,p,p-1);mpq_mul(s.mertens_inverse_product,s.mertens_inverse_product,c);
            mpq_set_ui(c,p+1,p);mpq_mul(s.mertens_plus_product,s.mertens_plus_product,c);
            weighted_remainder_log_interval_q(ll,lh,p);mpq_set_ui(c,1,p);
            add_scaled(s.mertens_prime_log_lower,s.mertens_prime_log_upper,ll,lh,c);
            mpq_set_ui(c,1,p-1);add_scaled(s.limiting_prime_log_lower,s.limiting_prime_log_upper,ll,lh,c);
        }
        if (s.values.valuations[p]) {
            WeightedRemainderAlignmentLocal loc;weighted_remainder_alignment_local_init(&loc);
            weighted_remainder_alignment_local_compute(&loc,p,s.values.valuations[p]);
            mpq_mul(s.finite_alignment_product,s.finite_alignment_product,loc.alignment_factor);
            weighted_remainder_alignment_local_clear(&loc);
            if (s.values.prime_count==1) s.tower_prime=p;
        }
    }
    mpq_div(t,s.values.reset_product,s.values.limiting_factor_product);mpq_sub(s.reset_relative_product_loss,one,t);
    mpq_div(t,s.finite_alignment_product,s.values.limiting_factor_product);mpq_sub(s.alignment_relative_product_loss,one,t);
    if (s.lcm_bounds_available) {
        mpq_set_ui(s.lcm_factor_loss_upper,3,s.sqrt_floor);mpq_canonicalize(s.lcm_factor_loss_upper);
        mpq_set_ui(c,9,s.sqrt_floor);mpq_canonicalize(c);mpq_mul(s.lcm_log_loss_upper,c,s.log_scale_upper);
    }
    mpq_abs(t,ct->kappa_lower);mpq_abs(u,ct->kappa_upper);if (mpq_cmp(u,t)>0) mpq_set(t,u);
    mpq_set_ui(c,2,1);mpq_add(t,t,c);mpq_mul(s.amplitude_log_constant_upper,ct->leading_upper,t);
    mpq_set_ui(c,6,1);mpq_mul(t,ct->zeta_three_lower,c);mpq_div(u,ct->zeta_four_upper,t);
    mpq_add(s.amplitude_log_constant_upper,s.amplitude_log_constant_upper,u);
    if (s.tower_prime) {
        weighted_remainder_log_interval_q(ll,lh,s.tower_prime);
        mpq_add(t,one,lh);mpq_set_ui(c,4,s.tower_prime);mpq_canonicalize(c);mpq_mul(s.tower_reset_upper,t,c);
        mpq_mul(s.tower_alignment_upper,s.amplitude_log_constant_upper,s.tower_reset_upper);
        mpq_set_ui(c,1,3);mpq_mul(s.tower_alignment_upper,s.tower_alignment_upper,c);
        mpq_add(s.tower_combined_upper,s.tower_reset_upper,s.tower_alignment_upper);
    }
    mpq_clears(c,t,u,ll,lh,one,al,ah,NULL);
    WeightedRemainderAlignmentGrowth old=*out;*out=s;weighted_remainder_alignment_growth_clear(&old);return 1;
}
