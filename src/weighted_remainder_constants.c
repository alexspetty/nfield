#include "weighted_remainder_constants.h"

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX, LOG_TERMS=24 };

#define FIELDS(X) X(pi_lower) X(pi_upper) X(zeta_two_lower) X(zeta_two_upper) \
    X(zeta_three_lower) X(zeta_three_upper) X(zeta_four_lower) X(zeta_four_upper) \
    X(gamma_harmonic_prefix) X(log_n_lower) X(log_n_upper) X(gamma_lower) X(gamma_upper) \
    X(log_moment_prefix_lower) X(log_moment_prefix_upper) X(log_moment_tail_upper) \
    X(log_moment_lower) X(log_moment_upper) X(kappa_lower) X(kappa_upper) \
    X(leading_lower) X(leading_upper)

/* 0<=r<=1/3. The final power is r^(2*LOG_TERMS+1). The proven
 * remainder is 2*power/(1-r^2), without an extra odd denominator. */
static void log_kernel(mpq_t lo,mpq_t hi,const mpq_t r)
{
    mpq_t sum,power,ratio,c,t,error;mpq_inits(sum,power,ratio,c,t,error,NULL);
    mpq_set(power,r);mpq_mul(ratio,r,r);
    for (unsigned k=0;k<LOG_TERMS;++k) {
        mpq_set_ui(c,2,2*k+1);mpq_mul(t,c,power);mpq_add(sum,sum,t);
        mpq_mul(power,power,ratio);
    }
    mpq_set_ui(c,1,1);mpq_sub(c,c,ratio);mpq_div(error,power,c);
    mpq_set_ui(c,2,1);mpq_mul(error,error,c);
    mpq_add(hi,sum,error);mpq_set(lo,sum);
    mpq_clears(sum,power,ratio,c,t,error,NULL);
}

static void outward_grid(mpq_t out,const mpq_t x,int upward)
{
    mpz_t grid,n,k;mpz_inits(grid,n,k,NULL);mpz_ui_pow_ui(grid,10,24);
    mpz_mul(n,mpq_numref(x),grid);
    if (upward) mpz_cdiv_q(k,n,mpq_denref(x));
    else mpz_fdiv_q(k,n,mpq_denref(x));
    mpq_set_num(out,k);mpq_set_den(out,grid);mpq_canonicalize(out);
    mpz_clears(grid,n,k,NULL);
}

int weighted_remainder_log_interval_q(mpq_t lo,mpq_t hi,unsigned n)
{
    if (!lo || !hi || lo==hi || n<1 || n>MAX) return 0;
    unsigned a=1,b=0;while (2*a<=n) { a*=2;++b; }
    mpq_t r,l,h,l2,h2,c;mpq_inits(r,l,h,l2,h2,c,NULL);
    mpq_set_ui(r,1,3);log_kernel(l2,h2,r);
    mpq_set_ui(r,n-a,n+a);mpq_canonicalize(r);log_kernel(l,h,r);
    mpq_set_ui(c,b,1);mpq_mul(l2,l2,c);mpq_mul(h2,h2,c);
    mpq_add(l,l,l2);mpq_add(h,h,h2);
    outward_grid(lo,l,0);outward_grid(hi,h,1);
    mpq_clears(r,l,h,l2,h2,c,NULL);return 1;
}

int weighted_remainder_rational_log_interval_q(mpq_t lo,mpq_t hi,const mpq_t x)
{
    if (!lo || !hi || lo==hi || !x || mpz_sgn(mpq_numref(x))<=0 || mpz_sgn(mpq_denref(x))<=0 ||
        mpz_sizeinbase(mpq_numref(x),2)>256 || mpz_sizeinbase(mpq_denref(x),2)>256) return 0;
    mpz_t g;mpz_init(g);mpz_gcd(g,mpq_numref(x),mpq_denref(x));
    int valid=mpz_cmp_ui(g,1)==0;mpz_clear(g);if (!valid) return 0;
    mpq_t u,r,l,h,l2,h2,c,one;mpq_inits(u,r,l,h,l2,h2,c,one,NULL);
    mpq_set(u,x);mpq_set_ui(one,1,1);int b=0;
    while (mpq_cmp_ui(u,2,1)>=0) { mpq_div_2exp(u,u,1);++b; }
    while (mpq_cmp_ui(u,1,1)<0) { mpq_mul_2exp(u,u,1);--b; }
    mpq_sub(r,u,one);mpq_add(c,u,one);mpq_div(r,r,c);log_kernel(l,h,r);
    mpq_set_ui(r,1,3);log_kernel(l2,h2,r);
    mpq_set_si(c,b,1);mpq_mul(l2,l2,c);mpq_mul(h2,h2,c);
    if (b<0) mpq_swap(l2,h2);
    mpq_add(l,l,l2);mpq_add(h,h,h2);
    outward_grid(lo,l,0);outward_grid(hi,h,1);
    mpq_clears(u,r,l,h,l2,h2,c,one,NULL);return 1;
}

void weighted_remainder_constants_init(WeightedRemainderConstants *s)
{
    s->cutoff=s->log_tail_binary_exponent=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}

void weighted_remainder_constants_clear(WeightedRemainderConstants *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}

int weighted_remainder_constants_compute(WeightedRemainderConstants *out,unsigned N)
{
    if (!out || N<1 || N>MAX) return 0;
    WeightedRemainderConstants s;weighted_remainder_constants_init(&s);s.cutoff=N;
    mpq_t midpoint,radius,c,t,h,ll,lh;mpq_inits(midpoint,radius,c,t,h,ll,lh,NULL);
    mpq_set_str(midpoint,"3141592653589793238465/1000000000000000000000",10);
    mpq_canonicalize(midpoint);
    mpq_set_str(radius,"1/200000000000000000000",10);mpq_canonicalize(radius);
    mpq_sub(s.pi_lower,midpoint,radius);mpq_add(s.pi_upper,midpoint,radius);
    mpq_mul(s.zeta_two_lower,s.pi_lower,s.pi_lower);
    mpq_mul(s.zeta_two_upper,s.pi_upper,s.pi_upper);
    mpq_mul(s.zeta_four_lower,s.zeta_two_lower,s.zeta_two_lower);
    mpq_mul(s.zeta_four_upper,s.zeta_two_upper,s.zeta_two_upper);
    mpq_set_ui(c,1,6);mpq_mul(s.zeta_two_lower,s.zeta_two_lower,c);mpq_mul(s.zeta_two_upper,s.zeta_two_upper,c);
    mpq_set_ui(c,1,90);mpq_mul(s.zeta_four_lower,s.zeta_four_lower,c);mpq_mul(s.zeta_four_upper,s.zeta_four_upper,c);
    weighted_remainder_zeta_three_interval_q(s.zeta_three_lower,s.zeta_three_upper,N);
    for (unsigned n=1;n<=N;++n) {
        weighted_remainder_log_interval_q(ll,lh,n);
        if (n==N) {
            mpq_set(s.gamma_harmonic_prefix,h);mpq_set(s.log_n_lower,ll);mpq_set(s.log_n_upper,lh);
        }
        mpq_set_ui(c,1,n*n);
        mpq_mul(t,ll,c);mpq_add(s.log_moment_prefix_lower,s.log_moment_prefix_lower,t);
        mpq_mul(t,lh,c);mpq_add(s.log_moment_prefix_upper,s.log_moment_prefix_upper,t);
        mpq_set_ui(c,1,n);mpq_add(h,h,c);
    }
    mpq_set_ui(c,1,2*N);
    mpq_sub(s.gamma_lower,s.gamma_harmonic_prefix,s.log_n_upper);mpq_add(s.gamma_lower,s.gamma_lower,c);
    mpq_sub(s.gamma_upper,s.gamma_harmonic_prefix,s.log_n_lower);mpq_add(s.gamma_upper,s.gamma_upper,c);
    mpq_set_ui(c,1,12*N*N);mpq_add(s.gamma_upper,s.gamma_upper,c);
    unsigned power=1,b=0;while (power<2*N) { power*=2;++b; }s.log_tail_binary_exponent=b;
    mpq_set_ui(s.log_moment_tail_upper,2*b+3,N);mpq_canonicalize(s.log_moment_tail_upper);
    mpq_set(s.log_moment_lower,s.log_moment_prefix_lower);
    mpq_add(s.log_moment_upper,s.log_moment_prefix_upper,s.log_moment_tail_upper);
    mpq_div(t,s.log_moment_lower,s.zeta_two_upper);mpq_add(s.kappa_lower,s.gamma_lower,t);
    mpq_div(t,s.log_moment_upper,s.zeta_two_lower);mpq_add(s.kappa_upper,s.gamma_upper,t);
    mpq_div(s.leading_lower,s.zeta_two_lower,s.zeta_three_upper);
    mpq_div(s.leading_upper,s.zeta_two_upper,s.zeta_three_lower);
    out->cutoff=s.cutoff;out->log_tail_binary_exponent=b;
#define COPY(f) mpq_set(out->f,s.f);
    FIELDS(COPY)
#undef COPY
    mpq_clears(midpoint,radius,c,t,h,ll,lh,NULL);weighted_remainder_constants_clear(&s);return 1;
}
