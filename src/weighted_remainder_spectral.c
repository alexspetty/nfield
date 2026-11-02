#include "weighted_remainder_spectral.h"

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };

#define MEAN_FIELDS(X) X(x) X(h_sum) X(h_mean) X(correction_floor_sum) X(correction_floor_mean) \
    X(correction_series_prefix) X(product_lower) X(product_upper) \
    X(nu_sum_lower) X(nu_sum_upper) X(nu_square_sum_lower) X(nu_square_sum_upper) \
    X(nu_mean_lower) X(nu_mean_upper) X(nu_square_mean_lower) X(nu_square_mean_upper) \
    X(first_prefix_lower) X(first_prefix_upper) X(first_tail_upper) X(first_lower) X(first_upper) \
    X(second_prefix_lower) X(second_prefix_upper) X(second_tail_upper) X(second_lower) X(second_upper) \
    X(nu_first_mean_bound) X(nu_second_mean_bound)

static int prime(unsigned n)
{
    if (n<2) return 0;
    for (unsigned d=2;d*d<=n;++d) if (n%d==0) return 0;
    return 1;
}

static void factors(mpq_t local,mpq_t euler,unsigned p)
{
    mpq_t square,t,den,c;mpq_inits(square,t,den,c,NULL);
    mpq_set_ui(square,p*p,1);mpq_set_ui(c,1,1);
    mpq_sub(t,square,c);mpq_mul(local,square,t);
    mpq_set_ui(c,p+1,1);mpq_add(den,square,c);mpq_mul(den,den,den);mpq_div(local,local,den);
    mpq_set_ui(c,1,1);mpq_sub(euler,local,c);
    mpq_set_ui(t,1,p);mpq_mul(euler,euler,t);mpq_add(euler,euler,c);
    mpq_clears(square,t,den,c,NULL);
}

int weighted_remainder_spectral_factors_q(mpq_t local,mpq_t euler,unsigned p)
{
    if (!local || !euler || local==euler || p>MAX || !prime(p)) return 0;
    factors(local,euler,p);return 1;
}

int weighted_remainder_spectral_arithmetic_q(mpq_t h,mpq_t c,unsigned n)
{
    if (!h || !c || h==c || n>MAX) return 0;
    mpq_t hv,cv,local,euler,one;mpq_inits(hv,cv,local,euler,one,NULL);
    if (n) {
        mpq_set_ui(hv,1,1);mpq_set_ui(cv,1,1);mpq_set_ui(one,1,1);
        unsigned remaining=n;int squarefree=1;
        for (unsigned p=2;p<=remaining;++p) if (remaining%p==0) {
            factors(local,euler,p);mpq_mul(hv,hv,local);
            mpq_sub(local,local,one);mpq_mul(cv,cv,local);
            remaining/=p;if (remaining%p==0) squarefree=0;
            while (remaining%p==0) remaining/=p;
        }
        if (!squarefree) mpq_set_ui(cv,0,1);
    }
    mpq_set(h,hv);mpq_set(c,cv);mpq_clears(hv,cv,local,euler,one,NULL);return 1;
}

int weighted_remainder_spectral_product_q(mpq_t lo,mpq_t hi,unsigned P)
{
    if (!lo || !hi || lo==hi || P<1 || P>MAX) return 0;
    mpq_t product,local,euler,l;mpq_inits(product,local,euler,l,NULL);mpq_set_ui(product,1,1);
    for (unsigned p=2;p<=P;++p) if (prime(p)) {
        factors(local,euler,p);mpq_mul(product,product,euler);
    }
    mpq_set_ui(l,2,P);mpq_canonicalize(l);mpq_sub(l,product,l);if (mpq_sgn(l)<0) mpq_set_ui(l,0,1);
    mpq_set(lo,l);mpq_set(hi,product);mpq_clears(product,local,euler,l,NULL);return 1;
}

void weighted_remainder_spectral_mean_init(WeightedRemainderSpectralMean *s)
{
    s->floor_x=s->prime_cutoff=s->prime_tail_binary_exponent=0;
#define INIT(f) mpq_init(s->f);
    MEAN_FIELDS(INIT)
#undef INIT
}

void weighted_remainder_spectral_mean_clear(WeightedRemainderSpectralMean *s)
{
#define CLEAR(f) mpq_clear(s->f);
    MEAN_FIELDS(CLEAR)
#undef CLEAR
}

static int valid_x(const mpq_t x)
{
    if (!x || mpz_sgn(mpq_denref(x))<=0 || mpz_sgn(mpq_numref(x))<=0 ||
        mpz_sizeinbase(mpq_numref(x),2)>255 || mpz_sizeinbase(mpq_denref(x),2)>255) return 0;
    mpz_t g;mpz_init(g);mpz_gcd(g,mpq_numref(x),mpq_denref(x));
    int valid=mpz_cmp_ui(g,1)==0;mpz_clear(g);
    return valid && mpq_cmp_ui(x,1,1)>=0 && mpq_cmp_ui(x,MAX,1)<=0;
}

int weighted_remainder_spectral_mean_compute(WeightedRemainderSpectralMean *out,
                                              const mpq_t x,unsigned P)
{
    if (!out || P<1 || P>MAX || !valid_x(x)) return 0;
    WeightedRemainderSpectralMean s;weighted_remainder_spectral_mean_init(&s);
    mpq_set(s.x,x);s.prime_cutoff=P;
    mpz_t floor_value;mpz_init(floor_value);
    mpz_fdiv_q(floor_value,mpq_numref(s.x),mpq_denref(s.x));
    s.floor_x=(unsigned)mpz_get_ui(floor_value);
    unsigned power=1;while (power<2*P) { power*=2;++s.prime_tail_binary_exponent; }
    mpq_t log_lo[MAX+1],log_hi[MAX+1];
    unsigned end=s.floor_x>P?s.floor_x:P;
    for (unsigned n=0;n<=end;++n) { mpq_init(log_lo[n]);mpq_init(log_hi[n]); }
    for (unsigned p=2;p<=end;++p) if (prime(p)) weighted_remainder_log_interval_q(log_lo[p],log_hi[p],p);
    mpq_t h,c,t,d,l,u,nl,nu;mpq_inits(h,c,t,d,l,u,nl,nu,NULL);
    for (unsigned n=1;n<=s.floor_x;++n) {
        weighted_remainder_spectral_arithmetic_q(h,c,n);mpq_add(s.h_sum,s.h_sum,h);
        mpq_set_ui(d,n,1);mpq_div(t,s.x,d);
        mpz_fdiv_q(floor_value,mpq_numref(t),mpq_denref(t));mpq_set_z(t,floor_value);
        mpq_mul(t,c,t);mpq_add(s.correction_floor_sum,s.correction_floor_sum,t);
        mpq_div(t,c,d);mpq_add(s.correction_series_prefix,s.correction_series_prefix,t);
        mpq_set_ui(nl,0,1);mpq_set_ui(nu,0,1);
        unsigned remaining=n;
        for (unsigned p=2;p<=remaining;++p) if (remaining%p==0) {
            mpq_set_ui(d,p-1,1);mpq_div(l,log_lo[p],d);mpq_div(u,log_hi[p],d);
            mpq_add(nl,nl,l);mpq_add(nu,nu,u);
            do remaining/=p;while (remaining%p==0);
        }
        mpq_add(s.nu_sum_lower,s.nu_sum_lower,nl);mpq_add(s.nu_sum_upper,s.nu_sum_upper,nu);
        mpq_mul(t,nl,nl);mpq_add(s.nu_square_sum_lower,s.nu_square_sum_lower,t);
        mpq_mul(t,nu,nu);mpq_add(s.nu_square_sum_upper,s.nu_square_sum_upper,t);
    }
    mpq_div(s.h_mean,s.h_sum,s.x);mpq_div(s.correction_floor_mean,s.correction_floor_sum,s.x);
    mpq_div(s.nu_mean_lower,s.nu_sum_lower,s.x);mpq_div(s.nu_mean_upper,s.nu_sum_upper,s.x);
    mpq_div(s.nu_square_mean_lower,s.nu_square_sum_lower,s.x);
    mpq_div(s.nu_square_mean_upper,s.nu_square_sum_upper,s.x);
    weighted_remainder_spectral_product_q(s.product_lower,s.product_upper,P);
    for (unsigned p=2;p<=P;++p) if (prime(p)) {
        mpq_set_ui(d,p-1,1);mpq_div(l,log_lo[p],d);mpq_div(u,log_hi[p],d);mpq_set_ui(d,p,1);
        mpq_div(t,l,d);mpq_add(s.first_prefix_lower,s.first_prefix_lower,t);
        mpq_div(t,u,d);mpq_add(s.first_prefix_upper,s.first_prefix_upper,t);
        mpq_mul(t,l,l);mpq_div(t,t,d);mpq_add(s.second_prefix_lower,s.second_prefix_lower,t);
        mpq_mul(t,u,u);mpq_div(t,t,d);mpq_add(s.second_prefix_upper,s.second_prefix_upper,t);
    }
    mpq_set_ui(s.first_tail_upper,2*(2*s.prime_tail_binary_exponent+3),P);mpq_canonicalize(s.first_tail_upper);
    mpq_set_ui(s.second_tail_upper,16,P);mpq_canonicalize(s.second_tail_upper);
    mpq_set(s.first_lower,s.first_prefix_lower);mpq_add(s.first_upper,s.first_prefix_upper,s.first_tail_upper);
    mpq_set(s.second_lower,s.second_prefix_lower);mpq_add(s.second_upper,s.second_prefix_upper,s.second_tail_upper);
    mpq_set(s.nu_first_mean_bound,s.first_upper);
    mpq_mul(s.nu_second_mean_bound,s.first_upper,s.first_upper);
    mpq_add(s.nu_second_mean_bound,s.nu_second_mean_bound,s.second_upper);
    for (unsigned n=0;n<=end;++n) { mpq_clear(log_lo[n]);mpq_clear(log_hi[n]); }
    mpq_clears(h,c,t,d,l,u,nl,nu,NULL);mpz_clear(floor_value);
    WeightedRemainderSpectralMean old=*out;*out=s;weighted_remainder_spectral_mean_clear(&old);return 1;
}
