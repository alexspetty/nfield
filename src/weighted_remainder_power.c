#include "weighted_remainder_power.h"

enum { EXP_TERMS=24, EXP_SQUARES=7, EXPONENT_BITS=256 };

static int valid_exponent(const mpq_t s)
{
    if (!s || mpz_sgn(mpq_denref(s))<=0 || mpz_sgn(mpq_numref(s))<0 ||
        mpz_sizeinbase(mpq_numref(s),2)>EXPONENT_BITS ||
        mpz_sizeinbase(mpq_denref(s),2)>EXPONENT_BITS) return 0;
    mpz_t g;mpz_init(g);mpz_gcd(g,mpq_numref(s),mpq_denref(s));
    int ok=mpz_cmp_ui(g,1)==0;mpz_clear(g);
    return ok && mpq_cmp_ui(s,12,1)<=0;
}

static void outward_grid(mpq_t out,const mpq_t x,int upward,unsigned digits)
{
    mpz_t grid,z,k;mpz_inits(grid,z,k,NULL);mpz_ui_pow_ui(grid,10,digits);
    mpz_mul(z,mpq_numref(x),grid);
    if (upward) mpz_cdiv_q(k,z,mpq_denref(x));
    else mpz_fdiv_q(k,z,mpq_denref(x));
    mpq_set_num(out,k);mpq_set_den(out,grid);mpq_canonicalize(out);
    mpz_clears(grid,z,k,NULL);
}

static void exp_polynomial(mpq_t out,const mpq_t x)
{
    mpq_t term,c;mpq_inits(term,c,NULL);mpq_set_ui(term,1,1);mpq_set(out,term);
    for (unsigned k=1;k<EXP_TERMS;++k) {
        mpq_mul(term,term,x);mpq_set_ui(c,1,k);mpq_mul(term,term,c);
        mpq_add(out,out,term);
    }
    mpq_clears(term,c,NULL);
}

int weighted_remainder_small_exp_interval_q(mpq_t lo,mpq_t hi,const mpq_t a,const mpq_t b)
{
    if (!lo || !hi || lo==hi || !valid_exponent(a) || !valid_exponent(b) ||
        mpq_cmp(a,b)>0 || mpq_cmp_ui(b,1,1)>0) return 0;
    mpq_t l,h,c,error;mpq_inits(l,h,c,error,NULL);mpq_set(l,a);mpq_set(h,b);
    mpz_fac_ui(mpq_denref(error),24);mpz_mul_ui(mpq_denref(error),mpq_denref(error),24);
    mpz_set_ui(mpq_numref(error),25);mpq_canonicalize(error);
    exp_polynomial(c,l);mpq_sub(l,c,error);
    if (mpq_cmp_ui(l,1,1)<0) mpq_set_ui(l,1,1);
    outward_grid(l,l,0,24);
    if (mpq_cmp_ui(l,1,1)<0) mpq_set_ui(l,1,1);
    exp_polynomial(c,h);mpq_add(h,c,error);outward_grid(h,h,1,24);
    mpq_set(lo,l);mpq_set(hi,h);mpq_clears(l,h,c,error,NULL);return 1;
}

int weighted_remainder_power_interval_q(mpq_t lo,mpq_t hi,unsigned n,const mpq_t s)
{
    if (!lo || !hi || lo==hi || n<1 || n>WEIGHTED_REMAINDER_EXACT_MAX ||
        !valid_exponent(s)) return 0;
    mpq_t exponent,l,h,c,error;mpq_inits(exponent,l,h,c,error,NULL);
    mpq_set(exponent,s); /* Output/input aliases are admitted. */
    if (mpz_cmp_ui(mpq_denref(exponent),1)==0 || n==1) {
        unsigned long k=n==1 ? 0 : mpz_get_ui(mpq_numref(exponent));
        mpz_ui_pow_ui(mpq_denref(l),n,k);mpz_set_ui(mpq_numref(l),1);
        mpq_set(h,l);
    } else {
        weighted_remainder_log_interval_q(l,h,n);
        mpq_mul(l,l,exponent);mpq_mul(h,h,exponent);
        /* This exact guard is also the hypothesis of the range-reduction
         * theorem. It holds throughout the documented resource domain. */
        if (mpq_cmp_ui(h,128,1)>0) {
            mpq_clears(exponent,l,h,c,error,NULL);return 0;
        }
        mpq_set_ui(c,1,128);mpq_mul(l,l,c);mpq_mul(h,h,c);
        mpz_fac_ui(mpq_denref(error),24);
        mpz_mul_ui(mpq_denref(error),mpq_denref(error),24);
        mpz_set_ui(mpq_numref(error),25);mpq_canonicalize(error);
        exp_polynomial(c,l);mpq_sub(l,c,error);
        if (mpq_cmp_ui(l,1,1)<0) mpq_set_ui(l,1,1);
        outward_grid(l,l,0,24);
        if (mpq_cmp_ui(l,1,1)<0) mpq_set_ui(l,1,1);
        exp_polynomial(c,h);mpq_add(h,c,error);outward_grid(h,h,1,24);
        for (unsigned k=0;k<EXP_SQUARES;++k) {
            mpq_mul(l,l,l);outward_grid(l,l,0,24);
            if (mpq_cmp_ui(l,1,1)<0) mpq_set_ui(l,1,1);
            mpq_mul(h,h,h);outward_grid(h,h,1,24);
        }
        mpq_inv(c,h);mpq_inv(h,l);mpq_set(l,c);
        outward_grid(l,l,0,48);outward_grid(h,h,1,48);
    }
    mpq_set(lo,l);mpq_set(hi,h);
    mpq_clears(exponent,l,h,c,error,NULL);return 1;
}
