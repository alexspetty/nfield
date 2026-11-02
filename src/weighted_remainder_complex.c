#include "weighted_remainder_complex.h"

void weighted_remainder_complex_init(WeightedRemainderComplex *out)
{
    mpq_inits(out->real_lower,out->real_upper,out->imag_lower,out->imag_upper,NULL);
}

void weighted_remainder_complex_clear(WeightedRemainderComplex *out)
{
    mpq_clears(out->real_lower,out->real_upper,out->imag_lower,out->imag_upper,NULL);
}

static void square(mpq_t l,mpq_t u,const mpq_t a,const mpq_t b)
{
    mpq_mul(l,a,a);mpq_mul(u,b,b);if (mpq_cmp(l,u)>0) mpq_swap(l,u);
    if (mpq_sgn(a)<=0 && mpq_sgn(b)>=0) mpq_set_ui(l,0,1);
}

static void product(mpq_t l,mpq_t u,const mpq_t a,const mpq_t b,const mpq_t c,const mpq_t d)
{
    mpq_srcptr xs[]={a,b},ys[]={c,d};mpq_t t;mpq_init(t);
    mpq_mul(l,a,c);mpq_set(u,l);
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_mul(t,xs[i],ys[j]);if (mpq_cmp(t,l)<0) mpq_set(l,t);if (mpq_cmp(t,u)>0) mpq_set(u,t);
    }
    mpq_clear(t);
}

int weighted_remainder_complex_phase_q(mpq_t rl,mpq_t ru,mpq_t il,mpq_t iu,unsigned q,unsigned a)
{
    if (!rl || !ru || !il || !iu || q<1 || q>WEIGHTED_REMAINDER_EXACT_MAX || a>=q) return 0;
    mpq_ptr outs[]={rl,ru,il,iu};
    for (unsigned i=0;i<4;++i) for (unsigned j=i+1;j<4;++j) if (outs[i]==outs[j]) return 0;
    if (!a) { mpq_set_ui(rl,1,1);mpq_set_ui(ru,1,1);mpq_set_ui(il,0,1);mpq_set_ui(iu,0,1);return 1; }
    WeightedRemainderTrig t;weighted_remainder_trig_init(&t);mpz_t freq;mpz_init_set_ui(freq,a);
    int ok=weighted_remainder_trig_compute(&t,q,freq);mpz_clear(freq);
    if (!ok) { weighted_remainder_trig_clear(&t);return 0; }
    mpq_t cl,cu,sl,su;mpq_inits(cl,cu,sl,su,NULL);
    square(cl,cu,t.cos_lower,t.cos_upper);square(sl,su,t.sin_lower,t.sin_upper);
    mpq_sub(rl,cl,su);mpq_sub(ru,cu,sl);
    product(il,iu,t.sin_lower,t.sin_upper,t.cos_lower,t.cos_upper);
    mpq_mul_2exp(il,il,1);mpq_mul_2exp(iu,iu,1);
    mpq_clears(cl,cu,sl,su,NULL);weighted_remainder_trig_clear(&t);return 1;
}
