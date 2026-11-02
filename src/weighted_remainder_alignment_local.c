#include "weighted_remainder_alignment_local.h"
#define FIELDS(X) X(reset_factor) X(reset_numerator) X(reset_average) \
    X(alignment_factor) X(alignment_numerator) X(alignment_average) \
    X(alignment_tail) X(limiting_factor) X(limiting_average) \
    X(reset_factor_relative_loss) X(reset_average_loss) \
    X(alignment_factor_relative_loss) X(alignment_average_loss) \
    X(absent_factor) X(absent_average)
void weighted_remainder_alignment_local_init(WeightedRemainderAlignmentLocal *s)
{
    s->prime=s->valuation=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}
void weighted_remainder_alignment_local_clear(WeightedRemainderAlignmentLocal *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}
static int prime(unsigned p)
{
    if (p<2 || p>240) return 0;
    for (unsigned d=2;d<=p/d;++d) if (p%d==0) return 0;
    return 1;
}
int weighted_remainder_alignment_local_compute(WeightedRemainderAlignmentLocal *out,unsigned p,unsigned v)
{
    if (!out || !prime(p) || v>240) return 0;
    WeightedRemainderAlignmentLocal s;weighted_remainder_alignment_local_init(&s);
    s.prime=p;s.valuation=v;
    mpq_t r,rv,rv1,c,d,a,b,one,r2,den;
    mpq_inits(r,rv,rv1,c,d,a,b,one,r2,den,NULL);
    mpq_set_ui(one,1,1);mpq_set_ui(r,1,p);
    mpz_set_ui(mpq_numref(rv),1);mpz_ui_pow_ui(mpq_denref(rv),p,v);
    mpq_mul(rv1,rv,r);mpq_add(s.limiting_factor,one,r);
    mpq_set_ui(s.limiting_average,1,p-1);
    mpq_sub(s.reset_factor,s.limiting_factor,rv1);
    mpq_set_ui(c,v+1,1);mpq_mul(a,c,rv);
    mpq_sub(s.reset_numerator,s.limiting_factor,a);
    mpq_set_si(c,(long)v-1,1);mpq_mul(a,c,rv1);
    mpq_add(s.reset_numerator,s.reset_numerator,a);
    mpq_mul(s.reset_numerator,s.reset_numerator,s.limiting_average);
    mpq_div(s.reset_average,s.reset_numerator,s.reset_factor);
    mpq_set_ui(c,1,p+1);mpq_mul(a,c,rv);
    mpq_sub(s.alignment_factor,s.limiting_factor,a);
    /* Actual closed geometric tail after the reset prefix j=1..v. */
    mpq_mul(r2,r,r);mpq_sub(den,one,r2);
    mpq_set_ui(c,v+1,1);mpq_add(c,c,s.limiting_average);
    mpq_div(a,c,den);mpq_mul(d,den,den);mpq_div(b,r2,d);mpq_add(a,a,b);
    mpq_sub(c,one,r);mpq_mul(c,c,rv);mpq_mul(c,c,r2);
    mpq_mul(s.alignment_tail,c,a);
    mpq_add(s.alignment_numerator,s.reset_numerator,s.alignment_tail);
    mpq_div(s.alignment_average,s.alignment_numerator,s.alignment_factor);
    mpq_sub(a,s.limiting_factor,s.reset_factor);
    mpq_div(s.reset_factor_relative_loss,a,s.limiting_factor);
    mpq_sub(s.reset_average_loss,s.limiting_average,s.reset_average);
    mpq_sub(a,s.limiting_factor,s.alignment_factor);
    mpq_div(s.alignment_factor_relative_loss,a,s.limiting_factor);
    mpq_sub(s.alignment_average_loss,s.limiting_average,s.alignment_average);
    mpq_set_ui(c,1,p*(p+1));mpq_add(s.absent_factor,one,c);
    mpq_set_ui(s.absent_average,1,p*p-1);
    out->prime=p;out->valuation=v;
#define COPY(f) mpq_set(out->f,s.f);
    FIELDS(COPY)
#undef COPY
    mpq_clears(r,rv,rv1,c,d,a,b,one,r2,den,NULL);
    weighted_remainder_alignment_local_clear(&s);return 1;
}
