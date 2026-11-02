#ifndef NFIELD_WEIGHTED_REMAINDER_RECT_INTERNAL_H
#define NFIELD_WEIGHTED_REMAINDER_RECT_INTERNAL_H

#include "weighted_remainder_complex.h"

/* Private exact interval operations. Scalar outputs in product must be
 * distinct from one another and the inputs. Rectangle operations below
 * explicitly allow out to equal an input. All endpoints are canonical. */
static inline void wr_product(mpq_t lo,mpq_t hi,
    const mpq_t al,const mpq_t au,const mpq_t bl,const mpq_t bu)
{
    mpq_t t;mpq_init(t);mpq_srcptr xs[]={al,au},ys[]={bl,bu};
    mpq_mul(lo,al,bl);mpq_set(hi,lo);
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_mul(t,xs[i],ys[j]);
        if (mpq_cmp(t,lo)<0) mpq_set(lo,t);
        if (mpq_cmp(t,hi)>0) mpq_set(hi,t);
    }
    mpq_clear(t);
}

static inline void wr_rect_zero(WeightedRemainderComplex *s)
{
    mpq_set_ui(s->real_lower,0,1);mpq_set_ui(s->real_upper,0,1);
    mpq_set_ui(s->imag_lower,0,1);mpq_set_ui(s->imag_upper,0,1);
}

static inline void wr_rect_copy(WeightedRemainderComplex *s,const WeightedRemainderComplex *a)
{
    mpq_set(s->real_lower,a->real_lower);mpq_set(s->real_upper,a->real_upper);
    mpq_set(s->imag_lower,a->imag_lower);mpq_set(s->imag_upper,a->imag_upper);
}

static inline void wr_rect_add(WeightedRemainderComplex *s,
    const WeightedRemainderComplex *a,const WeightedRemainderComplex *b)
{
    mpq_add(s->real_lower,a->real_lower,b->real_lower);mpq_add(s->real_upper,a->real_upper,b->real_upper);
    mpq_add(s->imag_lower,a->imag_lower,b->imag_lower);mpq_add(s->imag_upper,a->imag_upper,b->imag_upper);
}

static inline void wr_rect_scale(WeightedRemainderComplex *s,
    const WeightedRemainderComplex *a,const mpq_t lo,const mpq_t hi)
{
    WeightedRemainderComplex t;weighted_remainder_complex_init(&t);
    wr_product(t.real_lower,t.real_upper,a->real_lower,a->real_upper,lo,hi);
    wr_product(t.imag_lower,t.imag_upper,a->imag_lower,a->imag_upper,lo,hi);
    wr_rect_copy(s,&t);weighted_remainder_complex_clear(&t);
}

static inline void wr_rect_conjugate(WeightedRemainderComplex *s,const WeightedRemainderComplex *a)
{
    mpq_t t;mpq_init(t);mpq_neg(t,a->imag_upper);
    mpq_neg(s->imag_upper,a->imag_lower);mpq_set(s->imag_lower,t);
    mpq_set(s->real_lower,a->real_lower);mpq_set(s->real_upper,a->real_upper);mpq_clear(t);
}

static inline void wr_rect_product(WeightedRemainderComplex *s,
    const WeightedRemainderComplex *a,const WeightedRemainderComplex *b)
{
    WeightedRemainderComplex t;weighted_remainder_complex_init(&t);
    mpq_t l,u;mpq_inits(l,u,NULL);
    wr_product(t.real_lower,t.real_upper,a->real_lower,a->real_upper,b->real_lower,b->real_upper);
    wr_product(l,u,a->imag_lower,a->imag_upper,b->imag_lower,b->imag_upper);
    mpq_sub(t.real_lower,t.real_lower,u);mpq_sub(t.real_upper,t.real_upper,l);
    wr_product(t.imag_lower,t.imag_upper,a->real_lower,a->real_upper,b->imag_lower,b->imag_upper);
    wr_product(l,u,a->imag_lower,a->imag_upper,b->real_lower,b->real_upper);
    mpq_add(t.imag_lower,t.imag_lower,l);mpq_add(t.imag_upper,t.imag_upper,u);
    wr_rect_copy(s,&t);mpq_clears(l,u,NULL);weighted_remainder_complex_clear(&t);
}

static inline void wr_rect_widen(WeightedRemainderComplex *s,
    const WeightedRemainderComplex *a,const mpq_t radius)
{
    mpq_sub(s->real_lower,a->real_lower,radius);mpq_add(s->real_upper,a->real_upper,radius);
    mpq_sub(s->imag_lower,a->imag_lower,radius);mpq_add(s->imag_upper,a->imag_upper,radius);
}

static inline int wr_rect_phase(WeightedRemainderComplex *s,unsigned q,unsigned a)
{
    return weighted_remainder_complex_phase_q(s->real_lower,s->real_upper,s->imag_lower,s->imag_upper,q,a);
}

#endif
