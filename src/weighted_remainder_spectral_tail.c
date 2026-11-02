#include "weighted_remainder_spectral.h"

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };
#define TAIL_FIELDS(X) X(product_lower) X(product_upper) X(amplitude_leading_lower) X(amplitude_leading_upper) \
    X(log_q_lower) X(log_q_upper) X(log_b_lower) X(log_b_upper) \
    X(weighted_band_lower) X(weighted_band_upper) X(weighted_remainder_upper) \
    X(weighted_tail_lower) X(weighted_tail_upper) \
    X(energy_band_lower) X(energy_band_upper) X(energy_remainder_upper) \
    X(projection_tail_lower) X(projection_tail_upper) \
    X(weighted_leading_lower) X(weighted_leading_upper) X(energy_leading_lower) X(energy_leading_upper)

static unsigned binary(unsigned n)
{
    unsigned b=0,p=1;while (p<2*n) { p*=2;++b; } return b;
}

static unsigned jordan_two(unsigned n)
{
    unsigned value=n*n,remaining=n;
    for (unsigned p=2;p<=remaining;++p) if (remaining%p==0) {
        value=value/(p*p)*(p*p-1);
        do remaining/=p;while (remaining%p==0);
    }
    return value;
}

static void weight_table(mpq_t *weights,mpq_t mass,unsigned M)
{
    for (unsigned k=0;k<=M;++k) mpq_init(weights[k]);
    mpq_set_ui(mass,0,1);
    for (unsigned k=2;k<=M;++k) {
        weighted_remainder_weight_q(weights[k],k);mpq_add(mass,mass,weights[k]);
    }
}

static void energy(mpq_t al,mpq_t au,mpq_t el,mpq_t eu,
                   const mpq_t *weights,const mpq_t mass,unsigned q,unsigned M)
{
    mpq_t t,c,ll,lu;mpq_inits(t,c,ll,lu,NULL);mpq_set_ui(al,0,1);
    for (unsigned k=q;k<=M;k+=q) mpq_add(al,al,weights[k]);
    mpq_set_ui(c,1,1);mpq_sub(au,c,mass);mpq_add(au,au,al);
    mpq_set_ui(t,2*binary(M)+3,q*M);mpq_canonicalize(t);mpq_add(t,t,al);
    if (mpq_cmp(t,au)<0) mpq_set(au,t);
    weighted_remainder_log_interval_q(ll,lu,q);
    mpq_add(t,lu,c);mpq_set_ui(c,4,q*q);mpq_canonicalize(c);mpq_mul(t,t,c);
    if (mpq_cmp(t,au)<0) mpq_set(au,t);
    mpq_set_ui(c,jordan_two(q),27);mpq_canonicalize(c);
    mpq_mul(el,al,al);mpq_mul(el,el,c);mpq_mul(eu,au,au);mpq_mul(eu,eu,c);
    mpq_clears(t,c,ll,lu,NULL);
}

int weighted_remainder_spectral_energy_q(mpq_t al,mpq_t au,mpq_t el,mpq_t eu,unsigned q,unsigned M)
{
    if (!al || !au || !el || !eu || q<2 || q>MAX || M<2 || M>MAX) return 0;
    mpq_ptr outputs[]={al,au,el,eu};
    for (unsigned i=0;i<4;++i) for (unsigned j=i+1;j<4;++j) if (outputs[i]==outputs[j]) return 0;
    mpq_t weights[MAX+1],mass;mpq_init(mass);weight_table(weights,mass,M);
    energy(al,au,el,eu,weights,mass,q,M);
    for (unsigned k=0;k<=M;++k) mpq_clear(weights[k]);
    mpq_clear(mass);return 1;
}

void weighted_remainder_spectral_tail_init(WeightedRemainderSpectralTail *s)
{
    s->cutoff=s->band_cutoff=s->period_cutoff=s->prime_cutoff=s->constant_cutoff=s->period_binary_exponent=0;
#define INIT(f) mpq_init(s->f);
    TAIL_FIELDS(INIT)
#undef INIT
}

void weighted_remainder_spectral_tail_clear(WeightedRemainderSpectralTail *s)
{
#define CLEAR(f) mpq_clear(s->f);
    TAIL_FIELDS(CLEAR)
#undef CLEAR
}

int weighted_remainder_spectral_tail_compute(WeightedRemainderSpectralTail *out,
    unsigned Q,unsigned B,unsigned M,unsigned P,unsigned N)
{
    if (!out || Q<1 || Q>B || B<4 || B>MAX || M<2 || M>MAX || P<1 || P>MAX || N<1 || N>MAX) return 0;
    WeightedRemainderSpectralTail s;weighted_remainder_spectral_tail_init(&s);
    s.cutoff=Q;s.band_cutoff=B;s.period_cutoff=M;s.prime_cutoff=P;s.constant_cutoff=N;
    s.period_binary_exponent=binary(M);
    weighted_remainder_spectral_product_q(s.product_lower,s.product_upper,P);
    WeightedRemainderConstants constants;weighted_remainder_constants_init(&constants);
    weighted_remainder_constants_compute(&constants,N);
    mpq_set(s.amplitude_leading_lower,constants.leading_lower);mpq_set(s.amplitude_leading_upper,constants.leading_upper);
    weighted_remainder_constants_clear(&constants);
    weighted_remainder_log_interval_q(s.log_q_lower,s.log_q_upper,Q);
    weighted_remainder_log_interval_q(s.log_b_lower,s.log_b_upper,B);
    mpq_t weights[MAX+1],mass,al,au,el,eu,ll,lu,h,c,t,d;
    mpq_inits(mass,al,au,el,eu,ll,lu,h,c,t,d,NULL);weight_table(weights,mass,M);
    for (unsigned q=Q+1;q<=B;++q) {
        energy(al,au,el,eu,weights,mass,q,M);
        mpq_add(s.energy_band_lower,s.energy_band_lower,el);mpq_add(s.energy_band_upper,s.energy_band_upper,eu);
        weighted_remainder_spectral_arithmetic_q(h,c,q);weighted_remainder_log_interval_q(ll,lu,q);
        mpq_set_ui(d,q*q,1);mpq_div(h,h,d);
        mpq_mul(t,ll,ll);mpq_mul(t,t,h);mpq_add(s.weighted_band_lower,s.weighted_band_lower,t);
        mpq_mul(t,lu,lu);mpq_mul(t,t,h);mpq_add(s.weighted_band_upper,s.weighted_band_upper,t);
    }
    mpq_mul(t,s.log_b_upper,s.log_b_upper);mpq_set_ui(c,2,1);
    mpq_mul(h,c,s.log_b_upper);mpq_add(t,t,h);mpq_add(t,t,c);
    mpq_set_ui(d,B,1);mpq_div(s.weighted_remainder_upper,t,d);
    mpq_set_ui(c,1,1);mpq_add(t,t,c);mpq_div(t,t,d);
    mpq_set_ui(c,32,27);mpq_mul(s.energy_remainder_upper,t,c);
    mpq_set(s.weighted_tail_lower,s.weighted_band_lower);
    mpq_add(s.weighted_tail_upper,s.weighted_band_upper,s.weighted_remainder_upper);
    mpq_set(s.projection_tail_lower,s.energy_band_lower);
    mpq_add(s.projection_tail_upper,s.energy_band_upper,s.energy_remainder_upper);
    mpq_set_ui(d,Q,1);mpq_mul(t,s.log_q_lower,s.log_q_lower);mpq_div(t,t,d);
    mpq_mul(s.weighted_leading_lower,t,s.product_lower);
    mpq_mul(t,s.log_q_upper,s.log_q_upper);mpq_div(t,t,d);mpq_mul(s.weighted_leading_upper,t,s.product_upper);
    mpq_mul(t,s.amplitude_leading_lower,s.amplitude_leading_lower);
    mpq_mul(t,t,s.weighted_leading_lower);mpq_set_ui(d,27,1);mpq_div(s.energy_leading_lower,t,d);
    mpq_mul(t,s.amplitude_leading_upper,s.amplitude_leading_upper);
    mpq_mul(t,t,s.weighted_leading_upper);mpq_div(s.energy_leading_upper,t,d);
    for (unsigned k=0;k<=M;++k) mpq_clear(weights[k]);
    mpq_clears(mass,al,au,el,eu,ll,lu,h,c,t,d,NULL);
    WeightedRemainderSpectralTail old=*out;*out=s;weighted_remainder_spectral_tail_clear(&old);return 1;
}
