#include "weighted_remainder_harmonic_root.h"
#include "weighted_remainder_rect_internal.h"
#include "weighted_remainder_constants.h"
#include <stdlib.h>

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };
#define ROOT_FIELDS(X) X(harmonic_tail_upper) X(cubic_prefix_lower) X(cubic_prefix_upper) X(cubic_tail_upper) \
    X(cubic_lower) X(cubic_upper) X(sine_prefix_lower) X(sine_prefix_upper) X(sine_tail_upper) \
    X(sine_lower) X(sine_upper) X(zeta_lower) X(zeta_upper) X(angle_weight_lower) X(angle_weight_upper) \
    X(identity_lower) X(identity_upper)
#define ROOT_RECTS(X) X(phase) X(harmonic_prefix) X(harmonic)

static unsigned harmonic_tail(mpq_t out,unsigned N)
{
    unsigned b=0,power=1;while (power<2*N) { power*=2;++b; }
    mpq_set_ui(out,2*b+3,N);mpq_canonicalize(out);return b;
}

static int rational_input(const mpq_t x)
{
    if (!x || mpz_sgn(mpq_denref(x))<=0 || mpz_sizeinbase(mpq_numref(x),2)>63 ||
        mpz_sizeinbase(mpq_denref(x),2)>63) return 0;
    mpz_t g;mpz_init(g);mpz_gcd(g,mpq_numref(x),mpq_denref(x));
    int ok=mpz_cmp_ui(g,1)==0;mpz_clear(g);return ok;
}

void weighted_remainder_harmonic_polylog_init(WeightedRemainderHarmonicPolylog *s)
{
    s->cutoff=s->binary_exponent=0;mpq_inits(s->z_real,s->z_imag,s->tail_upper,NULL);
    weighted_remainder_complex_init(&s->prefix);weighted_remainder_complex_init(&s->value);
}
void weighted_remainder_harmonic_polylog_clear(WeightedRemainderHarmonicPolylog *s)
{
    mpq_clears(s->z_real,s->z_imag,s->tail_upper,NULL);
    weighted_remainder_complex_clear(&s->prefix);weighted_remainder_complex_clear(&s->value);
}
int weighted_remainder_harmonic_polylog_compute(WeightedRemainderHarmonicPolylog *out,
    const mpq_t re,const mpq_t im,unsigned N)
{
    if (!out || N<1 || N>MAX || !rational_input(re) || !rational_input(im)) return 0;
    mpq_t x,y,h,c;mpq_inits(x,y,h,c,NULL);mpq_mul(x,re,re);mpq_mul(y,im,im);mpq_add(x,x,y);
    if (mpq_cmp_ui(x,1,1)>0) { mpq_clears(x,y,h,c,NULL);return 0; }
    WeightedRemainderHarmonicPolylog s;weighted_remainder_harmonic_polylog_init(&s);
    s.cutoff=N;s.binary_exponent=harmonic_tail(s.tail_upper,N);mpq_set(s.z_real,re);mpq_set(s.z_imag,im);
    WeightedRemainderComplex z,p,t;
    weighted_remainder_complex_init(&z);weighted_remainder_complex_init(&p);weighted_remainder_complex_init(&t);
    mpq_set(z.real_lower,re);mpq_set(z.real_upper,re);mpq_set(z.imag_lower,im);mpq_set(z.imag_upper,im);
    mpq_set_ui(p.real_lower,1,1);mpq_set_ui(p.real_upper,1,1);
    for (unsigned n=1;n<=N;++n) {
        wr_rect_product(&p,&p,&z);mpq_set_ui(c,1,n*n);mpq_mul(c,c,h);
        wr_rect_scale(&t,&p,c,c);wr_rect_add(&s.prefix,&s.prefix,&t);
        mpq_set_ui(c,1,n);mpq_add(h,h,c);
    }
    if (!mpq_sgn(re) && !mpq_sgn(im)) mpq_set_ui(s.tail_upper,0,1);
    wr_rect_widen(&s.value,&s.prefix,s.tail_upper);
    out->cutoff=N;out->binary_exponent=s.binary_exponent;
    mpq_set(out->z_real,s.z_real);mpq_set(out->z_imag,s.z_imag);mpq_set(out->tail_upper,s.tail_upper);
    wr_rect_copy(&out->prefix,&s.prefix);wr_rect_copy(&out->value,&s.value);
    weighted_remainder_complex_clear(&z);weighted_remainder_complex_clear(&p);weighted_remainder_complex_clear(&t);
    weighted_remainder_harmonic_polylog_clear(&s);mpq_clears(x,y,h,c,NULL);return 1;
}

static WeightedRemainderComplex *phase_table(unsigned q)
{
    WeightedRemainderComplex *phases=calloc(q,sizeof(*phases));if (!phases) return NULL;
    for (unsigned a=0;a<q;++a) weighted_remainder_complex_init(&phases[a]);
    for (unsigned a=0;a<q;++a) if (!wr_rect_phase(&phases[a],q,a)) {
        for (unsigned b=0;b<q;++b) weighted_remainder_complex_clear(&phases[b]);
        free(phases);return NULL;
    }
    return phases;
}
static void phases_clear(WeightedRemainderComplex *phases,unsigned q)
{
    if (!phases) return;
    for (unsigned a=0;a<q;++a) weighted_remainder_complex_clear(&phases[a]);
    free(phases);
}

void weighted_remainder_harmonic_root_init(WeightedRemainderHarmonicRoot *s)
{
    s->denominator=s->numerator=s->cutoff=s->zeta_cutoff=s->binary_exponent=0;
#define INIT(f) mpq_init(s->f);
    ROOT_FIELDS(INIT)
#undef INIT
#define INIT(f) weighted_remainder_complex_init(&s->f);
    ROOT_RECTS(INIT)
#undef INIT
}
void weighted_remainder_harmonic_root_clear(WeightedRemainderHarmonicRoot *s)
{
#define CLEAR(f) mpq_clear(s->f);
    ROOT_FIELDS(CLEAR)
#undef CLEAR
#define CLEAR(f) weighted_remainder_complex_clear(&s->f);
    ROOT_RECTS(CLEAR)
#undef CLEAR
}
int weighted_remainder_harmonic_root_compute(WeightedRemainderHarmonicRoot *out,
    unsigned q,unsigned a,unsigned N,unsigned K)
{
    if (!out || q<1 || q>MAX || a>=q || N<1 || N>MAX || K<1 || K>MAX) return 0;
    WeightedRemainderComplex *phases=phase_table(q);if (!phases) return 0;
    WeightedRemainderHarmonicRoot s;weighted_remainder_harmonic_root_init(&s);
    s.denominator=q;s.numerator=a;s.cutoff=N;s.zeta_cutoff=K;
    s.binary_exponent=harmonic_tail(s.harmonic_tail_upper,N);wr_rect_copy(&s.phase,&phases[a]);
    WeightedRemainderComplex t;weighted_remainder_complex_init(&t);
    mpq_t h,c,l,u;mpq_inits(h,c,l,u,NULL);
    for (unsigned n=1;n<=N;++n) {
        const WeightedRemainderComplex *z=&phases[(a*n)%q];
        mpq_set_ui(c,1,n*n);mpq_mul(c,c,h);wr_rect_scale(&t,z,c,c);
        wr_rect_add(&s.harmonic_prefix,&s.harmonic_prefix,&t);
        mpq_set_ui(c,1,n*n*n);
        mpq_mul(l,z->real_lower,c);mpq_add(s.cubic_prefix_lower,s.cubic_prefix_lower,l);
        mpq_mul(u,z->real_upper,c);mpq_add(s.cubic_prefix_upper,s.cubic_prefix_upper,u);
        mpq_set_ui(c,1,n*n);
        mpq_mul(l,z->imag_lower,c);mpq_add(s.sine_prefix_lower,s.sine_prefix_lower,l);
        mpq_mul(u,z->imag_upper,c);mpq_add(s.sine_prefix_upper,s.sine_prefix_upper,u);
        mpq_set_ui(c,1,n);mpq_add(h,h,c);
    }
    mpq_set_ui(s.cubic_tail_upper,1,2*N*N);mpq_set_ui(s.sine_tail_upper,1,N);
    wr_rect_widen(&s.harmonic,&s.harmonic_prefix,s.harmonic_tail_upper);
    mpq_sub(s.cubic_lower,s.cubic_prefix_lower,s.cubic_tail_upper);
    mpq_add(s.cubic_upper,s.cubic_prefix_upper,s.cubic_tail_upper);
    mpq_sub(s.sine_lower,s.sine_prefix_lower,s.sine_tail_upper);
    mpq_add(s.sine_upper,s.sine_prefix_upper,s.sine_tail_upper);
    WeightedRemainderConstants constants;weighted_remainder_constants_init(&constants);
    int ok=weighted_remainder_constants_compute(&constants,1) &&
        weighted_remainder_zeta_three_interval_q(s.zeta_lower,s.zeta_upper,K);
    if (ok && a==0) {
        /* Actual endpoint identities: harmonic(1)=C3(0)=zeta(3), Cl2(0)=0. */
        if (mpq_cmp(s.harmonic.real_lower,s.zeta_lower)<0) mpq_set(s.harmonic.real_lower,s.zeta_lower);
        if (mpq_cmp(s.harmonic.real_upper,s.zeta_upper)>0) mpq_set(s.harmonic.real_upper,s.zeta_upper);
        mpq_set_ui(s.harmonic.imag_lower,0,1);mpq_set_ui(s.harmonic.imag_upper,0,1);
        mpq_set(s.cubic_lower,s.cubic_prefix_lower);
        if (mpq_cmp(s.cubic_lower,s.zeta_lower)<0) mpq_set(s.cubic_lower,s.zeta_lower);
        if (mpq_cmp(s.cubic_upper,s.zeta_upper)>0) mpq_set(s.cubic_upper,s.zeta_upper);
        mpq_set_ui(s.sine_lower,0,1);mpq_set_ui(s.sine_upper,0,1);
    }
    if (ok) {
        mpq_set_si(c,2*(long)a-(long)q,2*q);mpq_canonicalize(c);
        wr_product(s.angle_weight_lower,s.angle_weight_upper,constants.pi_lower,constants.pi_upper,c,c);
        wr_product(l,u,s.angle_weight_lower,s.angle_weight_upper,s.sine_lower,s.sine_upper);
        mpq_add(s.identity_lower,s.zeta_lower,s.cubic_lower);mpq_div_2exp(s.identity_lower,s.identity_lower,1);
        mpq_add(s.identity_upper,s.zeta_upper,s.cubic_upper);mpq_div_2exp(s.identity_upper,s.identity_upper,1);
        mpq_add(s.identity_lower,s.identity_lower,l);mpq_add(s.identity_upper,s.identity_upper,u);
        out->denominator=q;out->numerator=a;out->cutoff=N;out->zeta_cutoff=K;out->binary_exponent=s.binary_exponent;
#define COPY(f) mpq_set(out->f,s.f);
        ROOT_FIELDS(COPY)
#undef COPY
#define COPY(f) wr_rect_copy(&out->f,&s.f);
        ROOT_RECTS(COPY)
#undef COPY
    }
    weighted_remainder_constants_clear(&constants);weighted_remainder_complex_clear(&t);
    weighted_remainder_harmonic_root_clear(&s);mpq_clears(h,c,l,u,NULL);phases_clear(phases,q);return ok;
}

void weighted_remainder_harmonic_root_average_init(WeightedRemainderHarmonicRootAverage *s)
{
    s->modulus=s->cutoff=s->binary_exponent=0;weighted_remainder_complex_init(&s->root_average_prefix);
    mpq_inits(s->selected_prefix,s->tail_upper,s->lower,s->upper,NULL);
}
void weighted_remainder_harmonic_root_average_clear(WeightedRemainderHarmonicRootAverage *s)
{
    weighted_remainder_complex_clear(&s->root_average_prefix);
    mpq_clears(s->selected_prefix,s->tail_upper,s->lower,s->upper,NULL);
}
int weighted_remainder_harmonic_root_average_compute(WeightedRemainderHarmonicRootAverage *out,
    unsigned q,unsigned N)
{
    if (!out || q<1 || q>MAX || N<1 || N>MAX) return 0;
    WeightedRemainderComplex *phases=phase_table(q);if (!phases) return 0;
    WeightedRemainderHarmonicRootAverage s;weighted_remainder_harmonic_root_average_init(&s);
    s.modulus=q;s.cutoff=N;s.binary_exponent=harmonic_tail(s.tail_upper,N);
    mpq_t residue[MAX],h,c;mpq_inits(h,c,NULL);
    for (unsigned r=0;r<q;++r) mpq_init(residue[r]);
    for (unsigned n=1;n<=N;++n) {
        mpq_set_ui(c,1,n*n);mpq_mul(c,c,h);mpq_add(residue[n%q],residue[n%q],c);
        mpq_set_ui(c,1,n);mpq_add(h,h,c);
    }
    mpq_set(s.selected_prefix,residue[0]);
    WeightedRemainderComplex t;weighted_remainder_complex_init(&t);
    for (unsigned a=0;a<q;++a) for (unsigned r=0;r<q;++r) {
        if (!mpq_sgn(residue[r])) continue;
        wr_rect_scale(&t,&phases[(a*r)%q],residue[r],residue[r]);
        wr_rect_add(&s.root_average_prefix,&s.root_average_prefix,&t);
    }
    mpq_set_ui(c,1,q);wr_rect_scale(&s.root_average_prefix,&s.root_average_prefix,c,c);
    mpq_set(s.lower,s.selected_prefix);mpq_add(s.upper,s.selected_prefix,s.tail_upper);
    out->modulus=q;out->cutoff=N;out->binary_exponent=s.binary_exponent;
    wr_rect_copy(&out->root_average_prefix,&s.root_average_prefix);
    mpq_set(out->selected_prefix,s.selected_prefix);mpq_set(out->tail_upper,s.tail_upper);
    mpq_set(out->lower,s.lower);mpq_set(out->upper,s.upper);
    for (unsigned r=0;r<q;++r) mpq_clear(residue[r]);
    weighted_remainder_complex_clear(&t);weighted_remainder_harmonic_root_average_clear(&s);
    mpq_clears(h,c,NULL);phases_clear(phases,q);return 1;
}

int weighted_remainder_sine_transform_q(mpq_t lo,mpq_t hi,mpq_t rl,mpq_t ru,unsigned q,const mpz_t frequency)
{
    if (!lo || !hi || !rl || !ru || !frequency || q<1 || q>MAX) return 0;
    mpq_ptr out[]={lo,hi,rl,ru};
    for (unsigned i=0;i<4;++i) for (unsigned j=i+1;j<4;++j) if (out[i]==out[j]) return 0;
    unsigned r=(unsigned)mpz_fdiv_ui(frequency,q);
    if (!r) { for (unsigned i=0;i<4;++i) mpq_set_ui(out[i],0,1);return 1; }
    WeightedRemainderComplex *phases=phase_table(q);if (!phases) return 0;
    mpq_t l,u,c,x,y;mpq_inits(l,u,c,x,y,NULL);
    for (unsigned a=1;a<q;++a) {
        mpq_set_si(c,2*(long)a-(long)q,2*q);mpq_canonicalize(c);
        wr_product(x,y,phases[(a*r)%q].imag_lower,phases[(a*r)%q].imag_upper,c,c);
        mpq_add(l,l,x);mpq_add(u,u,y);
    }
    WeightedRemainderTrig trig;weighted_remainder_trig_init(&trig);
    int ok=weighted_remainder_trig_compute(&trig,q,frequency);
    if (ok) {
        mpq_set(lo,l);mpq_set(hi,u);mpq_neg(rl,trig.cot_upper);mpq_neg(ru,trig.cot_lower);
        mpq_div_2exp(rl,rl,1);mpq_div_2exp(ru,ru,1);
    }
    weighted_remainder_trig_clear(&trig);mpq_clears(l,u,c,x,y,NULL);phases_clear(phases,q);return ok;
}
