#include "weighted_remainder_fourier.h"
#include "weighted_remainder_weights.h"
#include <stdio.h>
#include <string.h>

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };

#define TRIG_FIELDS(X) X(sin_lower) X(sin_upper) X(cos_lower) X(cos_upper) \
    X(cot_lower) X(cot_upper) X(csc_squared_lower) X(csc_squared_upper)
#define FOURIER_FIELDS(X) X(amplitude_lower) X(amplitude_upper) X(g_lower) X(g_upper) \
    X(y_real_lower) X(y_real_upper) X(y_imag_lower) X(y_imag_upper) \
    X(g_mass_lower) X(g_mass_upper) X(y_mass_lower) X(y_mass_upper)

static unsigned gcd(unsigned a,unsigned b)
{
    while (b) { unsigned r=a%b;a=b;b=r; }
    return a;
}

static int canonical(const mpq_t x)
{
    if (mpz_sgn(mpq_denref(x))<=0) return 0;
    mpz_t g;mpz_init(g);mpz_gcd(g,mpq_numref(x),mpq_denref(x));
    int ok=mpz_cmp_ui(g,1)==0;mpz_clear(g);return ok;
}

static int residue(unsigned *a,unsigned q,const mpz_t frequency,int primitive)
{
    if (q<2 || q>MAX) return 0;
    *a=(unsigned)mpz_fdiv_ui(frequency,q);
    return *a!=0 && (!primitive || gcd(*a,q)==1);
}

void weighted_remainder_trig_init(WeightedRemainderTrig *s)
{
    s->conductor=s->residue=0;
#define INIT(f) mpq_init(s->f);
    TRIG_FIELDS(INIT)
#undef INIT
}

void weighted_remainder_trig_clear(WeightedRemainderTrig *s)
{
#define CLEAR(f) mpq_clear(s->f);
    TRIG_FIELDS(CLEAR)
#undef CLEAR
}

static void trig_copy(WeightedRemainderTrig *out,const WeightedRemainderTrig *s)
{
    out->conductor=s->conductor;out->residue=s->residue;
#define COPY(f) mpq_set(out->f,s->f);
    TRIG_FIELDS(COPY)
#undef COPY
}

/* Input may alias either component: both new parts are ready before writes. */
static void complex_square(mpq_t re,mpq_t im)
{
    mpq_t r,i,t;mpq_inits(r,i,t,NULL);
    mpq_mul(r,re,re);mpq_mul(t,im,im);mpq_sub(r,r,t);
    mpq_mul(i,re,im);mpq_mul_2exp(i,i,1);
    mpq_set(re,r);mpq_set(im,i);mpq_clears(r,i,t,NULL);
}

static void outward(mpq_t out,const mpq_t x,const mpz_t grid,int upper)
{
    mpz_t n;mpz_init(n);mpz_mul(n,mpq_numref(x),grid);
    if (upper) mpz_cdiv_q(n,n,mpq_denref(x));
    else mpz_fdiv_q(n,n,mpq_denref(x));
    mpz_set(mpq_numref(out),n);mpz_set(mpq_denref(out),grid);
    mpq_canonicalize(out);mpz_clear(n);
}

/* Four corners are needed because the numerator can have either sign. */
static void interval_product(mpq_t lo,mpq_t hi,const mpq_t al,const mpq_t ah,
                             const mpq_t bl,const mpq_t bh)
{
    mpq_t l,h,t;mpq_inits(l,h,t,NULL);
    mpq_mul(l,al,bl);mpq_set(h,l);
    mpq_srcptr a[2]={al,ah},b[2]={bl,bh};
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_mul(t,a[i],b[j]);
        if (mpq_cmp(t,l)<0) mpq_set(l,t);
        if (mpq_cmp(t,h)>0) mpq_set(h,t);
    }
    mpq_set(lo,l);mpq_set(hi,h);mpq_clears(l,h,t,NULL);
}

static void interval_square(mpq_t lo,mpq_t hi,const mpq_t al,const mpq_t ah)
{
    mpq_t l,h;mpq_inits(l,h,NULL);
    mpq_mul(l,al,al);mpq_mul(h,ah,ah);
    if (mpq_cmp(l,h)>0) mpq_swap(l,h);
    if (mpq_sgn(al)<=0 && mpq_sgn(ah)>=0) mpq_set_ui(l,0,1);
    mpq_set(lo,l);mpq_set(hi,h);mpq_clears(l,h,NULL);
}

int weighted_remainder_trig_compute(WeightedRemainderTrig *out,
                                     unsigned q,const mpz_t frequency)
{
    unsigned a;
    if (!out || !residue(&a,q,frequency,0)) return 0;
    WeightedRemainderTrig s;weighted_remainder_trig_init(&s);
    s.conductor=q;s.residue=a;
    mpq_t theta,r,i,tr,ti,nr,t,e,two,invlo,invhi;
    mpq_inits(theta,r,i,tr,ti,nr,t,e,two,invlo,invhi,NULL);
    mpz_t grid;mpz_init(grid);mpz_ui_pow_ui(grid,10,WEIGHTED_REMAINDER_FOURIER_DECIMALS);
    if (2*a==q) {
        mpq_set_ui(s.sin_lower,1,1);mpq_set_ui(s.sin_upper,1,1);
        mpq_set_ui(s.csc_squared_lower,1,1);mpq_set_ui(s.csc_squared_upper,1,1);
    } else {
        /* theta = pi_midpoint*a/(4*q). The complex Taylor term is
         * multiplied by i*theta/n; degree 0 through 23, then fourth power. */
        mpq_set_str(theta,"3141592653589793238465/1000000000000000000000",10);
        mpq_canonicalize(theta);
        mpq_set_ui(t,a,4*q);mpq_canonicalize(t);mpq_mul(theta,theta,t);
        mpq_set_ui(r,1,1);mpq_set_ui(tr,1,1);
        for (unsigned n=1;n<24;++n) {
            mpq_set_ui(t,1,n);mpq_mul(t,t,theta);
            mpq_mul(nr,ti,t);mpq_neg(nr,nr);mpq_mul(ti,tr,t);mpq_set(tr,nr);
            mpq_add(r,r,tr);mpq_add(i,i,ti);
        }
        complex_square(r,i);complex_square(r,i);
        mpz_fac_ui(mpq_denref(e),24);mpz_mul_ui(mpq_denref(e),mpq_denref(e),24);
        mpz_set_ui(mpq_numref(e),25);mpq_canonicalize(e);mpq_set_ui(two,2,1);
        for (unsigned j=0;j<2;++j) { mpq_add(t,two,e);mpq_mul(e,e,t); }
        mpq_set_str(t,"1/200000000000000000000",10);mpq_add(e,e,t);
        mpq_sub(t,i,e);outward(s.sin_lower,t,grid,0);
        mpq_add(t,i,e);outward(s.sin_upper,t,grid,1);
        mpq_sub(t,r,e);outward(s.cos_lower,t,grid,0);
        mpq_add(t,r,e);outward(s.cos_upper,t,grid,1);
        /* Strictly positive on every admitted interior angle. This exact
         * check is required before interval division; a failure is atomic. */
        if (mpq_sgn(s.sin_lower)<=0) goto bad;
        mpq_inv(invlo,s.sin_upper);mpq_inv(invhi,s.sin_lower);
        interval_product(s.cot_lower,s.cot_upper,s.cos_lower,s.cos_upper,invlo,invhi);
        mpq_mul(s.csc_squared_lower,invlo,invlo);
        mpq_mul(s.csc_squared_upper,invhi,invhi);
    }
    trig_copy(out,&s);
    mpz_clear(grid);mpq_clears(theta,r,i,tr,ti,nr,t,e,two,invlo,invhi,NULL);
    weighted_remainder_trig_clear(&s);return 1;
bad:
    mpz_clear(grid);mpq_clears(theta,r,i,tr,ti,nr,t,e,two,invlo,invhi,NULL);
    weighted_remainder_trig_clear(&s);return 0;
}

void weighted_remainder_fourier_init(WeightedRemainderFourier *s)
{
    s->cutoff=s->mode=0;weighted_remainder_trig_init(&s->trig);
#define INIT(f) mpq_init(s->f);
    FOURIER_FIELDS(INIT)
#undef INIT
}

void weighted_remainder_fourier_clear(WeightedRemainderFourier *s)
{
    weighted_remainder_trig_clear(&s->trig);
#define CLEAR(f) mpq_clear(s->f);
    FOURIER_FIELDS(CLEAR)
#undef CLEAR
}

static void fourier_copy(WeightedRemainderFourier *out,const WeightedRemainderFourier *s)
{
    out->cutoff=s->cutoff;out->mode=s->mode;trig_copy(&out->trig,&s->trig);
#define COPY(f) mpq_set(out->f,s->f);
    FOURIER_FIELDS(COPY)
#undef COPY
}

int weighted_remainder_fourier_interval_compute(WeightedRemainderFourier *out,
    unsigned q,const mpz_t frequency,const mpq_t lo,const mpq_t hi)
{
    unsigned a;
    if (!out || !residue(&a,q,frequency,1) || !canonical(lo) ||
        !canonical(hi) || mpq_cmp(lo,hi)>0) return 0;
    WeightedRemainderFourier s;weighted_remainder_fourier_init(&s);
    mpq_t factor,sl,sh;mpq_inits(factor,sl,sh,NULL);
    int ok=weighted_remainder_trig_compute(&s.trig,q,frequency);
    if (ok) {
        mpq_set(s.amplitude_lower,lo);mpq_set(s.amplitude_upper,hi);
        mpq_set_si(factor,-1,3);
        mpq_mul(s.y_real_lower,hi,factor);mpq_mul(s.y_real_upper,lo,factor);
        mpq_mul_2exp(s.g_lower,s.y_real_lower,1);mpq_mul_2exp(s.g_upper,s.y_real_upper,1);
        interval_product(s.y_imag_lower,s.y_imag_upper,lo,hi,s.trig.cot_lower,s.trig.cot_upper);
        mpq_set_ui(factor,1,3);mpq_mul(s.y_imag_lower,s.y_imag_lower,factor);
        mpq_mul(s.y_imag_upper,s.y_imag_upper,factor);
        interval_square(sl,sh,lo,hi);mpq_set_ui(factor,4,9);
        mpq_mul(s.g_mass_lower,sl,factor);mpq_mul(s.g_mass_upper,sh,factor);
        mpq_set_ui(factor,1,9);mpq_mul(sl,sl,factor);mpq_mul(sh,sh,factor);
        mpq_mul(s.y_mass_lower,sl,s.trig.csc_squared_lower);
        mpq_mul(s.y_mass_upper,sh,s.trig.csc_squared_upper);
        fourier_copy(out,&s);
    }
    mpq_clears(factor,sl,sh,NULL);weighted_remainder_fourier_clear(&s);return ok;
}

int weighted_remainder_fourier_finite_compute(WeightedRemainderFourier *out,
    unsigned M,unsigned q,const mpz_t frequency,const mpq_t *weights)
{
    if (!out) return 0;
    mpq_t xi;mpq_init(xi);
    int ok=weighted_remainder_weights_amplitude_q(xi,weights,M,q);
    if (ok) ok=weighted_remainder_fourier_interval_compute(out,q,frequency,xi,xi);
    if (ok) { out->cutoff=M;out->mode=1; }
    mpq_clear(xi);return ok;
}

int weighted_remainder_fourier_collision_compute(WeightedRemainderFourier *out,
    unsigned M,unsigned q,const mpz_t frequency,int full)
{
    if (!out || (full!=0 && full!=1)) return 0;
    mpq_t lo,hi;mpq_inits(lo,hi,NULL);
    int ok=weighted_remainder_amplitude_interval_q(lo,hi,q,M);
    if (ok && !full) mpq_set(hi,lo);
    if (ok) ok=weighted_remainder_fourier_interval_compute(out,q,frequency,lo,hi);
    if (ok) { out->cutoff=M;out->mode=full ? 2 : 1; }
    mpq_clears(lo,hi,NULL);return ok;
}

int weighted_remainder_row_fourier_q(mpq_t p_real,mpq_t imag_lower,
    mpq_t imag_upper,mpq_t c_real,unsigned p,unsigned q,const mpz_t frequency)
{
    mpq_ptr outputs[4]={p_real,imag_lower,imag_upper,c_real};
    unsigned a;
    if (p<2 || p>MAX || !residue(&a,q,frequency,1)) return 0;
    for (unsigned i=0;i<4;++i) for (unsigned j=0;j<i;++j)
        if (outputs[i]==outputs[j]) return 0;
    WeightedRemainderTrig t;weighted_remainder_trig_init(&t);
    int ok=p!=q || weighted_remainder_trig_compute(&t,q,frequency);
    if (ok) {
        mpq_set_si(p_real,p==q ? -1 : 0,p==q ? 2 : 1);
        mpq_div_2exp(imag_lower,t.cot_lower,1);mpq_div_2exp(imag_upper,t.cot_upper,1);
        mpq_set_ui(c_real,p==q ? 1 : 0,1);
    }
    weighted_remainder_trig_clear(&t);return ok;
}

static int parse_period(const char *p,unsigned *q)
{
    if (!p || !*p) return 0;
    unsigned n=0;
    for (;*p;++p) { if (*p<'0' || *p>'9') return 0;
        n=10*n+(unsigned)(*p-'0');if (n>MAX) return 0; }
    if (n<2) return 0;
    *q=n;return 1;
}

static int parse_frequency(mpz_t z,const char *p)
{
    if (!p || !*p) return 0;
    const char *digits=p;if (*digits=='-') ++digits;
    if (!*digits) return 0;
    for (const char *s=digits;*s;++s) if (*s<'0' || *s>'9') return 0;
    return mpz_set_str(z,p,10)==0;
}

int weighted_remainder_fourier_command(int argc,char **argv)
{
    unsigned q,M;
    if (argc!=7 || strcmp(argv[2],"fourier") || !parse_period(argv[3],&q) ||
        !parse_period(argv[5],&M) || (strcmp(argv[6],"finite") && strcmp(argv[6],"full"))) goto bad;
    mpz_t frequency;mpz_init(frequency);
    WeightedRemainderFourier s;weighted_remainder_fourier_init(&s);
    int full=!strcmp(argv[6],"full");
    int ok=parse_frequency(frequency,argv[4]) &&
        weighted_remainder_fourier_collision_compute(&s,M,q,frequency,full);
    if (ok) {
        printf("Primitive additive Fourier coefficients\nmode=%s\nconductor=%u\nresidue=%u\ncutoff=%u\n",
            full ? "full" : "finite",q,s.trig.residue,M);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s.f);
        FOURIER_FIELDS(PRINT)
#undef PRINT
#define PRINT(f) gmp_printf(#f "=%Qd\n",s.trig.f);
        TRIG_FIELDS(PRINT)
#undef PRINT
        mpq_t lo,hi;mpq_inits(lo,hi,NULL);
        mpq_div_2exp(lo,s.trig.cot_lower,1);mpq_div_2exp(hi,s.trig.cot_upper,1);
        gmp_printf("p_real=-1/2\np_imag_lower=%Qd\np_imag_upper=%Qd\n"
            "r_real=0\nr_imag_lower=%Qd\nr_imag_upper=%Qd\nc_real=1\nc_imag=0\ng_imag=0\n",lo,hi,lo,hi);
        mpq_clears(lo,hi,NULL);
        puts("All interval endpoints are exact rationals. Spectral masses are squared moduli.");
    }
    weighted_remainder_fourier_clear(&s);mpz_clear(frequency);
    if (ok) return 0;
bad:
    fputs("fourier requires conductor 2..240, a signed integer primitive frequency, "
          "cutoff 2..240 and mode finite|full.\n",stderr);
    return 1;
}
