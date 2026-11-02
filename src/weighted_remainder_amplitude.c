#include "weighted_remainder_amplitude.h"
#include <stdio.h>
#include <string.h>

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };

#define FIELDS(X) X(delta) X(jordan_three) X(zeta_lower) X(zeta_upper) X(zeta_tail) \
    X(retained_amplitude) X(amplitude_lower) X(amplitude_upper) X(conductor_upper) \
    X(seed_prefix) X(seed_budget_lower) X(seed_lower) X(seed_upper) X(seed_tail_upper) \
    X(refinement_numerator_lower) X(refinement_numerator_upper) X(refinement_lower) X(refinement_upper) \
    X(jordan_sum_lower) X(jordan_sum_upper) X(jordan_rhs_lower) X(jordan_rhs_upper) \
    X(mobius_prefix_lower) X(mobius_prefix_upper) X(mobius_tail_upper) \
    X(mobius_lower) X(mobius_upper) X(prime_lower) X(prime_upper) \
    X(period_tail_bound) X(period_tail_upper)

static unsigned gcd(unsigned a,unsigned b)
{
    while (b) { unsigned r=a%b;a=b;b=r; }
    return a;
}

static int moebius(unsigned n)
{
    if (!n) return 0;
    int sign=1;
    for (unsigned p=2;p*p<=n;++p) if (n%p==0) {
        n/=p;sign=-sign;if (n%p==0) return 0;
    }
    return n>1 ? -sign : sign;
}

static int is_prime(unsigned n)
{
    if (n<2) return 0;
    for (unsigned d=2;d*d<=n;++d) if (n%d==0) return 0;
    return 1;
}

static unsigned jordan_three(unsigned q)
{
    unsigned j=q*q*q,n=q;
    for (unsigned p=2;p<=n;++p) if (n%p==0) {
        unsigned cube=p*p*p;j=(j/cube)*(cube-1);
        do n/=p;while (n%p==0);
    }
    return j;
}

int weighted_remainder_amplitude_factors_q(mpq_t delta,mpq_t jordan,unsigned q)
{
    if (!delta || !jordan || delta==jordan || q<1 || q>MAX) return 0;
    unsigned j=jordan_three(q);
    mpq_set_ui(delta,j,q*q*q);mpq_canonicalize(delta);mpq_set_ui(jordan,j,1);
    return 1;
}

int weighted_remainder_zeta_three_interval_q(mpq_t lo,mpq_t hi,unsigned N)
{
    if (!lo || !hi || lo==hi || N<1 || N>MAX) return 0;
    mpq_t l,u,t;mpq_inits(l,u,t,NULL);
    for (unsigned n=1;n<=N;++n) { mpq_set_ui(t,1,n*n*n);mpq_add(l,l,t); }
    mpq_set_ui(t,1,2*N*N);mpq_add(u,l,t);mpq_set(lo,l);mpq_set(hi,u);
    mpq_clears(l,u,t,NULL);return 1;
}

int weighted_remainder_harmonic_seed_prefix_q(mpq_t out,unsigned q,unsigned M)
{
    if (!out || q<1 || q>MAX || M>MAX) return 0;
    mpq_t sum,h,t;mpq_inits(sum,h,t,NULL);
    for (unsigned n=1;n<=M;++n) {
        if (n%q==0) { mpq_set_ui(t,1,n*n);mpq_mul(t,t,h);mpq_add(sum,sum,t); }
        mpq_set_ui(t,1,n);mpq_add(h,h,t);
    }
    mpq_set(out,sum);mpq_clears(sum,h,t,NULL);return 1;
}

void weighted_remainder_amplitude_init(WeightedRemainderAmplitude *s)
{
    s->conductor=s->period_cutoff=s->zeta_cutoff=s->mobius_cutoff=0;
    s->binary_exponent=s->prime=s->period_binary_exponent=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}

void weighted_remainder_amplitude_clear(WeightedRemainderAmplitude *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}

static void copy(WeightedRemainderAmplitude *out,const WeightedRemainderAmplitude *s)
{
    out->conductor=s->conductor;out->period_cutoff=s->period_cutoff;
    out->zeta_cutoff=s->zeta_cutoff;out->mobius_cutoff=s->mobius_cutoff;
    out->binary_exponent=s->binary_exponent;out->prime=s->prime;
    out->period_binary_exponent=s->period_binary_exponent;
#define COPY(f) mpq_set(out->f,s->f);
    FIELDS(COPY)
#undef COPY
}

static unsigned conductor_bound(mpq_t out,unsigned q)
{
    if (q==1) { mpq_set_ui(out,1,1);return 0; }
    unsigned b=0,power=1;
    while (power<2*q) { ++b;power*=2; }
    mpq_set_ui(out,4*(b+1),q*q);mpq_canonicalize(out);return b;
}

static void add_scaled_interval(mpq_t lo,mpq_t hi,const mpq_t coefficient,
                                 const mpq_t l,const mpq_t h)
{
    mpq_t a,b;mpq_inits(a,b,NULL);
    mpq_mul(a,coefficient,l);mpq_mul(b,coefficient,h);
    if (mpq_cmp(a,b)>0) mpq_swap(a,b);
    mpq_add(lo,lo,a);mpq_add(hi,hi,b);mpq_clears(a,b,NULL);
}

/* Positive denominator interval, with a numerator of either sign. All
 * four corners are computed before either output is changed. */
static void divide_interval(mpq_t lo,mpq_t hi,const mpq_t nl,const mpq_t nh,
                              const mpq_t dl,const mpq_t dh)
{
    mpq_t l,h,t;mpq_inits(l,h,t,NULL);mpq_div(l,nl,dh);mpq_set(h,l);
    mpq_srcptr n[2]={nl,nh},d[2]={dl,dh};
    for (unsigned i=0;i<2;++i) for (unsigned j=0;j<2;++j) {
        mpq_div(t,n[i],d[j]);if (mpq_cmp(t,l)<0) mpq_set(l,t);
        if (mpq_cmp(t,h)>0) mpq_set(h,t);
    }
    mpq_set(lo,l);mpq_set(hi,h);mpq_clears(l,h,t,NULL);
}

int weighted_remainder_amplitude_refinement_compute(WeightedRemainderAmplitude *out,
    unsigned q,unsigned M,unsigned N,unsigned D)
{
    if (!out || q<1 || q>MAX || M<2 || M>MAX || N<1 || N>MAX || D<1 || D>MAX) return 0;
    WeightedRemainderAmplitude s;weighted_remainder_amplitude_init(&s);
    s.conductor=q;s.period_cutoff=M;s.zeta_cutoff=N;s.mobius_cutoff=D;s.prime=is_prime(q);
    mpq_t w[MAX+1],al[MAX+1],ah[MAX+1],fl[MAX+1],fh[MAX+1];
    for (unsigned k=0;k<=MAX;++k) { mpq_init(w[k]);mpq_init(al[k]);mpq_init(ah[k]);mpq_init(fl[k]);mpq_init(fh[k]); }
    mpq_t mass,tail,coefficient,t,u,dl,dh,bl,bh;
    mpq_inits(mass,tail,coefficient,t,u,dl,dh,bl,bh,NULL);
    weighted_remainder_amplitude_factors_q(s.delta,s.jordan_three,q);
    weighted_remainder_zeta_three_interval_q(s.zeta_lower,s.zeta_upper,N);
    mpq_sub(s.zeta_tail,s.zeta_upper,s.zeta_lower);
    s.period_binary_exponent=conductor_bound(t,M);
    mpq_set_ui(s.period_tail_bound,2*s.period_binary_exponent+3,q*M);
    mpq_canonicalize(s.period_tail_bound);
    for (unsigned k=2;k<=M;++k) { weighted_remainder_weight_q(w[k],k);mpq_add(mass,mass,w[k]); }
    mpq_set_ui(tail,1,1);mpq_sub(tail,tail,mass);
    /* Every later seed argument divides q, including q/gcd(q,d). */
    for (unsigned d=1;d<=q;++d) if (q%d==0) {
        if (d==1) { mpq_set_ui(al[d],1,1);mpq_set_ui(ah[d],1,1); }
        else {
            for (unsigned k=d;k<=M;k+=d) mpq_add(al[d],al[d],w[k]);
            mpq_add(ah[d],al[d],tail);
            mpq_set_ui(t,2*s.period_binary_exponent+3,d*M);mpq_canonicalize(t);
            mpq_add(t,t,al[d]);
            if (mpq_cmp(t,ah[d])<0) mpq_set(ah[d],t);
            conductor_bound(t,d);
            if (mpq_cmp(t,ah[d])<0) mpq_set(ah[d],t);
        }
    }
    if (q==1) mpq_set(s.retained_amplitude,mass);
    else mpq_set(s.retained_amplitude,al[q]);
    mpq_set(s.amplitude_lower,al[q]);mpq_set(s.amplitude_upper,ah[q]);
    mpq_sub(s.period_tail_upper,ah[q],s.retained_amplitude);
    s.binary_exponent=conductor_bound(s.conductor_upper,q);
    for (unsigned d=1;d<=q;++d) if (q%d==0) {
        mpq_set_ui(bl,0,1);mpq_set_ui(bh,0,1);
        for (unsigned e=1;e<=d;++e) if (d%e==0) {
            mpq_set_ui(coefficient,jordan_three(e),1);
            add_scaled_interval(bl,bh,coefficient,al[e],ah[e]);
        }
        mpq_set_ui(coefficient,1,d*d*d);
        mpq_mul(fl[d],bl,s.zeta_lower);mpq_mul(fl[d],fl[d],coefficient);
        mpq_mul(fh[d],bh,s.zeta_upper);mpq_mul(fh[d],fh[d],coefficient);
        weighted_remainder_harmonic_seed_prefix_q(t,d,M);
        if (d==q) {
            mpq_set(s.jordan_sum_lower,bl);mpq_set(s.jordan_sum_upper,bh);
            mpq_set(s.seed_prefix,t);mpq_set(s.seed_budget_lower,fl[d]);
        }
        if (mpq_cmp(t,fl[d])>0) mpq_set(fl[d],t);
    }
    mpq_set(s.seed_lower,fl[q]);mpq_set(s.seed_upper,fh[q]);
    mpq_sub(s.seed_tail_upper,fh[q],s.seed_prefix);
    for (unsigned d=1;d<=q;++d) if (q%d==0) {
        mpq_set_si(coefficient,moebius(d),d*d*d);mpq_canonicalize(coefficient);
        add_scaled_interval(s.refinement_numerator_lower,s.refinement_numerator_upper,
                              coefficient,fl[q/d],fh[q/d]);
    }
    mpq_mul(dl,s.zeta_lower,s.delta);mpq_mul(dh,s.zeta_upper,s.delta);
    divide_interval(s.refinement_lower,s.refinement_upper,s.refinement_numerator_lower,
                      s.refinement_numerator_upper,dl,dh);
    mpq_set_ui(coefficient,q*q*q,1);mpq_mul(t,fl[q],coefficient);mpq_mul(u,fh[q],coefficient);
    divide_interval(s.jordan_rhs_lower,s.jordan_rhs_upper,t,u,s.zeta_lower,s.zeta_upper);
    for (unsigned d=1;d<=D;++d) {
        unsigned r=q/gcd(q,d);mpq_set_si(coefficient,moebius(d),d*d*d);mpq_canonicalize(coefficient);
        add_scaled_interval(s.mobius_prefix_lower,s.mobius_prefix_upper,coefficient,fl[r],fh[r]);
    }
    mpq_set_ui(coefficient,1,2*D*D);mpq_mul(s.mobius_tail_upper,s.zeta_upper,coefficient);
    mpq_sub(s.mobius_lower,s.mobius_prefix_lower,s.mobius_tail_upper);
    mpq_add(s.mobius_upper,s.mobius_prefix_upper,s.mobius_tail_upper);
    if (s.prime) {
        /* Literal prime formula retains the lower-conductor seed F(1). */
        mpq_set(bl,fl[q]);mpq_set(bh,fh[q]);mpq_set_si(coefficient,-1,q*q*q);
        add_scaled_interval(bl,bh,coefficient,fl[1],fh[1]);
        divide_interval(s.prime_lower,s.prime_upper,bl,bh,dl,dh);
    }
    copy(out,&s);
    for (unsigned k=0;k<=MAX;++k) { mpq_clear(w[k]);mpq_clear(al[k]);mpq_clear(ah[k]);mpq_clear(fl[k]);mpq_clear(fh[k]); }
    mpq_clears(mass,tail,coefficient,t,u,dl,dh,bl,bh,NULL);weighted_remainder_amplitude_clear(&s);return 1;
}

static int parse_bounded(const char *p,unsigned lower,unsigned *out)
{
    if (!p || !*p) return 0;
    unsigned n=0;
    for (;*p;++p) { if (*p<'0' || *p>'9') return 0;n=10*n+(unsigned)(*p-'0');if (n>MAX) return 0; }
    if (n<lower) return 0;
    *out=n;return 1;
}

int weighted_remainder_amplitude_command(int argc,char **argv)
{
    unsigned q,M,N,D;
    if (argc!=7 || strcmp(argv[2],"amplitude-refinement") || !parse_bounded(argv[3],1,&q) ||
        !parse_bounded(argv[4],2,&M) || !parse_bounded(argv[5],1,&N) || !parse_bounded(argv[6],1,&D)) goto bad;
    WeightedRemainderAmplitude s;weighted_remainder_amplitude_init(&s);
    int ok=weighted_remainder_amplitude_refinement_compute(&s,q,M,N,D);
    if (ok) {
        printf("Full collision amplitude and harmonic seed\nconductor=%u\nperiod_cutoff=%u\nzeta_cutoff=%u\nmobius_cutoff=%u\nbinary_exponent=%u\nprime=%u\n",q,M,N,D,s.binary_exponent,s.prime);
        printf("period_binary_exponent=%u\n",s.period_binary_exponent);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s.f);
        FIELDS(PRINT)
#undef PRINT
        puts("Exact rational intervals enclose full values; retained mass and seed prefixes are separate finite sums.");
    }
    weighted_remainder_amplitude_clear(&s);if (ok) return 0;
bad:
    fputs("amplitude-refinement requires conductor 1..240, period cutoff 2..240, zeta cutoff 1..240 and Mobius cutoff 1..240.\n",stderr);
    return 1;
}
