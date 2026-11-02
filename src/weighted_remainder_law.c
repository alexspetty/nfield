#include "weighted_remainder_law.h"
#include "weighted_remainder_weights.h"
#include "weighted_remainder_cylinder.h"
#include <mpfr.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FIELDS(X) X(finite) X(absolute) X(full_lower) X(full_upper) X(squared_l2_error) \
 X(probability_error) X(finite_expanded) X(real_lower) X(real_upper) X(rounding_width) X(characteristic_error_upper)
void weighted_remainder_law_init(WeightedRemainderLaw *s)
{
    s->cutoff=s->period=s->distinct=s->degree=s->binary_exponent=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}
void weighted_remainder_law_clear(WeightedRemainderLaw *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}
static int rational(const mpq_t q)
{
    if (!q || mpz_sgn(mpq_denref(q))<=0 || mpz_sizeinbase(mpq_numref(q),2)>256 ||
        mpz_sizeinbase(mpq_denref(q),2)>256) return 0;
    mpz_t g;mpz_init(g);mpz_gcd(g,mpq_numref(q),mpq_denref(q));
    int ok=mpz_cmp_ui(g,1)==0;mpz_clear(g);return ok;
}
typedef struct { mpq_t value; unsigned count; } LawAtom;
typedef struct { LawAtom *atoms; unsigned count; } LawData;
static int collect(const mpq_t value,unsigned multiplicity,void *context)
{
    LawData *d=context;
    if (d->count>=WEIGHTED_REMAINDER_CLOCK_LAW_MAX) return 0;
    LawAtom *p=&d->atoms[d->count++];mpq_init(p->value);mpq_set(p->value,value);p->count=multiplicity;
    return 1;
}
static void release(LawData *d)
{
    for (unsigned i=0;i<d->count;++i) mpq_clear(d->atoms[i].value);
    free(d->atoms);
}
static unsigned below(const LawData *d,const mpq_t x)
{
    unsigned n=0;
    for (unsigned i=0;i<d->count;++i) if (mpq_cmp(d->atoms[i].value,x)<=0) n+=d->atoms[i].count;
    return n;
}
static unsigned window(const LawData *d,const mpq_t lo,const mpq_t hi)
{
    unsigned n=0;
    for (unsigned i=0;i<d->count;++i)
        if (mpq_cmp(d->atoms[i].value,lo)>=0 && mpq_cmp(d->atoms[i].value,hi)<=0) n+=d->atoms[i].count;
    return n;
}
static unsigned concentration(const LawData *d,const mpq_t width)
{
    unsigned right=0,total=0,best=0;mpq_t end;mpq_init(end);
    for (unsigned left=0;left<d->count;++left) {
        mpq_add(end,d->atoms[left].value,width);
        while (right<d->count && mpq_cmp(d->atoms[right].value,end)<=0) total+=d->atoms[right++].count;
        if (total>best) best=total;
        total-=d->atoms[left].count;
    }
    mpq_clear(end);return best;
}
static void probability(mpq_t q,unsigned count,unsigned period)
{
    mpq_set_ui(q,count,period);mpq_canonicalize(q);
}
static void clamp_probability(mpq_t q)
{
    if (mpq_sgn(q)<0) mpq_set_ui(q,0,1);
    if (mpq_cmp_ui(q,1,1)>0) mpq_set_ui(q,1,1);
}
/* Exact upward square root on a 10^-24 grid. */
static void sqrt_upper(mpq_t out,const mpq_t x)
{
    mpz_t grid,n,k;mpz_inits(grid,n,k,NULL);mpz_ui_pow_ui(grid,10,24);
    mpz_mul(n,grid,grid);mpz_mul(n,n,mpq_numref(x));mpz_cdiv_q(n,n,mpq_denref(x));
    mpz_sqrt(k,n);mpz_t square;mpz_init(square);mpz_mul(square,k,k);
    if (mpz_cmp(square,n)<0) mpz_add_ui(k,k,1);
    mpq_set_num(out,k);mpq_set_den(out,grid);mpq_canonicalize(out);
    mpz_clears(grid,n,k,square,NULL);
}
static void characteristic(WeightedRemainderLaw *s,const LawData *d,const mpq_t frequency)
{
    mpfr_t mid,lo,hi,delta,other,cl,ch;
    mpfr_inits2(256,mid,lo,hi,delta,other,cl,ch,(mpfr_ptr)0);
    mpq_t x,l,h,weight,t;mpq_inits(x,l,h,weight,t,NULL);
    for (unsigned i=0;i<d->count;++i) {
        mpq_mul(x,frequency,d->atoms[i].value);
        mpfr_set_q(mid,x,MPFR_RNDN);mpfr_set_q(lo,x,MPFR_RNDD);mpfr_set_q(hi,x,MPFR_RNDU);
        mpfr_sub(delta,mid,lo,MPFR_RNDU);mpfr_sub(other,hi,mid,MPFR_RNDU);
        if (mpfr_cmp(other,delta)>0) mpfr_set(delta,other,MPFR_RNDU);
        /* cos is 1-Lipschitz, so this includes argument conversion as
         * well as correctly directed MPFR cosine rounding at mid. */
        mpfr_cos(cl,mid,MPFR_RNDD);mpfr_cos(ch,mid,MPFR_RNDU);
        mpfr_sub(cl,cl,delta,MPFR_RNDD);mpfr_add(ch,ch,delta,MPFR_RNDU);
        if (mpfr_cmp_si(cl,-1)<0) mpfr_set_si(cl,-1,MPFR_RNDN);
        if (mpfr_cmp_ui(ch,1)>0) mpfr_set_ui(ch,1,MPFR_RNDN);
        mpfr_get_q(l,cl);mpfr_get_q(h,ch);probability(weight,d->atoms[i].count,s->period);
        mpq_mul(l,l,weight);mpq_mul(h,h,weight);
        mpq_add(s->real_lower,s->real_lower,l);mpq_add(s->real_upper,s->real_upper,h);
    }
    mpq_sub(s->rounding_width,s->real_upper,s->real_lower);
    mpq_mul(t,frequency,frequency);mpq_mul(t,t,s->squared_l2_error);
    sqrt_upper(s->characteristic_error_upper,t);
    mpq_sub(s->full_lower,s->real_lower,s->characteristic_error_upper);
    mpq_add(s->full_upper,s->real_upper,s->characteristic_error_upper);
    if (mpq_cmp_si(s->full_lower,-1,1)<0) mpq_set_si(s->full_lower,-1,1);
    if (mpq_cmp_ui(s->full_upper,1,1)>0) mpq_set_ui(s->full_upper,1,1);
    mpq_clears(x,l,h,weight,t,NULL);
    mpfr_clears(mid,lo,hi,delta,other,cl,ch,(mpfr_ptr)0);
}
int weighted_remainder_law_compute(WeightedRemainderLaw *out,
    WeightedRemainderLawOperation op,unsigned M,unsigned degree,
    const mpq_t a,const mpq_t b,const mpq_t margin)
{
    if (!out || M<2 || M>12 || degree>16 || op<WEIGHTED_LAW_MOMENT || op>WEIGHTED_LAW_CHARACTERISTIC ||
        !rational(a) || !rational(b) || !rational(margin)) return 0;
    if ((op==WEIGHTED_LAW_CDF || op==WEIGHTED_LAW_WINDOW || op==WEIGHTED_LAW_CONCENTRATION) && mpq_sgn(margin)<=0) return 0;
    if ((op==WEIGHTED_LAW_WINDOW && mpq_cmp(a,b)>0) || (op==WEIGHTED_LAW_CONCENTRATION && mpq_sgn(a)<0)) return 0;
    LawData d={calloc(WEIGHTED_REMAINDER_CLOCK_LAW_MAX,sizeof(LawAtom)),0};
    if (!d.atoms) return 0;
    WeightedRemainderLaw s;weighted_remainder_law_init(&s);s.cutoff=M;s.degree=degree;
    if (!weighted_remainder_clock_law(&s.period,&s.distinct,M,collect,&d)) { release(&d);weighted_remainder_law_clear(&s);return 0; }
    mpq_t lo,hi,t,u,weight,cross,variance;mpq_inits(lo,hi,t,u,weight,cross,variance,NULL);
    weighted_remainder_collision_variance_q(variance,s.squared_l2_error,cross,u,&s.binary_exponent,M);
    if (op==WEIGHTED_LAW_MOMENT) {
        for (unsigned i=0;i<d.count;++i) {
            mpz_pow_ui(mpq_numref(t),mpq_numref(d.atoms[i].value),degree);
            mpz_pow_ui(mpq_denref(t),mpq_denref(d.atoms[i].value),degree);
            probability(weight,d.atoms[i].count,s.period);mpq_mul(t,t,weight);
            mpq_add(s.finite,s.finite,t);mpq_abs(t,t);mpq_add(s.absolute,s.absolute,t);
        }
    } else if (op==WEIGHTED_LAW_CHARACTERISTIC) {
        characteristic(&s,&d,a);
    } else {
        mpq_mul(t,margin,margin);mpq_div(s.probability_error,s.squared_l2_error,t);
        if (op==WEIGHTED_LAW_CDF) {
            probability(s.finite,below(&d,a),s.period);
            mpq_sub(lo,a,margin);mpq_add(hi,a,margin);
            probability(s.full_lower,below(&d,lo),s.period);probability(s.full_upper,below(&d,hi),s.period);
            mpq_set(s.finite_expanded,s.full_upper);
        } else if (op==WEIGHTED_LAW_WINDOW) {
            probability(s.finite,window(&d,a,b),s.period);
            mpq_add(lo,a,margin);mpq_sub(hi,b,margin);probability(s.full_lower,window(&d,lo,hi),s.period);
            mpq_sub(lo,a,margin);mpq_add(hi,b,margin);probability(s.full_upper,window(&d,lo,hi),s.period);
            mpq_set(s.finite_expanded,s.full_upper);
        } else {
            probability(s.finite,concentration(&d,a),s.period);
            mpq_mul_2exp(t,margin,1);mpq_add(t,t,a);
            probability(s.full_upper,concentration(&d,t),s.period);mpq_set(s.finite_expanded,s.full_upper);
        }
        mpq_sub(s.full_lower,s.full_lower,s.probability_error);mpq_add(s.full_upper,s.full_upper,s.probability_error);
        clamp_probability(s.full_lower);clamp_probability(s.full_upper);
    }
    mpq_clears(lo,hi,t,u,weight,cross,variance,NULL);release(&d);
    WeightedRemainderLaw old=*out;*out=s;weighted_remainder_law_clear(&old);return 1;
}

int weighted_remainder_law_recurrence_q(mpq_t *probabilities,mpq_t mean_square,
    mpq_t second_moment,unsigned M,unsigned H,const mpq_t lower,const mpq_t upper)
{
    if (!probabilities || !mean_square || !second_moment || mean_square==second_moment || M<2 || M>12 ||
        H<1 || H>240 || !rational(lower) || !rational(upper) || mpq_cmp(lower,upper)>0) return 0;
    for (unsigned h=0;h<H;++h) if (probabilities[h]==mean_square || probabilities[h]==second_moment) return 0;
    unsigned period,distinct;
    if (!weighted_remainder_clock_law(&period,&distinct,M,NULL,NULL)) return 0;
    unsigned char *event=calloc(period,1);if (!event) return 0;
    mpq_t weights[13],value,t,c,mean,second;mpq_inits(value,t,c,mean,second,NULL);
    for (unsigned k=2;k<=M;++k) { mpq_init(weights[k]);weighted_remainder_weight_q(weights[k],k); }
    for (unsigned n=0;n<period;++n) {
        mpq_set_ui(value,0,1);
        for (unsigned k=2;k<=M;++k) {
            mpq_set_si(c,2L*(n%k)-(long)k+1,3);mpq_canonicalize(c);mpq_mul(t,c,weights[k]);mpq_add(value,value,t);
        }
        event[n]=mpq_cmp(value,lower)>=0 && mpq_cmp(value,upper)<=0;
    }
    unsigned count[240]={0};
    for (unsigned h=0;h<H;++h) for (unsigned n=0;n<period;++n) count[h]+=event[n] && event[(n+h)%period];
    probability(mean,count[0],period);mpq_mul(mean,mean,mean);
    mpq_set_ui(second,H*count[0],1);
    for (unsigned h=1;h<H;++h) { mpq_set_ui(t,2UL*(H-h)*count[h],1);mpq_add(second,second,t); }
    mpq_set_ui(t,1,(unsigned long)H*H*period);mpq_mul(second,second,t);
    for (unsigned h=0;h<H;++h) probability(probabilities[h],count[h],period);
    mpq_set(mean_square,mean);mpq_set(second_moment,second);
    for (unsigned k=2;k<=M;++k) mpq_clear(weights[k]);
    mpq_clears(value,t,c,mean,second,NULL);free(event);return 1;
}

static int index_arg(const char *p,unsigned low,unsigned high,unsigned *out)
{
    if (!p || !*p) return 0;
    unsigned n=0;
    for (;*p;++p) { if (*p<'0' || *p>'9') return 0;n=10*n+(unsigned)(*p-'0');if (n>high) return 0; }
    if (n<low) return 0;
    *out=n;return 1;
}
static int rational_arg(mpq_t q,const char *p)
{
    if (!p || !*p || strlen(p)>160) return 0;
    const char *start=p;if (*p=='-') ++p;
    unsigned digits=0,slash=0;
    for (;*p;++p) {
        if (*p=='/' && !slash && digits) { slash=1;digits=0; }
        else if (*p>='0' && *p<='9') ++digits;else return 0;
    }
    if (!digits || mpq_set_str(q,start,10) || mpz_sgn(mpq_denref(q))<=0) return 0;
    mpq_canonicalize(q);return rational(q);
}
static int cutoff_difference(unsigned M,const char *address)
{
    if (!*address || strlen(address)>1235) return 0;
    const char *p=address;if (*p=='-') ++p;if (!*p) return 0;
    for (;*p;++p) if (*p<'0' || *p>'9') return 0;
    mpz_t n,reflected,anchor;mpz_inits(n,reflected,anchor,NULL);
    int ok=!mpz_set_str(n,address,10) && mpz_sizeinbase(n,2)<=4096;
    if (!ok) { mpz_clears(n,reflected,anchor,NULL);return 0; }
    int negative=mpz_sgn(n)<0;
    if (negative) { mpz_neg(reflected,n);mpz_sub_ui(reflected,reflected,1);mpz_set_si(anchor,-1); }
    else mpz_set(reflected,n);
    WeightedRemainderClock c,z;weighted_remainder_clock_init(&c);weighted_remainder_clock_init(&z);
    weighted_remainder_clock_compute(&c,M,n);weighted_remainder_clock_compute(&z,M,anchor);
    mpq_t difference,correction,completed,factor;mpq_inits(difference,correction,completed,factor,NULL);
    mpq_sub(difference,c.centered_age,z.centered_age);
    int available=mpz_cmp_ui(reflected,M)<=0;
    if (available) {
        mpz_mul_ui(mpq_numref(factor),reflected,2);mpz_set_ui(mpq_denref(factor),3);mpq_canonicalize(factor);
        mpq_mul(correction,factor,c.omitted_mass);if (negative) mpq_neg(correction,correction);
        mpq_add(completed,difference,correction);
    }
    printf("Integer clock difference and completion\ncutoff=%u\nnegative_address=%d\ncompleted_difference_available=%d\n",M,negative,available);
    gmp_printf("address=%Zd\nanchor=%Zd\nreflected_address=%Zd\ncentered_clock=%Qd\nanchor_clock=%Qd\ncutoff_difference=%Qd\nstationary_age=%Qd\nomitted_mass=%Qd\ntail_correction=%Qd\ncompleted_difference=%Qd\n",
        n,anchor,reflected,c.centered_age,z.centered_age,difference,c.stationary_age,c.omitted_mass,correction,completed);
    puts("Completion is signed D(reflected_address) when the reflected address is at most the cutoff; unavailable completion fields are zero. These are finite clocks, not values of the limiting Haar potential at integers.");
    mpq_clears(difference,correction,completed,factor,NULL);weighted_remainder_clock_clear(&c);weighted_remainder_clock_clear(&z);
    mpz_clears(n,reflected,anchor,NULL);return 1;
}
static void tail_bound(unsigned M,unsigned L,const mpq_t H)
{
    mpq_t finite,error,cross,variance,alignment,mean,radius,mass,lo,hi,t,gap;
    mpq_inits(finite,error,cross,variance,alignment,mean,radius,mass,lo,hi,t,gap,NULL);
    unsigned exponent;mpz_t zero;mpz_init(zero);
    weighted_remainder_collision_variance_q(finite,error,cross,variance,&exponent,M);
    weighted_remainder_cylinder_q(alignment,mean,radius,mass,L,zero,M);
    WeightedRemainderClock clock;weighted_remainder_clock_init(&clock);weighted_remainder_clock_compute(&clock,M,zero);
    mpq_mul(t,H,H);mpq_div(hi,variance,t);
    mpq_sub(gap,H,clock.stationary_age);
    if (mpq_sgn(gap)>0) { mpq_mul(t,gap,gap);mpq_div(t,error,t);if (mpq_cmp(t,hi)<0) mpq_set(hi,t); }
    if (mpq_cmp_ui(hi,1,2)>0) mpq_set_ui(hi,1,2);
    mpq_sub(gap,alignment,H);
    if (mpq_sgn(gap)>0) {
        mpq_mul(lo,gap,gap);mpq_set_ui(t,(unsigned long)L*L,1);mpq_mul(t,t,variance);mpq_div(lo,lo,t);
    }
    printf("One-sided stationary tail bounds\nperiod_cutoff=%u\ncylinder_modulus=%u\n",M,L);
    gmp_printf("threshold=%Qd\ntail_lower=%Qd\ntail_upper=%Qd\nfinite_variance=%Qd\nfull_variance_upper=%Qd\nsquared_l2_error=%Qd\nstationary_age=%Qd\nalignment_lower=%Qd\n",H,lo,hi,finite,variance,error,clock.stationary_age,alignment);
    puts("Bounds apply equally to P(Y>threshold) and P(Y<-threshold). The lower bound uses the cylinder mean; the upper bound uses variance and, when available, the finite clock maximum. They may be conservative.");
    weighted_remainder_clock_clear(&clock);mpz_clear(zero);
    mpq_clears(finite,error,cross,variance,alignment,mean,radius,mass,lo,hi,t,gap,NULL);
}
static int block_activation(unsigned P,unsigned length,const mpq_t width)
{
    if (P<4 || length<1 || length>P/4 || mpq_sgn(width)<0) return 0;
    mpq_t bias,total,harmonic,increment,minimum,bound,t;
    mpq_inits(bias,total,harmonic,increment,minimum,bound,t,NULL);
    unsigned primes[240],count=0;
    for (unsigned p=P/2+1;p<=P;++p) {
        int prime=p>=2;
        for (unsigned d=2;d<=p/d;++d) if (p%d==0) { prime=0;break; }
        if (!prime) continue;
        primes[count++]=p;
        mpq_set_ui(bias,length,p);mpq_canonicalize(bias);mpq_add(total,total,bias);
        mpq_set_ui(harmonic,0,1);
        for (unsigned j=1;j<p;++j) { mpq_set_ui(t,1,j);mpq_add(harmonic,harmonic,t); }
        mpq_set_ui(t,1,p);mpq_mul(increment,harmonic,t);
        if (count==1 || mpq_cmp(increment,minimum)<0) mpq_set(minimum,increment);
    }
    int ok=count && mpq_cmp(width,minimum)<0;
    if (ok) {
        mpq_set_ui(t,1,1);mpq_add(t,t,total);mpq_set_ui(bound,400,1);mpq_div(bound,bound,t);
        clamp_probability(bound);
        printf("Prime activation for an increment block\nprime_cutoff=%u\nblock_length=%u\nprime_count=%u\n",P,length,count);
        for (unsigned i=0;i<count;++i) {
            mpq_set_ui(bias,length,primes[i]);mpq_canonicalize(bias);
            gmp_printf("bias_%u=%Qd\n",primes[i],bias);
        }
        gmp_printf("width=%Qd\nminimum_increment=%Qd\nbias_sum=%Qd\nsquared_probability_upper=%Qd\n",width,minimum,total,bound);
        puts("Independent prime hit probabilities are length/p. Width must be strictly below every selected reset increment. The squared bound is min(1,400/(1+sum biases)); this finite prime selection may give a trivial bound.");
    }
    mpq_clears(bias,total,harmonic,increment,minimum,bound,t,NULL);return ok;
}
int weighted_remainder_law_command(int argc,char **argv)
{
    if (argc<4) goto bad;
    unsigned M,degree=0,H,L;
    if (!index_arg(argv[3],2,240,&M)) goto bad;
    if (!strcmp(argv[2],"clock-difference")) {
        if (argc!=5 || !cutoff_difference(M,argv[4])) goto bad;
        return 0;
    }
    mpq_t a,b,margin;mpq_inits(a,b,margin,NULL);mpq_set_ui(margin,1,1);
    WeightedRemainderLawOperation op=WEIGHTED_LAW_MOMENT;int ok=0;
    if (!strcmp(argv[2],"law-activation")) {
        ok=argc==6 && index_arg(argv[4],1,60,&H) && rational_arg(a,argv[5]) && block_activation(M,H,a);
    } else if (!strcmp(argv[2],"law-tail-bound")) {
        ok=argc==6 && rational_arg(a,argv[4]) && mpq_sgn(a)>0 && index_arg(argv[5],1,240,&L);
        if (ok) tail_bound(M,L,a);
    } else if (!strcmp(argv[2],"law-recurrence")) {
        ok=argc==7 && M<=12 && rational_arg(a,argv[4]) && rational_arg(b,argv[5]) && index_arg(argv[6],1,240,&H);
        if (ok) {
            mpq_t probabilities[240],mean,second;mpq_inits(mean,second,NULL);
            for (unsigned h=0;h<H;++h) mpq_init(probabilities[h]);
            ok=weighted_remainder_law_recurrence_q(probabilities,mean,second,M,H,a,b);
            if (ok) {
                printf("Complete-period interval recurrence\ncutoff=%u\nhorizon=%u\n",M,H);
                for (unsigned h=0;h<H;++h) gmp_printf("intersection_%u=%Qd\n",h,probabilities[h]);
                gmp_printf("mean_square=%Qd\nsecond_moment=%Qd\n",mean,second);
            }
            for (unsigned h=0;h<H;++h) mpq_clear(probabilities[h]);
            mpq_clears(mean,second,NULL);
        }
    } else {
        if (!strcmp(argv[2],"law-moment")) ok=argc==5 && index_arg(argv[4],0,16,&degree);
        else if (!strcmp(argv[2],"law-cdf")) { op=WEIGHTED_LAW_CDF;ok=argc==6 && rational_arg(a,argv[4]) && rational_arg(margin,argv[5]); }
        else if (!strcmp(argv[2],"law-window")) { op=WEIGHTED_LAW_WINDOW;ok=argc==7 && rational_arg(a,argv[4]) && rational_arg(b,argv[5]) && rational_arg(margin,argv[6]); }
        else if (!strcmp(argv[2],"law-concentration")) { op=WEIGHTED_LAW_CONCENTRATION;ok=argc==6 && rational_arg(a,argv[4]) && rational_arg(margin,argv[5]); }
        else if (!strcmp(argv[2],"law-characteristic")) { op=WEIGHTED_LAW_CHARACTERISTIC;ok=argc==5 && rational_arg(a,argv[4]); }
        WeightedRemainderLaw s;weighted_remainder_law_init(&s);
        ok=ok && weighted_remainder_law_compute(&s,op,M,degree,a,b,margin);
        if (ok) {
            printf("Complete finite clock law\ncutoff=%u\nperiod=%u\ndistinct=%u\ndegree=%u\n",s.cutoff,s.period,s.distinct,s.degree);
            if (op==WEIGHTED_LAW_CHARACTERISTIC) {
                gmp_printf("real_lower=%Qd\nreal_upper=%Qd\nimaginary=0\nrounding_width=%Qd\ncharacteristic_error_upper=%Qd\nfull_real_lower=%Qd\nfull_real_upper=%Qd\n",s.real_lower,s.real_upper,s.rounding_width,s.characteristic_error_upper,s.full_lower,s.full_upper);
            } else {
                gmp_printf("finite=%Qd\n",s.finite);
                if (op==WEIGHTED_LAW_MOMENT) gmp_printf("absolute_moment=%Qd\n",s.absolute);
                else gmp_printf("full_lower=%Qd\nfull_upper=%Qd\nfinite_expanded=%Qd\nprobability_error=%Qd\n",s.full_lower,s.full_upper,s.finite_expanded,s.probability_error);
            }
            gmp_printf("squared_l2_error=%Qd\n",s.squared_l2_error);
            puts("The finite law uses every phase with its multiplicity. Full-law bounds use the proved L2 cutoff budget and may be wide; finite moments are not full-moment certificates.");
        }
        weighted_remainder_law_clear(&s);
    }
    mpq_clears(a,b,margin,NULL);if (!ok) goto bad;return 0;
bad:
    fputs("Use law-moment M degree; law-cdf M x margin; law-window M lower upper margin; law-concentration M width margin; law-characteristic M frequency; law-recurrence M lower upper horizon; law-activation P length width; law-tail-bound M threshold modulus; clock-difference M address. "
          "Complete laws require M=2..12, degree=0..16, positive rational margin, nonnegative width, ordered interval and horizon=1..240. Activation requires P=4..240, length=1..floor(P/4) and width strictly below every selected prime reset increment. Tail bounds require M=2..240, threshold>0 and modulus=1..240. Rational components have at most 256 bits. Clock differences admit M=2..240 and signed decimal addresses up to 4096 bits.\n",stderr);
    return 1;
}
