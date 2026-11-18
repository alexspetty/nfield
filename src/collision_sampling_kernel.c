/* Exact finite capacity and sampled energy kernels. */
#include "collision_sampling.h"
#include <stdint.h>

static void cs_fraction(mpq_t out,long numerator,unsigned long denominator)
{ mpq_set_si(out,numerator,denominator); mpq_canonicalize(out); }

static void cs_scale(mpq_t out,const mpq_t in,long numerator,unsigned long den)
{
    mpq_t factor; mpq_init(factor); cs_fraction(factor,numerator,den);
    mpq_mul(out,in,factor); mpq_clear(factor);
}

static uint64_t cs_floor_sum(uint64_t n,uint64_t m,uint64_t a,uint64_t b)
{
    uint64_t sum=0;
    for(;;) {
        if(a>=m) { sum+=(n-1)*n*(a/m)/2; a%=m; }
        if(b>=m) { sum+=n*(b/m); b%=m; }
        uint64_t y=a*n+b;
        if(y<m) return sum;
        n=y/m; b=y%m; uint64_t t=m; m=a; a=t;
    }
}

int collision_sampling_capacity_q(mpq_t out,unsigned n)
{
    if(n>=COLLISION_SAMPLING_MAX_PRIME) return 0;
    mpq_t harmonic[COLLISION_SAMPLING_MAX_PRIME], sum, term;
    unsigned jordan[COLLISION_SAMPLING_MAX_PRIME];
    mpq_inits(sum,term,NULL);
    for(unsigned i=0;i<=n;i++) {
        mpq_init(harmonic[i]); jordan[i]=i*i;
        if(i) { cs_fraction(term,1,i); mpq_add(harmonic[i],harmonic[i-1],term); }
    }
    for(unsigned prime=2;prime<=n;prime++) {
        int isprime=1; for(unsigned d=2;d<=prime/d;d++) if(prime%d==0) isprime=0;
        if(isprime) for(unsigned d=prime;d<=n;d+=prime)
            jordan[d]=jordan[d]/(prime*prime)*(prime*prime-1);
    }
    for(unsigned d=1;d<=n;d++) {
        mpq_mul(term,harmonic[n/d],harmonic[n/d]);
        cs_scale(term,term,jordan[d],3UL*d*d); mpq_add(sum,sum,term);
    }
    mpq_set(out,sum);
    for(unsigned i=0;i<=n;i++) mpq_clear(harmonic[i]);
    mpq_clears(sum,term,NULL); return 1;
}

int collision_sampling_energy_q(mpq_t sampled,unsigned p)
{
    if(p<3||p>10007||p%2==0)return 0;
    for(unsigned d=3;d<=p/d;d+=2)if(p%d==0)return 0;
    uint64_t m=(uint64_t)p*p,words[2]={0,0};
    for(uint64_t a=1;a<m;a++)if(a%p) {
        uint64_t slope=(p+1)*a;
        int64_t count=(int64_t)(cs_floor_sum(p,m,slope,a)-cs_floor_sum(p,m,slope,0));
        int64_t d=(int64_t)p*count-(int64_t)a;
        uint64_t previous=words[0];words[0]+=(uint64_t)(d*d);
        if(words[0]<previous)words[1]++;
    }
    /* Each square fits 64 bits; the exact total needs two limbs at the
     * larger resolutions. Import both, never round the accumulator. */
    mpz_import(mpq_numref(sampled),2,-1,sizeof(uint64_t),0,0,words);
    uint64_t denominator=m*m;mpz_import(mpq_denref(sampled),1,1,sizeof(uint64_t),0,0,&denominator);
    mpq_canonicalize(sampled);return 1;
}
