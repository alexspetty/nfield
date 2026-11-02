/* Exact carrier sums. No asymptotic assertion is inferred from a scan. */
#include "collision_sampling.h"
#include "collision_capacity_transition.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <limits.h>
#include <math.h>

const char *const collision_sampling_names[CS_FIELD_COUNT] = {
    "capacity", "sampled", "defect", "endpoint", "X", "reservoir",
    "alias_A", "alias_C", "X_term", "reservoir_term", "alias_A_term",
    "alias_C_term", "bridge", "alias", "bridge_error", "alias_error"
};
const char *const collision_switching_names[CSS_FIELD_COUNT] = {
    "reservoir", "dwell_area", "fresh_area", "energy", "increment_energy",
    "charge", "release", "mean", "coherent_energy", "variance",
    "full_triangle", "full_triangle_bridge"
};
const char *const collision_poles_names[CSP_FIELD_COUNT] = {
    "diagonal","off_diagonal","main","R0","Ra","Rk","four_way_error","energy_error"
};
static unsigned cs_gcd(unsigned a, unsigned b)
{ while (b) { unsigned t=a%b; a=b; b=t; } return a; }
static unsigned cs_inverse(unsigned a, unsigned m)
{
    long x=0, y=1, r=m, s=a%m;
    while(s) { long q=r/s, t=r-q*s; r=s; s=t; t=x-q*y; x=y; y=t; }
    return (unsigned)((x%(long)m+(long)m)%(long)m);
}
static int cs_prime(unsigned p)
{
    if (p<3 || p>COLLISION_SAMPLING_MAX_PRIME || !(p&1)) return 0;
    for(unsigned d=3; d<=p/d; d+=2) if(p%d==0) return 0;
    return 1;
}
static int cs_mask(unsigned p,const unsigned char *mask,unsigned length)
{
    if (!cs_prime(p)) return 0;
    if (!mask) return length==0;
    if (length!=p) return 0;
    for(unsigned k=0;k<p;k++)
        if(mask[k]>1 || (mask[k] && (k<2 || k>=p-1))) return 0;
    return 1;
}
static int cs_selected(const unsigned char *mask,unsigned k)
{ return !mask || mask[k]; }
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
static void cs_saw(mpq_t out,unsigned residue,unsigned modulus)
{
    residue%=modulus;
    cs_fraction(out,residue?2L*residue-(long)modulus:0,2UL*modulus);
}
static void cs_dedekind(mpq_t out,unsigned h,unsigned k)
{
    if(k==1 || h==0) { mpq_set_ui(out,0,1); return; }
    mpq_t next, term; mpq_inits(next,term,NULL);
    /* -(1/4)+h/(12k)+k/(12h)+1/(12hk). All products fit uint64_t. */
    cs_fraction(term,(long)h*h+(long)k*k+1-3L*h*k,12UL*h*k);
    cs_dedekind(next,k%h,h); mpq_sub(out,term,next);
    mpq_clears(next,term,NULL);
}
int collision_sampling_dedekind_q(mpq_t out,unsigned k,unsigned long long h)
{
    if(!k || k>COLLISION_SAMPLING_MAX_PRIME*COLLISION_SAMPLING_MAX_PRIME)
        return 0;
    unsigned r=(unsigned)(h%k), g=cs_gcd(r,k);
    cs_dedekind(out,r/g,k/g); return 1;
}
void collision_sampling_init(CollisionSampling *out)
{ for(unsigned i=0;i<CS_FIELD_COUNT;i++) mpq_init(out->value[i]); }
void collision_sampling_clear(CollisionSampling *out)
{ for(unsigned i=0;i<CS_FIELD_COUNT;i++) mpq_clear(out->value[i]); }
void collision_switching_init(CollisionSwitching *out)
{ for(unsigned i=0;i<CSS_FIELD_COUNT;i++) mpq_init(out->value[i]); }
void collision_switching_clear(CollisionSwitching *out)
{ for(unsigned i=0;i<CSS_FIELD_COUNT;i++) mpq_clear(out->value[i]); }
void collision_poles_init(CollisionPoles *out)
{ for(unsigned i=0;i<CSP_FIELD_COUNT;i++) mpq_init(out->value[i]); }
void collision_poles_clear(CollisionPoles *out)
{ for(unsigned i=0;i<CSP_FIELD_COUNT;i++) mpq_clear(out->value[i]); }

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
static void cs_jump(mpq_t out,unsigned k,unsigned prefix,unsigned a)
{
    uint64_t floors=cs_floor_sum(prefix,k,a,a);
    cs_fraction(out,(long)a*prefix*(prefix+1)-2L*k*(long)floors-(long)prefix*k,k);
}
int collision_sampling_correlation_q(mpq_t out,unsigned k,unsigned prefix,
                                      unsigned long long slope)
{
    if(k<2 || k>COLLISION_SAMPLING_MAX_MODULUS || prefix>=k) return 0;
    unsigned c=(unsigned)(slope%k);
    mpq_t sum,jump,saw; mpq_inits(sum,jump,saw,NULL);
    for(unsigned a=1;a<k;a++) if(cs_gcd(a,k)==1) {
        cs_jump(jump,k,prefix,a); cs_saw(saw,(c*a)%k,k);
        mpq_mul(jump,jump,saw); mpq_add(sum,sum,jump);
    }
    mpq_set(out,sum); mpq_clears(sum,jump,saw,NULL); return 1;
}
int collision_sampling_carrier_q(mpq_t x,mpq_t reservoir,mpq_t alias_a,
                                  mpq_t alias_c,unsigned p,unsigned k)
{
    if(!cs_prime(p) || !k || k>=p || x==reservoir || x==alias_a || x==alias_c ||
       reservoir==alias_a || reservoir==alias_c || alias_a==alias_c) return 0;
    unsigned n=p-1, m=p*p;
    mpq_t xx,rr,aa,cc,t; mpq_inits(xx,rr,aa,cc,t,NULL);
    for(unsigned a=k+1;a<=n;a++) if(cs_gcd(a,k)==1) {
        cs_fraction(t,(long)(n/a)*(a*a+k*k),(unsigned long)a*k);
        mpq_add(xx,xx,t);
        if(k>1) {
            collision_sampling_dedekind_q(t,k,(uint64_t)(m%k)*cs_inverse(a,k));
            cs_scale(t,t,-8L*(n/a),1); mpq_add(rr,rr,t);
        }
    }
    if(k>1) {
        collision_sampling_correlation_q(aa,k,n%k,m);
        cs_scale(aa,aa,n/k,1);
        for(unsigned a=1;a<k;a++) if(cs_gcd(a,k)==1) {
            unsigned r=((m%k)*a)%k;
            cs_fraction(t,6L*r*r-6L*r*k+(long)k*k,6UL*k*k);
            mpq_add(cc,cc,t);
        }
        cs_scale(cc,cc,n/k,1);
    }
    mpq_set(x,xx); mpq_set(reservoir,rr); mpq_set(alias_a,aa); mpq_set(alias_c,cc);
    mpq_clears(xx,rr,aa,cc,t,NULL); return 1;
}
int collision_sampling_prefix_q(mpq_t out,unsigned p,unsigned k,unsigned cutoff)
{
    if(!cs_prime(p) || k<2 || k>=p || cutoff>=p) return 0;
    mpq_t sum,t; mpq_inits(sum,t,NULL);
    /* A complete reduced-residue block is exactly zero. */
    for(unsigned a=1;a<=cutoff%k;a++) if(cs_gcd(a,k)==1) {
        collision_sampling_dedekind_q(t,k,(uint64_t)((p*p)%k)*cs_inverse(a,k));
        mpq_add(sum,sum,t);
    }
    mpq_set(out,sum); mpq_clears(sum,t,NULL); return 1;
}
int collision_sampling_q(CollisionSampling *out,unsigned p)
{
    if(!out || !cs_prime(p)) return 0;
    unsigned n=p-1, m=p*p;
    CollisionSampling temp; collision_sampling_init(&temp);
    mpq_t x,r,a,c,t; mpq_inits(x,r,a,c,t,NULL);
    collision_sampling_capacity_q(temp.value[CS_CAPACITY],n);
    collision_sampling_energy_q(temp.value[CS_SAMPLED],p);
    mpq_sub(temp.value[CS_DEFECT],temp.value[CS_CAPACITY],temp.value[CS_SAMPLED]);
    cs_fraction(temp.value[CS_ENDPOINT],(long)n*n,m);
    cs_fraction(temp.value[CS_ALIAS_C],n,6);
    for(unsigned k=1;k<=n;k++) {
        collision_sampling_carrier_q(x,r,a,c,p,k);
        mpq_add(temp.value[CS_X],temp.value[CS_X],x);
        mpq_add(temp.value[CS_RESERVOIR],temp.value[CS_RESERVOIR],r);
        mpq_add(temp.value[CS_ALIAS_A],temp.value[CS_ALIAS_A],a);
        mpq_add(temp.value[CS_ALIAS_C],temp.value[CS_ALIAS_C],c);
    }
    cs_fraction(t,n,1); mpq_add(t,t,temp.value[CS_X]);
    cs_scale(temp.value[CS_X_TERM],t,2,3UL*m*m);
    cs_scale(temp.value[CS_RESERVOIR_TERM],temp.value[CS_RESERVOIR],1,m);
    cs_scale(temp.value[CS_ALIAS_A_TERM],temp.value[CS_ALIAS_A],4,m);
    cs_scale(temp.value[CS_ALIAS_C_TERM],temp.value[CS_ALIAS_C],-2L*p*n,(unsigned long)m*m);
    mpq_sub(temp.value[CS_BRIDGE],temp.value[CS_ENDPOINT],temp.value[CS_X_TERM]);
    mpq_sub(temp.value[CS_BRIDGE],temp.value[CS_BRIDGE],temp.value[CS_RESERVOIR_TERM]);
    mpq_add(temp.value[CS_ALIAS],temp.value[CS_ENDPOINT],temp.value[CS_ALIAS_A_TERM]);
    mpq_add(temp.value[CS_ALIAS],temp.value[CS_ALIAS],temp.value[CS_ALIAS_C_TERM]);
    mpq_sub(temp.value[CS_BRIDGE_ERROR],temp.value[CS_BRIDGE],temp.value[CS_DEFECT]);
    mpq_sub(temp.value[CS_ALIAS_ERROR],temp.value[CS_ALIAS],temp.value[CS_DEFECT]);
    for(unsigned i=0;i<CS_FIELD_COUNT;i++) mpq_set(out->value[i],temp.value[i]);
    mpq_clears(x,r,a,c,t,NULL); collision_sampling_clear(&temp); return 1;
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
int collision_sampling_poles_q(CollisionPoles *out,unsigned p)
{
    if(!out||!cs_prime(p)) return 0;
    unsigned n=p-1,m=p*p;
    CollisionPoles z; collision_poles_init(&z);
    mpq_t t,u,energy; mpq_inits(t,u,energy,NULL);
    collision_sampling_dedekind_q(t,m,1); cs_scale(z.value[CSP_DIAGONAL],t,4L*n,1);
    for(unsigned a=2;a<=n;a++) for(unsigned k=1;k<a;k++) if(cs_gcd(a,k)==1) {
        unsigned weight=n/a;
        collision_sampling_dedekind_q(t,m,(uint64_t)a*cs_inverse(k,m));
        cs_scale(t,t,8L*weight,1); mpq_add(z.value[CSP_OFF_DIAGONAL],z.value[CSP_OFF_DIAGONAL],t);
        cs_fraction(t,2L*m*weight,3UL*a*k); mpq_add(z.value[CSP_MAIN],z.value[CSP_MAIN],t);
        cs_fraction(t,2L*weight*(a*a+k*k),3UL*a*k*m); cs_fraction(u,2L*weight,1);
        mpq_sub(t,t,u); mpq_add(z.value[CSP_R0],z.value[CSP_R0],t);
        collision_sampling_dedekind_q(t,a,(uint64_t)k*cs_inverse(m,a));
        cs_scale(t,t,-8L*weight,1); mpq_add(z.value[CSP_RA],z.value[CSP_RA],t);
        if(k>1) {
            collision_sampling_dedekind_q(t,k,(uint64_t)m*cs_inverse(a,k));
            cs_scale(t,t,-8L*weight,1); mpq_add(z.value[CSP_RK],z.value[CSP_RK],t);
        }
    }
    mpq_set(t,z.value[CSP_MAIN]);
    for(unsigned i=CSP_R0;i<=CSP_RK;i++) mpq_add(t,t,z.value[i]);
    mpq_sub(z.value[CSP_FOUR_WAY_ERROR],t,z.value[CSP_OFF_DIAGONAL]);
    /* Independent uncompressed pair table, rather than calling the sampling
     * bridge or defining its residual to be zero. */
    for(unsigned a=1;a<=n;a++) for(unsigned k=1;k<=n;k++) {
        collision_sampling_dedekind_q(t,m,(uint64_t)a*cs_inverse(k,m));
        mpq_add(energy,energy,t);
    }
    cs_scale(energy,energy,4,1);
    mpq_add(t,z.value[CSP_DIAGONAL],z.value[CSP_OFF_DIAGONAL]);
    mpq_sub(z.value[CSP_ENERGY_ERROR],t,energy);
    for(unsigned i=0;i<CSP_FIELD_COUNT;i++) mpq_set(out->value[i],z.value[i]);
    mpq_clears(t,u,energy,NULL); collision_poles_clear(&z); return 1;
}
int collision_sampling_collar_q(mpq_t absolute,mpq_t signed_mass,unsigned p,unsigned cutoff)
{
    if(!cs_prime(p)||cutoff<1||cutoff>p/2||absolute==signed_mass) return 0;
    mpq_t a,s,t; mpq_inits(a,s,t,NULL);
    for(unsigned k=2;k<p;k++) {
        unsigned rem=(p*p)%k, distance=rem<k-rem?rem:k-rem;
        if(!distance||distance>cutoff) continue;
        for(unsigned h=1;h<=(p-1)/(k+1);h++) {
            collision_sampling_prefix_q(t,p,k,(p-1)/h); mpq_add(s,s,t);
            mpq_abs(t,t); mpq_add(a,a,t);
        }
    }
    cs_scale(absolute,a,8,(unsigned long)p*p);
    cs_scale(signed_mass,s,8,(unsigned long)p*p);
    mpq_clears(a,s,t,NULL); return 1;
}
int collision_sampling_state_q(mpq_t burden,mpq_t fresh,unsigned p,unsigned state,
                                const unsigned char *mask,unsigned length)
{
    if(burden==fresh || !cs_mask(p,mask,length) || !state || state>=p) return 0;
    mpq_t b,f,t; mpq_inits(b,f,t,NULL);
    for(unsigned k=2;k<state;k++) if(cs_selected(mask,k)) {
        collision_sampling_prefix_q(t,p,k,state); mpq_add(b,b,t);
        if(cs_gcd(k,state)==1) {
            collision_sampling_dedekind_q(t,k,(uint64_t)((p*p)%k)*cs_inverse(state,k));
            mpq_add(f,f,t);
        }
    }
    mpq_set(burden,b); mpq_set(fresh,f); mpq_clears(b,f,t,NULL); return 1;
}
int collision_sampling_convolution_q(mpq_t primitive,mpq_t full,mpq_t elementary,
                                      unsigned p,unsigned state)
{
    if(!cs_prime(p) || !state || state>=p || primitive==full ||
       primitive==elementary || full==elementary) return 0;
    unsigned m=p*p,phi=0;
    mpq_t c,a,e,t,h; mpq_inits(c,a,e,t,h,NULL);
    for(unsigned k=1;k<state;k++) {
        collision_sampling_dedekind_q(t,m,(uint64_t)k*cs_inverse(state-k,m));
        mpq_add(a,a,t);
        if(cs_gcd(k,state)==1) {
            mpq_add(c,c,t); phi++;
            cs_fraction(t,1,k); mpq_add(h,h,t);
        }
    }
    if(state>=3) {
        cs_scale(e,h,m,12UL*state); cs_scale(t,h,state,12UL*m); mpq_add(e,e,t);
        cs_fraction(t,phi,12UL*m); mpq_sub(e,e,t);
        cs_fraction(t,phi,8); mpq_sub(e,e,t);
    }
    mpq_set(primitive,c); mpq_set(full,a); mpq_set(elementary,e);
    mpq_clears(c,a,e,t,h,NULL); return 1;
}
int collision_sampling_switching_q(CollisionSwitching *out,unsigned p,
                                    const unsigned char *mask,unsigned length)
{
    if(!out || !cs_mask(p,mask,length)) return 0;
    unsigned n=p-1;
    CollisionSwitching z; collision_switching_init(&z);
    mpq_t b,f,previous,t,j,c,a,e,x,r; mpq_inits(b,f,previous,t,j,c,a,e,x,r,NULL);
    for(unsigned k=2;k<n;k++) if(cs_selected(mask,k)) {
        collision_sampling_carrier_q(x,r,a,c,p,k); cs_scale(r,r,-1,8);
        mpq_add(z.value[CSS_RESERVOIR],z.value[CSS_RESERVOIR],r);
    }
    for(unsigned state=2;state<=n;state++) {
        unsigned h=n/state, dwell=h-n/(state+1);
        collision_sampling_convolution_q(c,a,e,p,state);
        mpq_add(z.value[CSS_TRIANGLE],z.value[CSS_TRIANGLE],a);
        if(state>=3) {
            cs_scale(t,e,h,1); mpq_add(z.value[CSS_TRIANGLE_BRIDGE],z.value[CSS_TRIANGLE_BRIDGE],t);
        }
        collision_sampling_state_q(b,f,p,state,mask,length);
        cs_scale(t,b,dwell,1); mpq_add(z.value[CSS_DWELL_AREA],z.value[CSS_DWELL_AREA],t);
        cs_scale(t,f,h,1); mpq_add(z.value[CSS_FRESH_AREA],z.value[CSS_FRESH_AREA],t);
        mpq_mul(t,b,b); cs_scale(t,t,dwell,1); mpq_add(z.value[CSS_ENERGY],z.value[CSS_ENERGY],t);
        mpq_mul(j,f,f); cs_scale(j,j,1,2); mpq_mul(t,previous,f); mpq_add(j,j,t);
        cs_scale(t,j,2L*h,1); mpq_add(z.value[CSS_INCREMENT_ENERGY],z.value[CSS_INCREMENT_ENERGY],t);
        cs_scale(t,j,h,1);
        if(mpq_sgn(t)>=0) mpq_add(z.value[CSS_CHARGE],z.value[CSS_CHARGE],t);
        else mpq_sub(z.value[CSS_RELEASE],z.value[CSS_RELEASE],t);
        mpq_set(previous,b);
    }
    unsigned d=n/3;
    if(d) {
        cs_scale(z.value[CSS_MEAN],z.value[CSS_DWELL_AREA],1,d);
        mpq_mul(t,z.value[CSS_DWELL_AREA],z.value[CSS_DWELL_AREA]);
        cs_scale(z.value[CSS_COHERENT_ENERGY],t,1,d);
        mpq_sub(z.value[CSS_VARIANCE],z.value[CSS_ENERGY],z.value[CSS_COHERENT_ENERGY]);
    }
    cs_scale(t,z.value[CSS_TRIANGLE],1,2);
    mpq_sub(z.value[CSS_TRIANGLE_BRIDGE],z.value[CSS_TRIANGLE_BRIDGE],t);
    collision_sampling_dedekind_q(t,p*p,1); cs_scale(t,t,n/2,2);
    mpq_add(z.value[CSS_TRIANGLE_BRIDGE],z.value[CSS_TRIANGLE_BRIDGE],t);
    for(unsigned i=0;i<CSS_FIELD_COUNT;i++) mpq_set(out->value[i],z.value[i]);
    mpq_clears(b,f,previous,t,j,c,a,e,x,r,NULL); collision_switching_clear(&z); return 1;
}

static int cs_mobius(unsigned n)
{
    int value=1;
    for(unsigned p=2;p<=n/p;p++) if(n%p==0) {
        n/=p; value=-value; if(n%p==0) return 0;
        while(n%p==0) n/=p;
    }
    return n>1?-value:value;
}
static long double cs_to_ld(const mpq_t value)
{
    /* The small Dedekind numerators/denominators in these transforms fit
     * exactly in a long. Avoid narrowing through mpq_get_d(double). */
    return (long double)mpz_get_si(mpq_numref(value)) /
           (long double)mpz_get_ui(mpq_denref(value));
}
static long double cs_inverse_series(unsigned q,unsigned r)
{
    if(q==1 || r%q==0) return 0;
    long double total=0,pi=acosl(-1.0L); mpq_t saw; mpq_init(saw);
    for(unsigned u=1;u<q;u++) if(cs_gcd(u,q)==1) {
        cs_saw(saw,(r*cs_inverse(u,q))%q,q);
        total+=cs_to_ld(saw)/tanl(pi*u/q);
    }
    mpq_clear(saw); return pi*total/(2*q);
}
static long double complex cs_full_transform(unsigned q,unsigned t,int units)
{
    if(q==1) return 0;
    long double complex total=0; long double pi=acosl(-1.0L);
    mpq_t d; mpq_init(d);
    for(unsigned h=1;h<q;h++) if(!units || cs_gcd(h,q)==1) {
        collision_sampling_dedekind_q(d,q,h);
        long double angle=-2*pi*((t*h)%q)/q;
        total+=cs_to_ld(d)*(cosl(angle)+I*sinl(angle));
    }
    mpq_clear(d); return total;
}
int collision_sampling_transform(CollisionInverseTransform *out,unsigned q,
                                  unsigned long long frequency)
{
    if(!out || q<2 || q>COLLISION_SAMPLING_MAX_MODULUS) return 0;
    unsigned t=(unsigned)(frequency%q); CollisionInverseTransform z={0};
    z.full=cs_full_transform(q,t,0); z.unit=cs_full_transform(q,t,1);
    z.inverse_series=cs_inverse_series(q,t);
    for(unsigned g=1;g<=q;g++) if(q%g==0 && t%g==0 && q/g>=2)
        z.full_from_inverse+=I*(q/(long double)g)*cs_inverse_series(q/g,t/g)/acosl(-1.0L);
    for(unsigned d=1;d<=q;d++) if(q%d==0)
        z.unit_from_mobius+=cs_mobius(d)*cs_full_transform(q/d,t,0);
    unsigned c=cs_gcd(t,q), reduced=q/c, product=1, remaining=q;
    for(unsigned p=2;p<=remaining/p;p++) if(remaining%p==0) {
        if(reduced%p) product*=p;
        while(remaining%p==0) remaining/=p;
    }
    if(remaining>1 && reduced%remaining) product*=remaining;
    if(reduced>1) for(unsigned d=1;d<=product;d++) if(product%d==0)
        z.inverse_from_descent+=cs_mobius(d)*cs_inverse_series(reduced,
            ((t/c)*cs_inverse(d,reduced))%reduced)/(long double)d;
    z.full_error=cabsl(z.full-z.full_from_inverse);
    z.unit_error=cabsl(z.unit-z.unit_from_mobius);
    z.descent_error=fabsl(z.inverse_series-z.inverse_from_descent);
    *out=z; return 1;
}
int collision_sampling_inverse_q(mpq_t prefix,mpq_t harmonic,mpq_t tail_bound,
    unsigned q,unsigned long long frequency,unsigned cutoff)
{
    if(q<2 || q>COLLISION_SAMPLING_MAX_MODULUS || cutoff>4096 ||
       prefix==harmonic || prefix==tail_bound || harmonic==tail_bound) return 0;
    unsigned r=(unsigned)(frequency%q);
    mpq_t sum,series,saw,t; mpq_inits(sum,series,saw,t,NULL);
    for(unsigned n=1;n<=cutoff;n++) if(cs_gcd(n,q)==1) {
        cs_saw(saw,(r*cs_inverse(n,q))%q,q); mpq_add(sum,sum,saw);
        cs_scale(t,saw,1,n); mpq_add(series,series,t);
    }
    mpq_set(prefix,sum); mpq_set(harmonic,series);
    cs_fraction(tail_bound,r?q:0,2UL*(cutoff+1));
    mpq_clears(sum,series,saw,t,NULL); return 1;
}

static int cs_uint(const char *text,unsigned *out)
{
    if(!text || !*text) return 0;
    for(const char *s=text;*s;s++) if(*s<'0'||*s>'9') return 0;
    errno=0; char *end; unsigned long x=strtoul(text,&end,10);
    if(errno || *end || x>UINT_MAX) return 0;
    *out=(unsigned)x; return 1;
}
static void cs_print(const char *key,const mpq_t value)
{ gmp_printf("%s=%Qd\n",key,value); }
#include "collision_sampling_source.inc"
void collision_sampling_help(void)
{
    puts("Exact collision sampling and carrier calculus\n\n"
         "Commands\n"
         "  nfield collision-sampling inspect <odd-prime>\n"
         "  nfield collision-sampling sampled <odd-prime>\n"
         "  nfield collision-sampling carrier <odd-prime> <k>\n"
         "  nfield collision-sampling poles <odd-prime>\n"
         "  nfield collision-sampling collar <odd-prime> <displacement-cutoff>\n"
         "  nfield collision-sampling prefix <odd-prime> <k> <X>\n"
         "  nfield collision-sampling correlation <k> <prefix> <slope>\n"
         "  nfield collision-sampling state <odd-prime> <X>\n"
         "  nfield collision-sampling switching <odd-prime> [--carriers 2,3,...]\n"
         "  nfield collision-sampling convolution <odd-prime> <X>\n"
         "  nfield collision-sampling capacity <N>\n"
         "  nfield collision-sampling dedekind <modulus> <slope>\n"
         "  nfield collision-sampling transform <modulus> <frequency>\n"
         "  nfield collision-sampling inverse <modulus> <frequency> <X>\n"
         "  nfield collision-sampling grid N q shift\n"
         "  nfield collision-sampling source N k Q\n"
         "  nfield collision-sampling decomposition prime H\n"
         "  nfield collision-sampling descent k c H\n"
         "  nfield collision-sampling prefix-word A B\n"
         "  nfield collision-sampling prefix-population first last\n"
         "  nfield collision-sampling stopped-cost modulus threshold\n"
         "  nfield collision-sampling fold A B u e Q L\n"
         "  nfield collision-sampling folded-source L Q K u e\n"
         "  nfield collision-sampling rectangle Q X Y parity\n"
         "  nfield collision-sampling cubic prime\n"
         "  nfield collision-sampling dedekind-mass modulus\n"
         "  nfield collision-sampling phase-sum gamma X beta first last\n"
         "  nfield collision-sampling completion N k Q weights\n"
         "  nfield collision-sampling kernel Q left right\n"
         "  nfield collision-sampling shells Q cutoff\n"
         "  nfield collision-sampling reciprocal left right numerator\n"
         "  nfield collision-sampling interior prime\n"
         "  nfield collision-sampling verify\n\n"
         "Exact GMP rational output. Odd primes 3..251, N=0..250.\n"
         "sampled alone accepts odd primes through 10007. Its E_p/p^2 is exact;\n"
         "the accompanying capacity and defect use long-double arithmetic.\n"
         "Correlation moduli 2..512; Dedekind moduli 1..63001.\n"
         "Inverse-series cutoffs 0..4096. Transform/cotangent values are\n"
         "long-double numerical evaluations; inverse prefixes and their\n"
         "absolute tail bound are exact. No libm rounding certificate is claimed.\n"
         "State and prefix cutoffs are explicit, with all endpoints retained.\n"
         "Grid: N=1..120, q=1..10000; rational shift in [0,1), denominator <=10000.\n"
         "Source/descent/prefix moduli <=512; fold u<=512, Q<=1000000, L<=10000.\n"
         "Folded source: L<=512, K=2..128; rectangle X,Y<=120 and parity\n"
         "Prefix population: 2<=first<=last<=512, words of length at least two,\n"
         "both determinant orientations. Wide ranges are best read locally.\n"
         "Stopped cost: modulus 2..512, threshold 1..modulus; every residue,\n"
         "including nonunits, with signed cyclic jumps and total variation.\n"
         "0=all, 1=odd moduli, 2=odd columns. Prefix B is signed.\n"
         "Decomposition retains small pairs, first cost, small remainders,\n"
         "stopped cost and terminal sum separately. H=1..prime-1.\n"
         "Phase sums use rational inputs, 2<=first<=last<=512 and first+beta>0.\n"
         "Completion uses k<=120 rational weights on residues 0..k-1, with weight 0 at 0.\n"
         "Kernel: indices 1..512; shells: cutoff 1..120. Q<=1000000 must be\n"
         "coprime to every used denominator. Reciprocal moduli <=10000;\n"
         "interior accepts primes 257..997 and displays a mean-zero witness.\n"
         "Selected carrier sets affect switching values; full_triangle and\n"
         "full_triangle_bridge always describe the complete carrier family.\n"
         "These are finite identities. Analytic damping and S_p -> 1 are not\n"
         "certified by their finite evaluation.");
}
int collision_sampling_command(int argc,char **argv)
{
    if(!argc || (argc==1 && (!strcmp(argv[0],"help") || !strcmp(argv[0],"--help")))) {
        collision_sampling_help(); return 0;
    }
    if(argc==1 && !strcmp(argv[0],"verify")) return !collision_sampling_verify();
    int source_status=collision_sampling_source_command(argc,argv);
    if(source_status>=0) {
        if(source_status)fputs("Signed-source inputs are outside the supported domain; see help collision-sampling.\n",stderr);
        return source_status;
    }
    unsigned p=0,k=0,x=0; int ok=0;
    if(argc<2 || !cs_uint(argv[1],&p)) goto bad;
    if(!strcmp(argv[0],"sampled") && argc==2) {
        mpq_t value;mpq_init(value);ok=collision_sampling_energy_q(value,p);
        if(ok) {
            CollisionTransition state={0};ok=collision_transition_init(&state,(int)p-1);
            if(ok) {
                char numerator[128],denominator[128];
                gmp_snprintf(numerator,sizeof numerator,"%Zd",mpq_numref(value));
                gmp_snprintf(denominator,sizeof denominator,"%Zd",mpq_denref(value));
                long double sample=strtold(numerator,NULL)/strtold(denominator,NULL);
                long double capacity=p-1-state.deficit[p-1];
                cs_print("sampled",value);
                printf("capacity_numerical=%.18Lg\ndefect_numerical=%.18Lg\n",capacity,capacity-sample);
                collision_transition_clear(&state);
            }
        }
        mpq_clear(value);
    } else if(!strcmp(argv[0],"inspect") && argc==2) {
        CollisionSampling z; collision_sampling_init(&z); ok=collision_sampling_q(&z,p);
        if(ok) for(unsigned i=0;i<CS_FIELD_COUNT;i++) cs_print(collision_sampling_names[i],z.value[i]);
        collision_sampling_clear(&z);
    } else if(!strcmp(argv[0],"poles") && argc==2) {
        CollisionPoles z; collision_poles_init(&z); ok=collision_sampling_poles_q(&z,p);
        if(ok) for(unsigned i=0;i<CSP_FIELD_COUNT;i++) cs_print(collision_poles_names[i],z.value[i]);
        collision_poles_clear(&z);
    } else if(!strcmp(argv[0],"switching") && (argc==2 || argc==4)) {
        unsigned char mask[COLLISION_SAMPLING_MAX_PRIME]={0};
        if(!cs_prime(p)) goto bad;
        if(argc==4) {
            if(strcmp(argv[2],"--carriers")) goto bad;
            const char *s=argv[3];
            if(!strcmp(s,"none")) s="";
            while(*s) {
                const char *end=strchr(s,','); size_t size=end?(size_t)(end-s):strlen(s);
                char token[16]; if(!size || size>=sizeof token) goto bad;
                memcpy(token,s,size); token[size]=0;
                if(!cs_uint(token,&k) || k<2 || k>=p-1 || mask[k]) goto bad;
                mask[k]=1; if(!end) break; s=end+1; if(!*s) goto bad;
            }
        }
        CollisionSwitching z; collision_switching_init(&z);
        ok=collision_sampling_switching_q(&z,p,argc==4?mask:NULL,argc==4?p:0);
        if(ok) for(unsigned i=0;i<CSS_FIELD_COUNT;i++) cs_print(collision_switching_names[i],z.value[i]);
        collision_switching_clear(&z);
    } else {
        mpq_t a,b,c,d; mpq_inits(a,b,c,d,NULL);
        if(argc==2 && !strcmp(argv[0],"capacity")) {
            ok=collision_sampling_capacity_q(a,p); if(ok) cs_print("capacity",a);
        } else if(argc>=3 && cs_uint(argv[2],&k)) {
            if(argc==3 && !strcmp(argv[0],"carrier")) {
                ok=collision_sampling_carrier_q(a,b,c,d,p,k);
                if(ok) {
                    cs_print("X",a); cs_print("reservoir",b); cs_print("alias_A",c); cs_print("alias_C",d);
                    int displacement=(int)((p*p)%k); if(2*displacement>(int)k) displacement-=(int)k;
                    printf("displacement=%d\n",displacement);
                }
            } else if(argc==3 && !strcmp(argv[0],"collar")) {
                ok=collision_sampling_collar_q(a,b,p,k);
                if(ok) { cs_print("absolute_mass",a); cs_print("signed_mass",b); }
            } else if(argc==3 && !strcmp(argv[0],"state")) {
                ok=collision_sampling_state_q(a,b,p,k,NULL,0);
                if(ok) { cs_print("burden",a); cs_print("fresh",b); }
            } else if(argc==3 && !strcmp(argv[0],"convolution")) {
                ok=collision_sampling_convolution_q(a,b,c,p,k);
                if(ok) { cs_print("primitive",a); cs_print("full",b); cs_print("elementary",c); }
            } else if(argc==3 && !strcmp(argv[0],"dedekind")) {
                ok=collision_sampling_dedekind_q(a,p,k); if(ok) cs_print("dedekind",a);
            } else if(argc==3 && !strcmp(argv[0],"transform")) {
                CollisionInverseTransform z; ok=collision_sampling_transform(&z,p,k);
                if(ok) {
                    printf("full_real=%.18Lg\nfull_imag=%.18Lg\nunit_real=%.18Lg\nunit_imag=%.18Lg\n",
                        creall(z.full),cimagl(z.full),creall(z.unit),cimagl(z.unit));
                    printf("inverse_series=%.18Lg\ninverse_from_descent=%.18Lg\nfull_error=%.6Lg\nunit_error=%.6Lg\ndescent_error=%.6Lg\n",
                        z.inverse_series,z.inverse_from_descent,z.full_error,z.unit_error,z.descent_error);
                }
            } else if(argc==4 && cs_uint(argv[3],&x)) {
                if(!strcmp(argv[0],"prefix")) {
                    ok=collision_sampling_prefix_q(a,p,k,x); if(ok) cs_print("prefix",a);
                } else if(!strcmp(argv[0],"correlation")) {
                    ok=collision_sampling_correlation_q(a,p,k,x); if(ok) cs_print("correlation",a);
                } else if(!strcmp(argv[0],"inverse")) {
                    ok=collision_sampling_inverse_q(a,b,c,p,k,x);
                    if(ok) { cs_print("prefix",a); cs_print("harmonic_prefix",b); cs_print("tail_bound",c); }
                }
            }
        }
        mpq_clears(a,b,c,d,NULL);
    }
    if(ok) return 0;
bad:
    fputs("Invalid collision-sampling action or parameters; see collision-sampling help.\n",stderr);
    return 1;
}
