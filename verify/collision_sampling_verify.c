#include "../src/collision_sampling.h"
#include <stdio.h>
#include <math.h>

static unsigned gcd(unsigned a,unsigned b)
{ while(b) { unsigned t=a%b; a=b; b=t; } return a; }
/* Independent defining finite sums, not the reciprocity/floor-sum algorithms
 * used in the library. No floating tolerance is involved in these checks. */
static void dedekind_direct(mpq_t out,unsigned q,unsigned h)
{
    long sum=0;
    for(unsigned a=1;a<q;a++) {
        unsigned r=(h*a)%q;
        if(r) sum+=(2L*a-q)*(2L*r-q);
    }
    mpq_set_si(out,sum,4UL*q*q); mpq_canonicalize(out);
}
static void capacity_direct(mpq_t out,unsigned n)
{
    mpq_set_ui(out,0,1); mpq_t t; mpq_init(t);
    for(unsigned r=1;r<=n;r++) for(unsigned s=1;s<=n;s++) {
        unsigned g=gcd(r,s); mpq_set_ui(t,g*g,3UL*r*s); mpq_canonicalize(t);
        mpq_add(out,out,t);
    }
    mpq_clear(t);
}
static void sample_direct(mpq_t out,unsigned p)
{
    unsigned m=p*p; unsigned long long total=0;
    for(unsigned a=0;a<m;a++) {
        long row=0;
        for(unsigned r=1;r<p;r++) {
            unsigned residue=(a*r)%m;
            if(residue) row+=2L*residue-m;
        }
        total+=(unsigned long long)(row*row);
    }
    mpq_set_ui(out,(unsigned long)total,(unsigned long)m*m*m); mpq_canonicalize(out);
}
int collision_sampling_verify(void)
{
    unsigned checks=0, failures=0;
#define CHECK(condition) do { checks++; if(!(condition)) { failures++; \
    fprintf(stderr,"collision-sampling check failed at line %d\n",__LINE__); } } while(0)
    mpq_t a,b,c,d,t,previous; mpq_inits(a,b,c,d,t,previous,NULL);
    for(unsigned q=1;q<=64;q++) for(unsigned h=0;h<q;h++) {
        CHECK(collision_sampling_dedekind_q(a,q,h)); dedekind_direct(b,q,h);
        CHECK(mpq_equal(a,b));
    }
    for(unsigned n=0;n<=50;n++) {
        CHECK(collision_sampling_capacity_q(a,n)); capacity_direct(b,n);
        CHECK(mpq_equal(a,b));
    }
    for(unsigned q=2;q<=48;q++) for(unsigned h=0;h<q;h++) {
        CollisionInverseTransform z;
        CHECK(collision_sampling_transform(&z,q,h));
        CHECK(z.full_error<1e-11L && z.unit_error<1e-11L && z.descent_error<1e-11L);
        CHECK(collision_sampling_inverse_q(a,b,c,q,h,3*q));
        CHECK(mpq_sgn(a)==0);
        CHECK(fabsl((long double)mpq_get_d(b)-z.inverse_series)<(long double)mpq_get_d(c)+1e-12L);
    }
    CollisionSampling s; collision_sampling_init(&s);
    CollisionPoles poles; collision_poles_init(&poles);
    CollisionSwitching v; collision_switching_init(&v);
    const unsigned primes[]={3,5,7,11,13,17,23,31,43,61,101,151,251};
    for(unsigned i=0;i<sizeof primes/sizeof *primes;i++) {
        unsigned p=primes[i]; CHECK(collision_sampling_q(&s,p));
        CHECK(mpq_sgn(s.value[CS_BRIDGE_ERROR])==0);
        CHECK(mpq_sgn(s.value[CS_ALIAS_ERROR])==0);
        if(p<=43) { sample_direct(a,p); CHECK(mpq_equal(a,s.value[CS_SAMPLED])); }
        CHECK(collision_sampling_poles_q(&poles,p));
        CHECK(mpq_sgn(poles.value[CSP_FOUR_WAY_ERROR])==0 && mpq_sgn(poles.value[CSP_ENERGY_ERROR])==0);
        CHECK(mpq_sgn(poles.value[CSP_RA])==0 && mpq_equal(poles.value[CSP_RK],s.value[CS_RESERVOIR]));
        mpq_set_ui(t,p*p,1); mpq_mul(a,t,s.value[CS_SAMPLED]);
        mpq_add(b,poles.value[CSP_DIAGONAL],poles.value[CSP_OFF_DIAGONAL]); CHECK(mpq_equal(a,b));
        CHECK(collision_sampling_collar_q(a,b,p,p/2));
        mpq_mul(b,b,t); mpq_add(b,b,s.value[CS_RESERVOIR]); CHECK(mpq_sgn(b)==0);
        if(p<=61) {
            CHECK(collision_sampling_switching_q(&v,p,NULL,0));
            CHECK(mpq_equal(v.value[CSS_RESERVOIR],v.value[CSS_DWELL_AREA]));
            CHECK(mpq_equal(v.value[CSS_RESERVOIR],v.value[CSS_FRESH_AREA]));
            CHECK(mpq_equal(v.value[CSS_RESERVOIR],v.value[CSS_TRIANGLE_BRIDGE]));
            CHECK(mpq_equal(v.value[CSS_ENERGY],v.value[CSS_INCREMENT_ENERGY]));
            mpq_sub(a,v.value[CSS_CHARGE],v.value[CSS_RELEASE]); mpq_add(a,a,a);
            CHECK(mpq_equal(a,v.value[CSS_ENERGY]));
            mpq_add(a,v.value[CSS_COHERENT_ENERGY],v.value[CSS_VARIANCE]);
            CHECK(mpq_equal(a,v.value[CSS_ENERGY]) && mpq_sgn(v.value[CSS_VARIANCE])>=0);
            mpq_set_ui(previous,0,1);
            for(unsigned x=2;x<p;x++) {
                CHECK(collision_sampling_state_q(a,b,p,x,NULL,0));
                mpq_sub(t,a,previous); CHECK(mpq_equal(t,b)); mpq_set(previous,a);
                CHECK(collision_sampling_convolution_q(a,c,d,p,x));
                if(x>=3) {
                    mpq_add(t,d,d); mpq_add(b,b,b); mpq_sub(t,t,b);
                    CHECK(mpq_equal(t,a));
                }
                mpq_set_ui(t,0,1);
                for(unsigned divisor=1;divisor<=x;divisor++) if(x%divisor==0) {
                    collision_sampling_convolution_q(a,b,d,p,divisor); mpq_add(t,t,a);
                }
                CHECK(mpq_equal(t,c));
            }
        }
    }
    mpq_set_si(a,-7,3); mpq_set(b,a);
    CHECK(!collision_sampling_capacity_q(a,251) && mpq_equal(a,b));
    CHECK(!collision_sampling_dedekind_q(a,0,1) && mpq_equal(a,b));
    CHECK(!collision_sampling_dedekind_q(a,63002,1) && mpq_equal(a,b));
    CHECK(!collision_sampling_carrier_q(a,a,c,d,7,3) && mpq_equal(a,b));
    CHECK(!collision_sampling_q(&s,9));
    CHECK(!collision_sampling_prefix_q(a,7,7,3) && mpq_equal(a,b));
    CHECK(!collision_sampling_correlation_q(a,7,7,1) && mpq_equal(a,b));
    unsigned char mask[7]={0,0,0,0,0,0,1};
    CHECK(!collision_sampling_switching_q(&v,7,mask,7));
    CHECK(!collision_sampling_state_q(a,b,7,0,NULL,0));
    collision_sampling_clear(&s); collision_switching_clear(&v);
    collision_poles_clear(&poles);
    mpq_clears(a,b,c,d,t,previous,NULL);
    printf("Collision sampling verification: %u checks, %u failures\n",checks,failures);
    puts("Exact rational defining sums, joined bridges, switching, convolution and endpoints.\n"
         "Finite evidence does not certify a uniform analytic estimate or the open sampling limit.");
    return failures==0;
#undef CHECK
}
