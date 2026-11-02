#include "../src/collision_capacity_generation.h"
#include "../src/weighted_remainder_exact.h"
#include "../src/collision_kernel_readout.h"
#include <stdio.h>

static unsigned gcd_v(unsigned a,unsigned b)
{while(b){unsigned t=a%b;a=b;b=t;}return a;}
static int kernel_readout_verify(void)
{
    unsigned checks=0,fail=0;
    mpq_t p,r,g,l,t,u,h,c[3];mpq_inits(p,r,g,l,t,u,h,NULL);
    for(unsigned j=0;j<3;j++)mpq_init(c[j]);
    mpq_set_ui(l,1,1);
    for(unsigned n=1;n<=120;n++) {
        checks++;
        if(!collision_kernel_profile_q(p,r,g,l,NULL,0,n)||
           !weighted_remainder_weight_q(t,n)||mpq_cmp(p,t)||mpq_sgn(g))fail++;
    }
    mpq_set_si(l,3,2);mpq_set_si(c[0],-5,3);mpq_set_ui(c[1],7,4);mpq_set_si(c[2],-1,2);
    for(unsigned n=2;n<=64;n++) {
        collision_kernel_profile_q(p,r,g,l,c,3,n);mpq_set_ui(h,0,1);
        /* Independently sum the primitive kernel at its original addresses. */
        for(unsigned a=1;a<n;a++)if(gcd_v(a,n)==1) {
            mpq_set_ui(t,(unsigned long)a*(n-a),(unsigned long)n*n);mpq_canonicalize(t);
            mpq_set(u,c[2]);mpq_mul(u,u,t);mpq_add(u,u,c[1]);
            mpq_mul(u,u,t);mpq_add(u,u,c[0]);
            mpq_set_ui(t,1,(unsigned long)n*n*n);mpq_mul(u,u,t);
            mpq_set_ui(t,1,2UL*a*(n-a)*n);mpq_mul(t,t,l);mpq_add(t,t,u);mpq_add(h,h,t);
        }
        checks++;if(mpq_cmp(p,h))fail++;
    }
    CollisionKernelSeed seed;collision_kernel_seed_init(&seed);
    for(unsigned q=1;q<=40;q++) {
        checks++;
        if(!collision_kernel_seed_q(&seed,q,240/q)||
           mpq_cmp(seed.value[CK_B0],seed.value[CK_B0_INVERSE])||
           mpq_cmp(seed.value[CK_F_LOWER],seed.value[CK_F_UPPER])>0||
           mpq_cmp(seed.value[CK_SELECTOR_LOWER],seed.value[CK_ETA_UPPER])>0||
           mpq_cmp(seed.value[CK_SELECTOR_UPPER],seed.value[CK_ETA_LOWER])<0)fail++;
    }
    collision_kernel_seed_clear(&seed);
    CollisionCarryMeasurement measurement;collision_measurement_init(&measurement);
    mpq_set_si(l,-3,2);
    for(unsigned m=3;m<=53;m+=2) {
        checks++;
        if(!collision_kernel_measurement_q(&measurement,m,1,1,2,l)||
           mpq_sgn(measurement.value[CKM_DEFECT])||mpq_sgn(measurement.value[CKM_NONLOCAL_DEFECT]))fail++;
    }
    checks++;
    if(!collision_kernel_measurement_q(&measurement,5,1,1,4,l)||
       !mpq_sgn(measurement.value[CKM_DEFECT])||mpq_sgn(measurement.value[CKM_NONLOCAL_DEFECT]))fail++;
    collision_measurement_clear(&measurement);
    for(unsigned den=1;den<=5;den++)for(unsigned num=1;num<=7;num++) {
        mpq_set_ui(l,num,den);mpq_canonicalize(l);checks++;
        if(!collision_kernel_lattice_q(p,r,g,l,12)) {fail++;continue;}
        mpq_mul(t,p,l);if(mpq_cmp(t,g)||mpq_cmp(p,r)>0)fail++;
    }
    for(unsigned j=0;j<3;j++)mpq_clear(c[j]);
    mpq_clears(p,r,g,l,t,u,h,NULL);
    printf("capacity-generation kernel readouts: %u exact finite cases, %u failures\n",checks,fail);
    return fail==0;
}
int collision_capacity_generation_verify(void)
{
    mpq_t x,y,p,l,r,d,t,w;mpq_inits(x,y,p,l,r,d,t,w,NULL);
    unsigned checks=0,fail=0;
    for(unsigned base=2;base<=12;base++)for(unsigned lag=1;lag<=3;lag++){
        unsigned q=1;for(unsigned j=0;j<lag;j++)q*=base;
        unsigned m=base*q;if(m>4096)continue;
        for(unsigned a=0;a<m;a++){
            checks++;if(!collision_generation_source_q(x,y,base,lag,a)||mpq_cmp(x,y))fail++;
        }
    }
    for(unsigned m=3;m<=31;m+=2)for(unsigned a=1;a<m;a++)for(unsigned b=1;b<m;b++)
      if(gcd_v(a,m)==1&&gcd_v(b,m)==1&&gcd_v(a+b,m)==1){
        checks++;if(!collision_generation_carry_q(x,y,p,l,r,d,m,a,b)){fail++;continue;}
        mpq_set_ui(t,3,1);mpq_mul(t,t,x);if(mpq_cmp(y,t))fail++;
        mpq_add(t,l,r);if(mpq_cmp(p,t))fail++;
        mpq_set_ui(t,m-1,4UL*m*m);mpq_canonicalize(t);if(mpq_cmp(d,t))fail++;
      }
    for(unsigned n=1;n<=120;n++){
        checks++;collision_generation_recover_q(x,n);weighted_remainder_weight_q(y,n);
        if(mpq_cmp(x,y))fail++;
    }
    /* The origin/current tests retain coefficients of each formal prime log. */
    for(unsigned n=1;n<=48;n++)for(unsigned prime=2;prime<=n;prime++){
        int isprime=1;for(unsigned v=2;v<prime;v++)if(prime%v==0)isprime=0;
        if(!isprime)continue;
        checks++;collision_generation_current_q(x,n,prime,0,0);
        unsigned v=n;while(v%prime==0)v/=prime;
        mpq_set_ui(y,v==1,1);if(mpq_cmp(x,y))fail++;
    }
    collision_generation_current_q(x,6,2,7,11);
    mpq_set_ui(y,147,5324);if(mpq_cmp(x,y))fail++;
    collision_generation_current_q(x,6,3,7,11);if(mpq_cmp(x,y))fail++;checks+=2;
    /* Invalid-input preservation of the public exact APIs. */
    mpq_set_si(x,7,9);mpq_set(y,x);
    if(collision_generation_source_q(x,x,5,1,1)||mpq_cmp(x,y))fail++;
    if(collision_generation_recover_q(x,121)||mpq_cmp(x,y))fail++;
    if(collision_generation_current_q(x,5,4,0,0)||mpq_cmp(x,y))fail++;
    if(collision_generation_control_q(x,p,l,7,9,2)||mpq_cmp(x,y))fail++;
    checks+=4;
    mpq_clears(x,y,p,l,r,d,t,w,NULL);
    printf("capacity-generation: %u exact finite cases, %u failures\n",checks,fail);
    puts("Scope: finite source, carry, endpoint, capacity inverse and signed coefficients.");
    puts("All-amplitude selection and infinite analytic conclusions require the written proofs.");
    int kernel_ok=kernel_readout_verify();
    return fail==0&&kernel_ok;
}
