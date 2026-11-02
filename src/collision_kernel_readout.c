#include "collision_kernel_readout.h"
#include "weighted_remainder_exact.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <errno.h>

const char *const collision_kernel_seed_names[CK_COUNT]={
    "B0","B0_inverse","F_lower","F_upper","eta_lower","eta_upper",
    "selector_lower","selector_upper","zeta3_lower","zeta3_upper"
};
const char *const collision_measurement_names[CKM_COUNT]={
    "parent","left","right","defect","nonlocal_parent","nonlocal_left",
    "nonlocal_right","nonlocal_defect"
};
void collision_measurement_init(CollisionCarryMeasurement *out)
{ for(unsigned j=0;j<CKM_COUNT;j++)mpq_init(out->value[j]); }
void collision_measurement_clear(CollisionCarryMeasurement *out)
{ for(unsigned j=0;j<CKM_COUNT;j++)mpq_clear(out->value[j]); }
static int mu(unsigned n)
{
    int s=1;for(unsigned p=2;p<=n/p;p++) if(n%p==0) {
        n/=p;s=-s;if(n%p==0)return 0;
    }
    return n>1?-s:s;
}
static void scale(mpq_t out,const mpq_t in,long num,unsigned long den)
{
    mpq_t t;mpq_init(t);mpq_set_si(t,num,den);mpq_canonicalize(t);
    mpq_mul(out,in,t);mpq_clear(t);
}
static void harmonic(mpq_t out,unsigned n)
{
    mpq_t t;mpq_init(t);mpq_set_ui(out,0,1);
    for(unsigned k=1;k<=n;k++){mpq_set_ui(t,1,k);mpq_add(out,out,t);}
    mpq_clear(t);
}
static unsigned gcd(unsigned a,unsigned b)
{while(b){unsigned t=a%b;a=b;b=t;}return a;}
int collision_kernel_measurement_q(CollisionCarryMeasurement *out,unsigned m,
    unsigned a,unsigned b,unsigned power,const mpq_t amplitude)
{
    if(!out||m<3||m>127||m%2==0||power<2||power>12||power%2)return 0;
    a%=m;b%=m;unsigned c=(a+b)%m;
    if(gcd(a,m)!=1||gcd(b,m)!=1||gcd(c,m)!=1)return 0;
    CollisionCarryMeasurement z;collision_measurement_init(&z);
    mpq_t u,v,t,w,plus,minus;mpq_inits(u,v,t,w,plus,minus,NULL);
    unsigned pairs[3][2]={{a,b},{a,c},{c,b}};
    for(unsigned j=0;j<3;j++) {
        mpq_set_ui(plus,0,1);mpq_set_ui(minus,0,1);
        for(unsigned x=0;x<m;x++) {
            mpq_set_si(u,2L*(pairs[j][0]*x%m)-(m-1),2UL*m);mpq_canonicalize(u);mpq_mul(u,u,amplitude);
            mpq_set_si(v,2L*(pairs[j][1]*x%m)-(m-1),2UL*m);mpq_canonicalize(v);mpq_mul(v,v,amplitude);
            mpq_add(t,u,v);mpq_sub(w,u,v);
            mpq_mul(u,t,t);mpq_add(plus,plus,u);
            mpq_mul(v,w,w);mpq_add(minus,minus,v);
            for(unsigned k=2;k<power;k++){mpq_mul(u,u,t);mpq_mul(v,v,w);}
            mpq_sub(u,u,v);mpq_add(z.value[j],z.value[j],u);
        }
        scale(z.value[j],z.value[j],1,4UL*m);
        mpq_mul(plus,plus,plus);mpq_mul(minus,minus,minus);mpq_sub(t,plus,minus);
        scale(z.value[CKM_NONLOCAL_PARENT+j],t,1,4UL*m*m);
    }
    for(unsigned offset=0;offset<=4;offset+=4) {
        mpq_sub(z.value[offset+3],z.value[offset],z.value[offset+1]);
        mpq_sub(z.value[offset+3],z.value[offset+3],z.value[offset+2]);
    }
    for(unsigned j=0;j<CKM_COUNT;j++)mpq_set(out->value[j],z.value[j]);
    mpq_clears(u,v,t,w,plus,minus,NULL);collision_measurement_clear(&z);return 1;
}
void collision_kernel_seed_init(CollisionKernelSeed *out)
{ for(unsigned i=0;i<CK_COUNT;i++)mpq_init(out->value[i]); }
void collision_kernel_seed_clear(CollisionKernelSeed *out)
{ for(unsigned i=0;i<CK_COUNT;i++)mpq_clear(out->value[i]); }
static void seed_bounds(mpq_t low,mpq_t high,unsigned q,unsigned length)
{
    mpq_t t;mpq_init(t);mpq_set_ui(low,0,1);
    for(unsigned k=1;k<=length;k++) {
        harmonic(t,q*k-1);scale(t,t,1,(unsigned long)q*q*k*k);mpq_add(low,low,t);
    }
    harmonic(t,q*length);mpq_set_ui(high,1,1);mpq_add(t,t,high);
    scale(t,t,1,(unsigned long)q*q*length);mpq_add(high,low,t);mpq_clear(t);
}
int collision_kernel_seed_q(CollisionKernelSeed *out,unsigned q,unsigned length)
{
    if(!out||q<1||q>240||length<1||length>240/q)return 0;
    CollisionKernelSeed z;collision_kernel_seed_init(&z);
    mpq_t low,high,nlo,nhi,delta,t,u,dlo,dhi;mpq_inits(low,high,nlo,nhi,delta,t,u,dlo,dhi,NULL);
    harmonic(t,q-1);scale(z.value[CK_B0],t,1,(unsigned long)q*q);
    for(unsigned d=1;d<=q;d++)if(q%d==0) {
        weighted_remainder_weight_q(t,q/d);scale(t,t,1,(unsigned long)d*d*d);
        mpq_add(z.value[CK_B0_INVERSE],z.value[CK_B0_INVERSE],t);
    }
    seed_bounds(z.value[CK_F_LOWER],z.value[CK_F_UPPER],q,length);
    for(unsigned k=1;k<=length;k++) {
        weighted_remainder_weight_q(t,q*k);mpq_add(z.value[CK_ETA_LOWER],z.value[CK_ETA_LOWER],t);
        mpq_set_ui(t,1,(unsigned long)k*k*k);mpq_add(z.value[CK_ZETA_LOWER],z.value[CK_ZETA_LOWER],t);
    }
    mpq_sub(t,z.value[CK_F_UPPER],z.value[CK_F_LOWER]);
    mpq_add(z.value[CK_ETA_UPPER],z.value[CK_ETA_LOWER],t);
    mpq_set_ui(t,1,2UL*length*length);mpq_add(z.value[CK_ZETA_UPPER],z.value[CK_ZETA_LOWER],t);
    mpq_set_ui(delta,1,1);unsigned remaining=q;
    for(unsigned p=2;p<=remaining;p++)if(remaining%p==0) {
        mpq_set_ui(t,(unsigned long)p*p*p-1,(unsigned long)p*p*p);mpq_canonicalize(t);
        mpq_mul(delta,delta,t);while(remaining%p==0)remaining/=p;
    }
    for(unsigned d=1;d<=q;d++)if(q%d==0&&mu(d)) {
        seed_bounds(low,high,q/d,length);
        scale(low,low,mu(d),(unsigned long)d*d*d);
        scale(high,high,mu(d),(unsigned long)d*d*d);
        mpq_add(nlo,nlo,mu(d)>0?low:high);mpq_add(nhi,nhi,mu(d)>0?high:low);
    }
    mpq_mul(dlo,delta,z.value[CK_ZETA_LOWER]);mpq_mul(dhi,delta,z.value[CK_ZETA_UPPER]);
    mpq_div(z.value[CK_SELECTOR_LOWER],nlo,mpq_sgn(nlo)>=0?dhi:dlo);
    mpq_div(z.value[CK_SELECTOR_UPPER],nhi,mpq_sgn(nhi)>=0?dlo:dhi);
    for(unsigned i=0;i<CK_COUNT;i++)mpq_set(out->value[i],z.value[i]);
    mpq_clears(low,high,nlo,nhi,delta,t,u,dlo,dhi,NULL);collision_kernel_seed_clear(&z);return 1;
}
static void profile_row(mpq_t row,mpq_t grid,const mpq_t lambda,
                        const mpq_t *coeff,unsigned length,unsigned n)
{
    mpq_t t,h,u;mpq_inits(t,h,u,NULL);mpq_set_ui(grid,0,1);
    for(unsigned a=1;a<n;a++) {
        mpq_set_ui(t,(unsigned long)a*(n-a),(unsigned long)n*n);mpq_canonicalize(t);
        mpq_set_ui(h,0,1);
        for(unsigned j=length;j>0;j--) {mpq_mul(h,h,t);mpq_add(h,h,coeff[j-1]);}
        mpq_add(grid,grid,h);
    }
    harmonic(h,n-1);mpq_mul(h,h,lambda);scale(h,h,1,(unsigned long)n*n);
    scale(u,grid,1,(unsigned long)n*n*n);mpq_add(row,h,u);
    mpq_clears(t,h,u,NULL);
}
int collision_kernel_profile_q(mpq_t primitive,mpq_t row,mpq_t grid,
    const mpq_t lambda,const mpq_t *coeff,unsigned length,unsigned n)
{
    if(n<1||n>120||length>9||(length&&!coeff)||primitive==row||primitive==grid||row==grid)return 0;
    mpq_t p,r,s,t,u;mpq_inits(p,r,s,t,u,NULL);
    profile_row(r,s,lambda,coeff,length,n);
    for(unsigned d=1;d<=n;d++)if(n%d==0&&mu(d)) {
        profile_row(t,u,lambda,coeff,length,n/d);scale(t,t,mu(d),(unsigned long)d*d*d);mpq_add(p,p,t);
    }
    mpq_set(primitive,p);mpq_set(row,r);mpq_set(grid,s);
    mpq_clears(p,r,s,t,u,NULL);return 1;
}
static int number(const char *s,unsigned *out)
{
    if(!s||!*s)return 0;
    for(const char *c=s;*c;c++)if(*c<'0'||*c>'9')return 0;
    errno=0;char *end;unsigned long x=strtoul(s,&end,10);if(errno||*end||x>UINT_MAX)return 0;
    *out=(unsigned)x;return 1;
}
static int rational(mpq_t out,const char *s)
{
    if(!s||!*s||strlen(s)>80)return 0;
    const char *c=s;if(*c=='-')c++;if(!*c)return 0;
    unsigned digits=0;while(*c>='0'&&*c<='9'){digits++;c++;}if(!digits)return 0;
    if(*c=='/') {c++;digits=0;while(*c>='0'&&*c<='9'){digits++;c++;}if(!digits)return 0;}
    if(*c||mpq_set_str(out,s,10)||mpz_sgn(mpq_denref(out))==0)return 0;
    mpq_canonicalize(out);return 1;
}
int collision_kernel_readout_command(int argc,char **argv)
{
    unsigned n,length;int ok=0;
    if(argc==6&&!strcmp(argv[0],"measurement")) {
        unsigned a,b,power;mpq_t amplitude;mpq_init(amplitude);
        CollisionCarryMeasurement z;collision_measurement_init(&z);
        ok=number(argv[1],&n)&&number(argv[2],&a)&&number(argv[3],&b)&&
           number(argv[4],&power)&&rational(amplitude,argv[5])&&
           collision_kernel_measurement_q(&z,n,a,b,power,amplitude);
        if(ok)for(unsigned j=0;j<CKM_COUNT;j++)gmp_printf("%s=%Qd\n",collision_measurement_names[j],z.value[j]);
        mpq_clear(amplitude);collision_measurement_clear(&z);
    } else if(argc==3&&!strcmp(argv[0],"seed")&&number(argv[1],&n)&&number(argv[2],&length)) {
        CollisionKernelSeed z;collision_kernel_seed_init(&z);ok=collision_kernel_seed_q(&z,n,length);
        if(ok)for(unsigned i=0;i<CK_COUNT;i++)gmp_printf("%s=%Qd\n",collision_kernel_seed_names[i],z.value[i]);
        collision_kernel_seed_clear(&z);
    } else if(argc==4&&!strcmp(argv[0],"profile")&&number(argv[1],&n)) {
        mpq_t lambda,coeff[9],p,r,s;mpq_inits(lambda,p,r,s,NULL);for(unsigned j=0;j<9;j++)mpq_init(coeff[j]);
        length=0;ok=rational(lambda,argv[2]);const char *c=argv[3];
        if(!strcmp(c,"none"))c="";
        else if(!*c)ok=0;
        while(ok&&*c) {
            const char *end=strchr(c,',');size_t count=end?(size_t)(end-c):strlen(c);char token[81];
            if(!count||count>=sizeof token||length==9){ok=0;break;}
            memcpy(token,c,count);token[count]=0;ok=rational(coeff[length++],token);
            if(!end)break;
            c=end+1;if(!*c)ok=0;
        }
        if(ok)ok=collision_kernel_profile_q(p,r,s,lambda,coeff,length,n);
        if(ok)gmp_printf("primitive=%Qd\nrow=%Qd\ngrid_sum=%Qd\n",p,r,s);
        mpq_clears(lambda,p,r,s,NULL);for(unsigned j=0;j<9;j++)mpq_clear(coeff[j]);
    } else if(argc==3&&!strcmp(argv[0],"lattice")&&number(argv[2],&n)) {
        mpq_t x,lo,hi,reciprocal;mpq_inits(x,lo,hi,reciprocal,NULL);
        ok=rational(x,argv[1])&&collision_kernel_lattice_q(lo,hi,reciprocal,x,n);
        if(ok)gmp_printf("prefix=%Qd\nupper=%Qd\nreciprocal_prefix=%Qd\n",lo,hi,reciprocal);
        mpq_clears(x,lo,hi,reciprocal,NULL);
    }
    if(!ok)fputs("Invalid measurement/seed/profile/lattice parameters; see capacity-generation help.\n",stderr);
    return ok?0:1;
}

int collision_kernel_lattice_q(mpq_t prefix,mpq_t upper,mpq_t reciprocal,
    const mpq_t x,unsigned cutoff)
{
    if(!cutoff||cutoff>64||mpq_sgn(x)<=0||prefix==upper||prefix==reciprocal||upper==reciprocal)return 0;
    mpq_t lo,hi,rec,t,u,inv;mpq_inits(lo,hi,rec,t,u,inv,NULL);mpq_inv(inv,x);
    for(unsigned m=1;m<=cutoff;m++)for(unsigned n=1;n<=cutoff;n++) {
        scale(t,x,m,1);mpq_set_ui(u,n,1);mpq_add(t,t,u);scale(t,t,(long)m*n,1);
        mpq_inv(t,t);mpq_add(lo,lo,t);
        scale(t,inv,m,1);mpq_add(t,t,u);scale(t,t,(long)m*n,1);
        mpq_inv(t,t);mpq_add(rec,rec,t);
    }
    harmonic(t,cutoff);mpq_set_ui(u,1,1);mpq_add(t,t,u);scale(t,t,2,cutoff);
    if(mpq_cmp_ui(x,1,1)<0)mpq_div(t,t,x);
    mpq_add(hi,lo,t);
    mpq_set(prefix,lo);mpq_set(upper,hi);mpq_set(reciprocal,rec);
    mpq_clears(lo,hi,rec,t,u,inv,NULL);return 1;
}
