/* Exact native carries, tapered sources and finite moving-field work. */
#include "native_arithmetic.h"
#include <mpfr.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void nq(mpq_t z,long a,unsigned long b)
{ mpq_set_si(z,a,b);mpq_canonicalize(z); }
static void ns(mpq_t z,const mpq_t x,long a,unsigned long b)
{ mpq_t t;mpq_init(t);nq(t,a,b);mpq_mul(z,x,t);mpq_clear(t); }
static void np(const char *name,const mpq_t z) { gmp_printf("%s=%Qd\n",name,z); }
static mpq_t *nv(unsigned n)
{ mpq_t *v=calloc(n,sizeof *v);if(v)for(unsigned i=0;i<n;++i)mpq_init(v[i]);return v; }
static void nf(mpq_t *v,unsigned n)
{ if(v) { for(unsigned i=0;i<n;++i)mpq_clear(v[i]);free(v); } }
static int nu(const char *s,unsigned *n)
{
    if(!s||!*s)return 0;
    for(const char *p=s;*p;++p)if(*p<'0'||*p>'9')return 0;
    errno=0;char *end;unsigned long v=strtoul(s,&end,10);if(errno||*end||v>1000000)return 0;*n=(unsigned)v;return 1;
}
static int nr(const char *s,mpq_t q)
{
    if(!s||!*s||strlen(s)>160)return 0;
    const char *p=s;if(*p=='-')++p;int digits=0,slash=0;
    for(;*p;++p) { if(*p>='0'&&*p<='9') { ++digits;continue; }if(*p=='/'&&digits&&!slash) { slash=1;digits=0;continue; }return 0; }
    if(!digits||mpq_set_str(q,s,10)||mpz_sgn(mpq_denref(q))<=0)return 0;
    if(mpz_sizeinbase(mpq_numref(q),2)>256||mpz_sizeinbase(mpq_denref(q),2)>256)return 0;
    mpq_canonicalize(q);return 1;
}
static int nm(unsigned n)
{ int sign=1;for(unsigned p=2;p<=n/p;++p)if(n%p==0) { n/=p;sign=-sign;if(n%p==0)return 0;while(n%p==0)n/=p; }return n>1?-sign:sign; }
static unsigned nj(unsigned n)
{ unsigned out=n*n;for(unsigned p=2;p<=n/p;++p)if(n%p==0) { out=out/(p*p)*(p*p-1);while(n%p==0)n/=p; }if(n>1)out=out/(n*n)*(n*n-1);return out; }
static void taper(mpq_t z,unsigned S,unsigned j)
{ if(j<=S)nq(z,1,1);else if(j>=2*S)nq(z,0,1);else nq(z,2*S-j,S); }
/* r=0 selects the joined Mobius profile. Positive r selects one odd core. */
static int divisor_coeff(mpq_t *out,unsigned S,unsigned r)
{
    mpq_t previous,current,A,B,C,t;mpq_inits(previous,current,A,B,C,t,NULL);
    for(unsigned j=1;j<=2*S;++j) {
        if(r) {
            if(j>=r&&j<2*r)nq(current,1,r);
            else if(j>=2*r&&j<4*r)nq(current,-1,r);
            else if(j>=4*r&&j<8*r)nq(current,1,4*r);
            else nq(current,0,1);
        } else {
            nq(t,nm(j),j);mpq_add(A,A,t);
            if(j%2==0) { nq(t,nm(j/2),j/2);mpq_add(B,B,t); }
            if(j%4==0) { nq(t,nm(j/4),j/4);mpq_add(C,C,t); }
            ns(current,B,-3,2);mpq_add(current,current,A);ns(t,C,1,2);mpq_add(current,current,t);
        }
        taper(t,S,j);mpq_mul(current,current,t);mpq_sub(out[j],current,previous);ns(out[j],out[j],j,1);mpq_set(previous,current);
    }
    mpq_clears(previous,current,A,B,C,t,NULL);return 1;
}
static void readings(mpq_t *values,unsigned N,mpq_t *coeff,unsigned top)
{
    /* Reciprocal neutrality turns each unit increment into a divisor sum. */
    for(unsigned j=1;j<=top;++j)for(unsigned n=j;n<=N;n+=j)mpq_sub(values[n],values[n],coeff[j]);
    for(unsigned n=1;n<=N;++n)mpq_add(values[n],values[n],values[n-1]);
}
int native_packet_coefficients(mpq_t *out,unsigned capacity,unsigned t)
{
    if(!out||t<2||t>128||capacity<=8*t)return 0;
    mpq_t *coeff=nv(8*t+1);if(!coeff)return 0;
    mpq_t A,previous,current,tau,x;mpq_inits(A,previous,current,tau,x,NULL);
    const unsigned ss[]={2*t,t,4*t},copy[]={2,4,1};const int weight[]={3,-2,-1};
    for(unsigned i=0;i<3;++i) {
        nq(A,1,1);nq(previous,1,1);
        for(unsigned j=2;j<=2*ss[i];++j) {
            nq(x,nm(j),j);mpq_add(A,A,x);taper(tau,ss[i],j);mpq_mul(current,A,tau);
            mpq_sub(x,current,previous);ns(x,x,-(long)j*weight[i],1);
            mpq_add(coeff[copy[i]*j],coeff[copy[i]*j],x);
            if(copy[i]>1) { ns(x,x,1,j);mpq_sub(coeff[copy[i]],coeff[copy[i]],x); }
            mpq_set(previous,current);
        }
    }
    for(unsigned j=0;j<=8*t;++j)mpq_set(out[j],coeff[j]);
    mpq_clears(A,previous,current,tau,x,NULL);nf(coeff,8*t+1);return 1;
}
static int carry(unsigned j,unsigned n,const char *bases)
{
    unsigned radix[16],count=0;const char *p=bases;
    while(*p) {
        const char *comma=strchr(p,',');size_t size=comma?(size_t)(comma-p):strlen(p);char word[16];
        if(!size||size>=sizeof word||count==16)return 1;
        memcpy(word,p,size);word[size]=0;
        if(!nu(word,&radix[count])||radix[count]<2||radix[count]>36)return 1;
        ++count;if(!comma)break;
        p=comma+1;if(!*p)return 1;
    }
    if(!count||j<1||j>10000)return 1;
    mpz_t B,m,next,z,c;mpz_inits(B,m,next,z,c,NULL);mpz_set_ui(B,1);mpz_set_ui(z,n);mpz_cdiv_q_ui(m,z,j);
    mpq_t eta0,eta,sum,t,error;mpq_inits(eta0,eta,sum,t,error,NULL);mpq_set_z(eta0,m);nq(t,n,j);mpq_sub(eta0,eta0,t);
    for(unsigned i=0;i<count;++i) {
        mpz_mul_ui(B,B,radix[i]);mpz_mul_ui(z,B,n);mpz_cdiv_q_ui(next,z,j);mpz_mul_ui(c,m,radix[i]);mpz_sub(c,c,next);
        mpq_set_z(t,c);mpz_set(mpq_denref(t),B);mpq_canonicalize(t);mpq_add(sum,sum,t);
        gmp_printf("step=%u radix=%u scale=%Zd carry=%Zd\n",i+1,radix[i],B,c);mpz_set(m,next);
    }
    mpq_set_z(eta,m);mpq_set_z(t,z);mpz_mul_ui(mpq_denref(t),mpq_denref(t),j);mpq_canonicalize(t);mpq_sub(eta,eta,t);
    mpq_set_z(t,B);mpq_div(eta,eta,t);mpq_add(error,sum,eta);mpq_sub(error,error,eta0);
    np("initial_ceiling_gap",eta0);np("carry_sum",sum);np("terminal_gap",eta);np("identity_error",error);
    int failed=mpq_sgn(error)!=0;mpz_clears(B,m,next,z,c,NULL);mpq_clears(eta0,eta,sum,t,error,NULL);return failed;
}
static int polarity(unsigned b,unsigned n)
{ unsigned h=n/(b*b),u=(n/b)%b,v=n%b;return ((h+u+v)/(b-1))%2?-1:1; }
static void completed(mpq_t out,unsigned m,unsigned n)
{ static const int h[]={0,-1,2,1,-1,-2,1,0};nq(out,h[(n/m)%8],1); }
static void later(mpq_t out,unsigned S,unsigned r,unsigned n)
{ if(n<r)nq(out,0,1);else nq(out,(long)n*(n+1)+(long)r*(r-1)-4L*S*r,2UL*S*r); }
static int divisor_work(unsigned t,unsigned N,int parent_only)
{
    unsigned S=4*t;if(!t||t>128||N<2*S||N>10000)return 1;
    mpq_t *old=nv(2*S+1),*child=nv(4*S+1),*p=nv(N+1),*q=nv(N+1),*Z=nv(2*S+1),*v=nv(2*S+1);
    if(!old||!child||!p||!q||!Z||!v) { nf(old,2*S+1);nf(child,4*S+1);nf(p,N+1);nf(q,N+1);nf(Z,2*S+1);nf(v,2*S+1);return 1; }
    divisor_coeff(old,S,0);divisor_coeff(child,2*S,0);readings(p,N,old,2*S);readings(q,N,child,4*S);
    mpq_t shell,work,cross,fresh,reset,endpoint,head,low,high,zenergy,diagonal,retained,credit,reading_bound;
    mpq_t x,y,z,u,a[4],den,response,sum,prev,g,J;
    mpq_inits(shell,work,cross,fresh,reset,endpoint,head,low,high,zenergy,diagonal,retained,credit,reading_bound,x,y,z,u,den,response,sum,prev,g,J,NULL);
    for(unsigned i=0;i<4;++i)mpq_init(a[i]);
    for(unsigned m=1;m<=S/8;m+=2)if(nm(m)) {
        unsigned L=8*m*(2*S/(8*m));
        for(unsigned n=L+1;n<=2*S;++n) { completed(x,m,n);ns(y,x,nm(m),1);mpq_add(Z[n],Z[n],y);mpq_mul(y,x,x);ns(y,y,1,(unsigned long)n*(n+1));mpq_add(diagonal,diagonal,y); }
    }
    for(unsigned n=S+1;n<=N;++n) {
        mpq_mul(x,p[n],p[n]);
        if(n<=2*S) { ns(x,x,1,(unsigned long)n*(n+1));mpq_add(shell,shell,x); }
        else {
            mpq_sub(y,q[n],p[n]);mpq_mul(x,p[n],y);ns(x,x,2,(unsigned long)n*(n+1));mpq_add(cross,cross,x);
            mpq_mul(x,y,y);ns(x,x,1,(unsigned long)n*(n+1));mpq_add(fresh,fresh,x);
        }
        if(n<=2*S) {
            mpq_mul(x,Z[n],Z[n]);ns(x,x,1,(unsigned long)n*(n+1));mpq_add(zenergy,zenergy,x);
            mpq_sub(v[n],p[n],Z[n]);mpq_mul(x,v[n],v[n]);ns(x,x,1,(unsigned long)n*(n+1));mpq_add(retained,retained,x);
        }
    }
    mpq_add(head,cross,fresh);mpq_sub(head,head,shell);
    /* Exact boundary decomposition of the joined work g=q^2-p^2. */
    mpq_mul(prev,q[2*S],q[2*S]);mpq_mul(x,p[2*S],p[2*S]);mpq_sub(prev,prev,x);ns(endpoint,prev,1,2*S+1);
    for(unsigned n=2*S+1;n<=N;++n) { mpq_mul(g,q[n],q[n]);mpq_mul(x,p[n],p[n]);mpq_sub(g,g,x);mpq_sub(J,g,prev);ns(x,J,1,n);mpq_add(reset,reset,x);mpq_set(prev,g); }
    ns(x,prev,1,N+1);mpq_sub(endpoint,endpoint,x);mpq_add(work,endpoint,reset);mpq_sub(work,work,shell);
    nq(x,36L*S*S,N+1);mpq_sub(low,head,x);nq(x,144L*S*S,N+1);mpq_add(high,head,x);
    mpq_sub(credit,zenergy,retained);
    for(unsigned start=S+1;start+3<=2*S;start+=4) {
        unsigned r=start+2;later(a[2],S,r,r+1);later(a[3],S,r,r);mpq_neg(a[3],a[3]);
        ns(x,a[2],(long)(start+2)*(start+3)-(long)start*(start+1),1);ns(y,a[3],(long)(start+3)*(start+4)-(long)start*(start+1),1);mpq_add(x,x,y);ns(a[1],x,-1,2*(start+1));
        mpq_add(a[0],a[1],a[2]);mpq_add(a[0],a[0],a[3]);mpq_neg(a[0],a[0]);nq(den,0,1);nq(response,0,1);
        for(unsigned i=0;i<4;++i) { mpq_mul(x,a[i],v[start+i]);mpq_add(response,response,x);mpq_mul(x,a[i],a[i]);ns(x,x,(long)(start+i)*(start+i+1),1);mpq_add(den,den,x); }
        mpq_mul(x,response,response);mpq_div(x,x,den);mpq_add(reading_bound,reading_bound,x);
    }
    int failed=!mpq_equal(head,work)||mpq_cmp(reading_bound,retained)>0||mpq_cmp_ui(diagonal,1,4)>=0;
    if(!failed) {
        printf("scale=%u\nparent_cutoff=%u\nobservation_cutoff=%u\n",t,S,N);
        np("parent_shell_energy",shell);np("fragment_energy",zenergy);np("fragment_diagonal",diagonal);np("retained_energy",retained);np("parent_credit",credit);np("four_reading_lower",reading_bound);mpq_sub(x,zenergy,diagonal);np("fragment_excess",x);
        if(!parent_only) { np("signed_old_new_work",cross);np("new_field_energy",fresh);np("finite_head",head);np("reset_head",work);np("reset_sum",reset);np("boundary_terms",endpoint);np("complete_change_lower",low);np("complete_change_upper",high);puts("The enclosure retains the whole omitted tail; a finite value is not a uniform growth bound."); }
    }
    for(unsigned i=0;i<4;++i)mpq_clear(a[i]);
    mpq_clears(shell,work,cross,fresh,reset,endpoint,head,low,high,zenergy,diagonal,retained,credit,reading_bound,x,y,z,u,den,response,sum,prev,g,J,NULL);
    nf(old,2*S+1);nf(child,4*S+1);nf(p,N+1);nf(q,N+1);nf(Z,2*S+1);nf(v,2*S+1);return failed;
}
void native_arithmetic_help(void)
{
    puts("  nfield native-refinement carry denominator address bases\n"
         "  nfield native-refinement detail cutoff\n"
         "  nfield native-refinement polarity base address\n"
         "  nfield native-refinement stable-correction response cost error\n"
         "  nfield native-refinement divisor-family scale odd-core address\n"
         "  nfield native-refinement divisor-work scale cutoff\n"
         "  nfield native-refinement parent-credit scale\n\n"
         "Carry bases: comma-separated 2..36, at most 16; denominator <=10000.\n"
         "Detail cutoff 2..512; polarity base 2..36, address <=1000000.\n"
         "Stable correction accepts nonnegative rational response/error and positive cost.\n"
         "Its gain is conditional on those input bounds holding for the readings.\n"
         "Divisor scale 1..128, odd core <=16*scale, address <=10000.\n"
         "Work cutoff 8*scale..10000; exact finite work plus a complete tail enclosure.\n"
         "Parent credit includes restored fragments and the four-reading lower bound.");
}
int native_arithmetic_command(int argc,char **argv)
{
    if(!argc)return -1;
    const char *op=argv[0];
    int known=!strcmp(op,"carry")||!strcmp(op,"detail")||!strcmp(op,"polarity")||!strcmp(op,"stable-correction")||!strcmp(op,"divisor-family")||!strcmp(op,"divisor-work")||!strcmp(op,"parent-credit");
    if(!known)return -1;
    if(!strcmp(op,"stable-correction")&&argc==4) {
        mpq_t R,C,E,x,g;mpq_inits(R,C,E,x,g,NULL);int ok=nr(argv[1],R)&&nr(argv[2],C)&&nr(argv[3],E)&&mpq_sgn(R)>=0&&mpq_sgn(C)>0&&mpq_sgn(E)>=0;
        if(ok) { if(mpq_cmp(R,E)>0) { mpq_sub(g,R,E);mpq_div(x,g,R);mpq_div(x,x,C);mpq_mul(g,g,g);mpq_div(g,g,C); }np("step_size",x);np("guaranteed_gain",g); }
        mpq_clears(R,C,E,x,g,NULL);if(ok)return 0;goto bad;
    }
    unsigned a,b,c;if(argc<2||!nu(argv[1],&a))goto bad;
    if(!strcmp(op,"carry")&&argc==4&&nu(argv[2],&b))return carry(a,b,argv[3]);
    if(!strcmp(op,"divisor-work")&&argc==3&&nu(argv[2],&b))return divisor_work(a,b,0);
    if(!strcmp(op,"parent-credit")&&argc==2)return divisor_work(a,8*a,1);
    if(!strcmp(op,"polarity")&&argc==3&&nu(argv[2],&b)&&a>=2&&a<=36) {
        unsigned x=(b/(a-1))%2,y=(b/a)%2,z=(b/(a*a))%2,carry_bit=(x+y+z)/2;int difference=(int)x-(int)y,eta=difference*difference*(1-2*(int)z);
        printf("polarity=%d\nshort_bit=%u\nbase_bit=%u\nsquare_bit=%u\ncarry=%u\ndisagreement=%d\nradial_change=%d\n",polarity(a,b),x,y,z,carry_bit,eta,polarity(a,b+a-1)-polarity(a,b));
        for(unsigned s=0;s<a-1;++s)printf("spoke=%u response=%d\n",s,(polarity(a,b+s+1)-polarity(a,b+s))/2);
        mpq_t H,t;mpq_inits(H,t,NULL);nq(H,1,1);for(unsigned j=1;j<a;++j) { nq(t,1,j);mpq_add(H,H,t); }ns(H,H,1,a*(a-1));np("disagreement_cost_upper",H);nq(t,1,a);np("carry_cost_upper",t);mpq_clears(H,t,NULL);return 0;
    }
    if(!strcmp(op,"detail")&&argc==2&&a>=2&&a<=512) {
        mpq_t A,coef,t,lift;mpq_inits(A,coef,t,lift,NULL);
        for(unsigned m=1;m<=a;m+=2) { nq(t,nm(m)*nm(m),nj(m));mpq_add(A,A,t); }np("arithmetic_mass",A);nq(lift,2,1);
        for(unsigned j=1;j<=a;j+=2) { nq(coef,0,1);for(unsigned m=j;m<=a;m+=2*j) { nq(t,nm(m/j)*nm(m),nj(m));mpq_add(coef,coef,t); }ns(coef,coef,j,1);mpq_div(coef,coef,A);printf("odd_clock=%u\n",j);np("detail_coefficient",coef);if(j>1) { ns(t,coef,2,1);mpq_add(lift,lift,t);ns(t,coef,-(long)j,1);np("lift_coefficient_over_sqrt2",t); } }
        np("lift_clock2_over_sqrt2",lift);
        mpfr_t lo,hi,alo,ahi,bound;mpfr_inits2(256,lo,hi,alo,ahi,bound,(mpfr_ptr)0);
        mpfr_const_pi(lo,MPFR_RNDD);mpfr_const_pi(hi,MPFR_RNDU);mpfr_sqr(lo,lo,MPFR_RNDD);mpfr_sqr(hi,hi,MPFR_RNDU);mpfr_div_ui(bound,hi,6*a,MPFR_RNDU);
        mpfr_set_q(alo,A,MPFR_RNDD);mpfr_set_q(ahi,A,MPFR_RNDU);mpfr_div_ui(lo,lo,8,MPFR_RNDD);mpfr_div_ui(hi,hi,8,MPFR_RNDU);mpfr_div(lo,lo,ahi,MPFR_RNDD);mpfr_div(hi,hi,alo,MPFR_RNDU);mpfr_sub_ui(lo,lo,1,MPFR_RNDD);mpfr_sub_ui(hi,hi,1,MPFR_RNDU);
        mpfr_printf("complete_detail_error=[%.20RDe, %.20RUe]\ncomplete_error_upper=%.20RUe\n",lo,hi,bound);
        mpfr_clears(lo,hi,alo,ahi,bound,(mpfr_ptr)0);mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);mpq_clears(A,coef,t,lift,NULL);return 0;
    }
    if(!strcmp(op,"divisor-family")&&argc==4&&nu(argv[2],&b)&&nu(argv[3],&c)&&a>=1&&a<=128&&b>=1&&b<=16*a&&(b&1)&&c<=10000) {
        unsigned S=4*a;mpq_t *old=nv(2*S+1),*child=nv(4*S+1),*v=nv(c+1),*w=nv(c+1);if(!old||!child||!v||!w) { nf(old,2*S+1);nf(child,4*S+1);nf(v,c+1);nf(w,c+1);return 1; }
        divisor_coeff(old,S,b);divisor_coeff(child,2*S,b);readings(v,c,old,2*S);readings(w,c,child,4*S);
        np("parent_reading",v[c]);np("child_reading",w[c]);mpq_t mass,neutral,x;mpq_inits(mass,neutral,x,NULL);mpq_sub(x,w[c],v[c]);np("difference",x);
        for(unsigned j=1;j<=4*S;++j) { if(j<=2*S)mpq_sub(x,child[j],old[j]);else mpq_set(x,child[j]);ns(x,x,1,j);mpq_add(neutral,neutral,x);ns(x,x,j,1);mpq_abs(x,x);mpq_add(mass,mass,x); }
        np("changed_reset_mass",mass);np("reciprocal_balance",neutral);int failed=mpq_cmp_ui(mass,20,1)>0||mpq_sgn(neutral);mpq_clears(mass,neutral,x,NULL);nf(old,2*S+1);nf(child,4*S+1);nf(v,c+1);nf(w,c+1);return failed;
    }
bad: fputs("Invalid native arithmetic parameters; see help native-refinement.\n",stderr);return 1;
}
