/* Parameterized exact observations. Point readings, simultaneous boundaries,
 * signed interactions and observation weights remain separate inputs. */
#include "field_observation.h"
#include <gmp.h>
#include <mpfr.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { FO_VALUES=256, FO_FIELDS=16, FO_BOUNDARIES=513, FO_ROWS=8 };
typedef struct { mpq_t re,im; } Complex;
static void zi(Complex *z) { mpq_inits(z->re,z->im,NULL); }
static void zc(Complex *z) { mpq_clears(z->re,z->im,NULL); }
static void zz(Complex *z) { mpq_set_ui(z->re,0,1);mpq_set_ui(z->im,0,1); }
static void zs(Complex *z,const Complex *a) { mpq_set(z->re,a->re);mpq_set(z->im,a->im); }
static void za(Complex *z,const Complex *a,const Complex *b) { mpq_add(z->re,a->re,b->re);mpq_add(z->im,a->im,b->im); }
static void zd(Complex *z,const Complex *a,const Complex *b) { mpq_sub(z->re,a->re,b->re);mpq_sub(z->im,a->im,b->im); }
static void zq(Complex *z,const Complex *a,const mpq_t q) { mpq_mul(z->re,a->re,q);mpq_mul(z->im,a->im,q); }
static void zm(Complex *z,const Complex *a,const Complex *b,int conjugate)
{
    mpq_t re,im,x,y;mpq_inits(re,im,x,y,NULL);
    mpq_mul(x,a->re,b->re);mpq_mul(y,a->im,b->im);if(conjugate)mpq_add(re,x,y);else mpq_sub(re,x,y);
    mpq_mul(x,a->im,b->re);mpq_mul(y,a->re,b->im);if(conjugate)mpq_sub(im,y,x);else mpq_add(im,x,y);
    mpq_set(z->re,re);mpq_set(z->im,im);mpq_clears(re,im,x,y,NULL);
}
static void zn(mpq_t out,const Complex *z)
{ mpq_t t;mpq_init(t);mpq_mul(out,z->re,z->re);mpq_mul(t,z->im,z->im);mpq_add(out,out,t);mpq_clear(t); }
static void qi(mpq_t q,long n,unsigned long d) { mpq_set_si(q,n,d);mpq_canonicalize(q); }
static void qs(mpq_t q,const mpq_t x,long n,unsigned long d)
{ mpq_t t;mpq_init(t);qi(t,n,d);mpq_mul(q,x,t);mpq_clear(t); }
static void qp(const char *name,const mpq_t q) { gmp_printf("%s=%Qd\n",name,q); }
static void zp(const char *name,const Complex *z) { gmp_printf("%s=%Qd:%Qd\n",name,z->re,z->im); }
static int integer(const char *s,unsigned *n,unsigned maximum)
{
    if(!s||!*s)return 0;
    for(const char *p=s;*p;++p)if(*p<'0'||*p>'9')return 0;
    errno=0;char *end;unsigned long v=strtoul(s,&end,10);if(errno||*end||v>maximum)return 0;*n=(unsigned)v;return 1;
}
static int rational(const char *s,mpq_t q)
{
    if(!s||!*s||strlen(s)>160)return 0;
    const char *p=s;if(*p=='-')++p;int digits=0,slash=0;
    for(;*p;++p) { if(*p>='0'&&*p<='9') { ++digits;continue; }if(*p=='/'&&digits&&!slash) { slash=1;digits=0;continue; }return 0; }
    if(!digits||mpq_set_str(q,s,10)||mpz_sgn(mpq_denref(q))<=0)return 0;
    if(mpz_sizeinbase(mpq_numref(q),2)>256||mpz_sizeinbase(mpq_denref(q),2)>256)return 0;
    mpq_canonicalize(q);return 1;
}
static int complex_value(const char *s,Complex *z)
{
    const char *colon=strchr(s,':');if(!colon)return rational(s,z->re);
    char part[162];size_t n=(size_t)(colon-s);if(!n||n>=sizeof part)return 0;memcpy(part,s,n);part[n]=0;
    return rational(part,z->re)&&rational(colon+1,z->im);
}
static int list(const char *s,Complex *v,unsigned max,unsigned *count)
{
    *count=0;if(!s||!*s||strlen(s)>32768)return 0;
    while(*s) { const char *comma=strchr(s,',');size_t n=comma?(size_t)(comma-s):strlen(s);char word[326];
        if(!n||n>=sizeof word||*count==max)return 0;
        memcpy(word,s,n);word[n]=0;if(!complex_value(word,v+*count))return 0;++*count;
        if(!comma)break;
        s=comma+1;if(!*s)return 0;
    }
    return *count>0;
}
static int real_list(Complex *v,unsigned n,int sign)
{ for(unsigned i=0;i<n;++i)if(mpq_sgn(v[i].im)||(sign==1&&mpq_sgn(v[i].re)<=0)||(sign==0&&mpq_sgn(v[i].re)<0))return 0;return 1; }
static void fraction(mpq_t out,const mpq_t x)
{ mpz_t r;mpz_init(r);mpz_fdiv_r(r,mpq_numref(x),mpq_denref(x));mpz_set(mpq_numref(out),r);mpz_set(mpq_denref(out),mpq_denref(x));mpq_canonicalize(out);mpz_clear(r); }
static void saw(mpq_t out,const mpq_t x)
{ fraction(out,x);if(mpq_sgn(out)) { mpq_t half;mpq_init(half);qi(half,1,2);mpq_sub(out,out,half);mpq_clear(half); } }
static int whole(const mpq_t x) { return mpz_cmp_ui(mpq_denref(x),1)==0; }
static void clock_value(Complex *out,const mpq_t x,Complex *frequency,Complex *phase,Complex *amplitude,unsigned n)
{
    mpq_t arg,t;mpq_inits(arg,t,NULL);Complex v;zi(&v);zz(out);
    for(unsigned i=0;i<n;++i) { mpq_mul(arg,x,frequency[i].re);mpq_add(arg,arg,phase[i].re);saw(t,arg);qs(t,t,2,1);zq(&v,amplitude+i,t);za(out,out,&v); }
    zc(&v);mpq_clears(arg,t,NULL);
}
static void pulse_value(Complex *out,const mpq_t x,Complex *left,Complex *right,Complex *amplitude,Complex *lv,Complex *rv,unsigned n)
{
    zz(out);
    for(unsigned i=0;i<n;++i) {
        if(mpq_equal(x,left[i].re))za(out,out,lv+i);
        else if(mpq_equal(x,right[i].re)||(!mpq_sgn(x)&&mpq_cmp_ui(right[i].re,1,1)==0))za(out,out,rv+i);
        else if(mpq_cmp(x,left[i].re)>0&&mpq_cmp(x,right[i].re)<0)za(out,out,amplitude+i);
    }
}
static int boundary_insert(mpq_t *points,unsigned *count,const mpq_t x)
{
    unsigned at=0;while(at<*count&&mpq_cmp(points[at],x)<0)++at;
    if(at<*count&&mpq_equal(points[at],x))return 1;
    if(*count>=FO_BOUNDARIES-1)return 0;
    for(unsigned i=*count;i>at;--i)mpq_set(points[i],points[i-1]);
    mpq_set(points[at],x);++*count;return 1;
}
#include "field_observation_segments.inc"
#include "field_observation_matrix.inc"

static int grid(int argc,char **argv,int pulses)
{
    int matrix=argc>1&&!strcmp(argv[argc-1],"--matrix");if(matrix)--argc;
    if(argc!=(pulses?8:6))return 1;
    unsigned q=0;if(!integer(argv[1],&q,10000)||!q)return 1;
    Complex data[5][FO_FIELDS];for(unsigned i=0;i<5;++i)for(unsigned j=0;j<FO_FIELDS;++j)zi(&data[i][j]);
    mpq_t theta,x,y,z,width,continuous,sampled,point,jump,curvature,error,slope_norm,hleft,hright,hpoint;
    mpq_inits(theta,x,y,z,width,continuous,sampled,point,jump,curvature,error,slope_norm,hleft,hright,hpoint,NULL);
    mpq_t points[FO_BOUNDARIES];for(unsigned i=0;i<FO_BOUNDARIES;++i)mpq_init(points[i]);
    unsigned count[5]={0},boundaries=1;int ok=rational(argv[2],theta)&&mpq_sgn(theta)>=0&&mpq_cmp_ui(theta,1,1)<0;
    for(unsigned i=0;i<(pulses?5u:3u)&&ok;++i)ok=list(argv[i+3],data[i],FO_FIELDS,count+i)&&(i==0||count[i]==count[0]);
    unsigned n=count[0];Complex value,slope,C,U,tmp,left_value,right_value;
    zi(&value);zi(&slope);zi(&C);zi(&U);zi(&tmp);zi(&left_value);zi(&right_value);
    if(ok&&pulses) {
        ok=real_list(data[0],n,0)&&real_list(data[1],n,1);
        for(unsigned i=0;i<n&&ok;++i) {
            ok=mpq_cmp(data[0][i].re,data[1][i].re)<0&&mpq_cmp_ui(data[1][i].re,1,1)<=0;
            if(!mpq_sgn(data[0][i].re)&&mpq_cmp_ui(data[1][i].re,1,1)==0)ok=mpq_equal(data[3][i].re,data[4][i].re)&&mpq_equal(data[3][i].im,data[4][i].im);
            boundary_insert(points,&boundaries,data[0][i].re);fraction(x,data[1][i].re);boundary_insert(points,&boundaries,x);
        }
    } else if(ok) {
        ok=real_list(data[0],n,1)&&real_list(data[1],n,0);unsigned total=0;
        for(unsigned i=0;i<n&&ok;++i) {
            ok=whole(data[0][i].re)&&mpq_cmp_ui(data[0][i].re,120,1)<=0&&mpq_cmp_ui(data[1][i].re,1,1)<0;
            if(!ok)break;
            unsigned r=(unsigned)mpz_get_ui(mpq_numref(data[0][i].re));total+=r;if(total>512) { ok=0;break; }
            qs(x,data[0][i].re,2,1);zq(&tmp,&data[2][i],x);za(&slope,&slope,&tmp);
            for(unsigned a=0;a<r;++a) { qi(x,a,1);mpq_sub(x,x,data[1][i].re);mpq_div(x,x,data[0][i].re);fraction(x,x);if(!boundary_insert(points,&boundaries,x))ok=0; }
        }
    }
    if(ok) {
        qi(points[boundaries],1,1);zn(slope_norm,&slope);
        for(unsigned i=0;i<boundaries;++i) {
            mpq_add(x,points[i],points[i+1]);qs(x,x,1,2);mpq_sub(width,points[i+1],points[i]);
            if(pulses)pulse_value(&value,x,data[0],data[1],data[2],data[3],data[4],n);
            else clock_value(&value,x,data[0],data[1],data[2],n);
            zn(y,&value);
            if(!pulses) { mpq_mul(z,width,width);mpq_mul(z,z,slope_norm);qs(z,z,1,12);mpq_add(y,y,z); }
            mpq_mul(y,y,width);mpq_add(continuous,continuous,y);
        }
        for(unsigned a=0;a<q;++a) {
            qi(x,a,1);mpq_add(x,x,theta);qs(x,x,1,q);
            if(pulses)pulse_value(&value,x,data[0],data[1],data[2],data[3],data[4],n);else clock_value(&value,x,data[0],data[1],data[2],n);
            zn(y,&value);qs(y,y,1,q);mpq_add(sampled,sampled,y);
        }
        for(unsigned i=0;i<boundaries;++i) {
            qs(x,points[i],q,1);mpq_sub(x,x,theta);saw(y,x);
            if(pulses) {
                unsigned prev=i?i-1:boundaries-1;mpq_add(z,points[prev],points[prev+1]);qs(z,z,1,2);pulse_value(&left_value,z,data[0],data[1],data[2],data[3],data[4],n);
                mpq_add(z,points[i],points[i+1]);qs(z,z,1,2);pulse_value(&right_value,z,data[0],data[1],data[2],data[3],data[4],n);
                pulse_value(&value,points[i],data[0],data[1],data[2],data[3],data[4],n);zn(hleft,&left_value);zn(hright,&right_value);zn(hpoint,&value);
                if(whole(x)) { mpq_add(z,hleft,hright);qs(z,z,1,2);mpq_sub(z,z,hpoint);qs(z,z,1,q);mpq_add(point,point,z); }
                mpq_sub(z,hright,hleft);mpq_mul(z,z,y);qs(z,z,-1,q);mpq_add(jump,jump,z);
            } else {
                zz(&C);clock_value(&U,points[i],data[0],data[1],data[2],n);
                for(unsigned j=0;j<n;++j) { mpq_mul(z,points[i],data[0][j].re);mpq_add(z,z,data[1][j].re);if(whole(z))za(&C,&C,&data[2][j]); }
                if(whole(x)) { zn(z,&C);qs(z,z,1,q);mpq_add(point,point,z); }
                zm(&tmp,&C,&U,1);mpq_mul(z,tmp.re,y);qs(z,z,4,q);mpq_add(jump,jump,z);
                fraction(y,x);mpq_mul(z,y,y);mpq_sub(z,z,y);qi(y,1,6);mpq_add(z,z,y);zm(&tmp,&C,&slope,1);mpq_mul(z,z,tmp.re);qs(z,z,-2,(unsigned long)q*q);mpq_add(curvature,curvature,z);
            }
        }
        mpq_sub(x,continuous,sampled);mpq_add(error,point,jump);mpq_add(error,error,curvature);mpq_sub(error,error,x);ok=!mpq_sgn(error);
        if(ok) { qp("continuous_energy",continuous);qp("sampled_energy",sampled);qp("defect",x);qp("point_correction",point);qp("value_jump",jump);qp("derivative_jump",curvature);qp("identity_error",error);printf("distinct_boundaries=%u\n",boundaries); }
        if(ok&&matrix)ok=fo_grid_matrix(q,theta,data,n,pulses,points,boundaries);
    }
    for(unsigned i=0;i<5;++i)for(unsigned j=0;j<FO_FIELDS;++j)zc(&data[i][j]);
    for(unsigned i=0;i<FO_BOUNDARIES;++i)mpq_clear(points[i]);
    mpq_clears(theta,x,y,z,width,continuous,sampled,point,jump,curvature,error,slope_norm,hleft,hright,hpoint,NULL);zc(&value);zc(&slope);zc(&C);zc(&U);zc(&tmp);zc(&left_value);zc(&right_value);return !ok;
}
static int weighted(int argc,char **argv)
{
    const char *op=argv[0];int observation=!strcmp(op,"work"),variation=!strcmp(op,"native-variation"),boundary=!strcmp(op,"native-boundary");
    if(argc!=(observation?5:variation?4:3))return 1;
    Complex data[4][FO_VALUES];for(unsigned i=0;i<4;++i)for(unsigned j=0;j<FO_VALUES;++j)zi(&data[i][j]);
    unsigned count[4]={0},start=1;int ok=observation||integer(argv[1],&start,10000);if(!start)ok=0;
    for(unsigned i=0;i<(observation?4u:variation?2u:1u)&&ok;++i)ok=list(argv[i+(observation?1:2)],data[i],FO_VALUES,count+i)&&(i==0||count[i]==count[0]);
    if(observation&&ok)ok=real_list(data[0],count[0],0)&&real_list(data[1],count[0],0);
    Complex sum,endpoint,change,prefix,z,v,old;zi(&sum);zi(&endpoint);zi(&change);zi(&prefix);zi(&z);zi(&v);zi(&old);
    mpq_t before,after,mass,cross,newpart,x,y,error;mpq_inits(before,after,mass,cross,newpart,x,y,error,NULL);
    if(ok&&observation) {
        for(unsigned i=0;i<count[0];++i) {
            zn(x,&data[2][i]);mpq_mul(y,x,data[0][i].re);mpq_add(before,before,y);mpq_sub(y,data[1][i].re,data[0][i].re);mpq_mul(y,y,x);mpq_add(mass,mass,y);
            za(&z,&data[2][i],&data[3][i]);zn(y,&z);mpq_mul(y,y,data[1][i].re);mpq_add(after,after,y);
            zm(&z,&data[2][i],&data[3][i],1);mpq_mul(y,z.re,data[1][i].re);qs(y,y,2,1);mpq_add(cross,cross,y);
            zn(y,&data[3][i]);mpq_mul(y,y,data[1][i].re);mpq_add(newpart,newpart,y);
        }
        mpq_sub(x,after,before);mpq_add(error,mass,cross);mpq_add(error,error,newpart);mpq_sub(error,error,x);ok=!mpq_sgn(error);
        if(ok) { qp("old_energy",before);qp("new_energy",after);qp("energy_change",x);qp("observation_change",mass);qp("signed_interaction",cross);qp("addition_energy",newpart);qp("identity_error",error); }
    } else if(ok&&boundary) {
        unsigned last=start+count[0]-1;qi(x,1,start);zq(&endpoint,data[0],x);qi(x,1,last+1);zq(&z,&data[0][count[0]-1],x);zd(&endpoint,&endpoint,&z);
        for(unsigned i=0;i<count[0];++i) {
            unsigned n=start+i;qi(x,1,(unsigned long)n*(n+1));zq(&z,&data[0][i],x);za(&sum,&sum,&z);
            if(i) { zd(&z,&data[0][i],&data[0][i-1]);qi(x,1,n);zq(&z,&z,x);za(&change,&change,&z); }
        }
        za(&z,&endpoint,&change);ok=mpq_equal(z.re,sum.re)&&mpq_equal(z.im,sum.im);if(ok) { zp("weighted_sum",&sum);zp("endpoint_terms",&endpoint);zp("reset_terms",&change); }
    } else if(ok) {
        unsigned last=start+count[0]-1;
        for(unsigned i=0;i<count[0];++i) {
            unsigned n=start+i;za(&prefix,&prefix,&data[0][i]);zm(&z,&data[0][i],&data[1][i],0);qi(x,1,(unsigned long)n*(n+1));zq(&z,&z,x);za(&sum,&sum,&z);
            if(i+1<count[0]) {
                qi(x,2,(unsigned long)n*(n+1)*(n+2));zq(&v,&data[1][i],x);
                zd(&z,&data[1][i+1],&data[1][i]);qi(x,1,(unsigned long)(n+1)*(n+2));zq(&z,&z,x);zd(&v,&v,&z);zm(&z,&prefix,&v,0);za(&change,&change,&z);
            }
        }
        zm(&endpoint,&prefix,&data[1][count[0]-1],0);qi(x,1,(unsigned long)last*(last+1));zq(&endpoint,&endpoint,x);za(&z,&endpoint,&change);ok=mpq_equal(z.re,sum.re)&&mpq_equal(z.im,sum.im);if(ok) { zp("weighted_product",&sum);zp("upper_endpoint",&endpoint);zp("weighted_variation",&change); }
    }
    for(unsigned i=0;i<4;++i)for(unsigned j=0;j<FO_VALUES;++j)zc(&data[i][j]);
    zc(&sum);zc(&endpoint);zc(&change);zc(&prefix);zc(&z);zc(&v);zc(&old);mpq_clears(before,after,mass,cross,newpart,x,y,error,NULL);return !ok;
}
static int invariant(int argc,char **argv)
{
    if(argc<4||argc>3+FO_ROWS)return 1;
    unsigned m=(unsigned)argc-3,n=0,k=0;Complex weights[FO_VALUES],field[FO_VALUES],rows[FO_ROWS][FO_VALUES];
    for(unsigned i=0;i<FO_VALUES;++i) { zi(weights+i);zi(field+i);for(unsigned j=0;j<m;++j)zi(&rows[j][i]); }
    int ok=list(argv[1],weights,FO_VALUES,&n)&&real_list(weights,n,1)&&list(argv[2],field,FO_VALUES,&k)&&k==n;
    for(unsigned j=0;j<m&&ok;++j)ok=list(argv[j+3],rows[j],FO_VALUES,&k)&&k==n;
    Complex matrix[FO_ROWS][FO_ROWS+1],reading[FO_ROWS],solution[FO_ROWS],x,y,z;for(unsigned i=0;i<m;++i) { zi(reading+i);zi(solution+i);for(unsigned j=0;j<=m;++j)zi(&matrix[i][j]); }zi(&x);zi(&y);zi(&z);
    mpq_t t,pivot,energy,minimum,error;mpq_inits(t,pivot,energy,minimum,error,NULL);
    if(ok) {
        for(unsigned i=0;i<n;++i) { zn(t,field+i);mpq_mul(t,t,weights[i].re);mpq_add(energy,energy,t); }
        for(unsigned i=0;i<m;++i) {
            for(unsigned a=0;a<n;++a) { zm(&x,&rows[i][a],field+a,0);za(reading+i,reading+i,&x); }
            zs(&matrix[i][m],reading+i);
            for(unsigned j=0;j<m;++j)for(unsigned a=0;a<n;++a) { zm(&x,&rows[j][a],&rows[i][a],1);mpq_inv(t,weights[a].re);zq(&x,&x,t);za(&matrix[i][j],&matrix[i][j],&x); }
        }
        for(unsigned c=0;c<m&&ok;++c) {
            ok=mpq_sgn(matrix[c][c].re)>0&&!mpq_sgn(matrix[c][c].im);if(!ok)break;mpq_inv(pivot,matrix[c][c].re);
            for(unsigned j=c;j<=m;++j)zq(&matrix[c][j],&matrix[c][j],pivot);
            for(unsigned i=0;i<m;++i)if(i!=c) { zs(&x,&matrix[i][c]);for(unsigned j=c;j<=m;++j) { zm(&y,&x,&matrix[c][j],0);zd(&matrix[i][j],&matrix[i][j],&y); } }
        }
        if(ok) {
            for(unsigned i=0;i<m;++i) { zs(solution+i,&matrix[i][m]);zm(&x,reading+i,solution+i,1);mpq_add(minimum,minimum,x.re); }
            ok=mpq_sgn(minimum)>=0&&mpq_cmp(minimum,energy)<=0;
            if(ok) { qp("energy",energy);qp("minimum_for_readings",minimum);mpq_sub(t,energy,minimum);qp("unmeasured_energy",t);printf("independent_readings=%u\n",m);for(unsigned i=0;i<m;++i) { printf("row=%u\n",i);zp("reading",reading+i); } }
        }
    }
    for(unsigned i=0;i<FO_VALUES;++i) { zc(weights+i);zc(field+i);for(unsigned j=0;j<m;++j)zc(&rows[j][i]); }
    for(unsigned i=0;i<m;++i) { zc(reading+i);zc(solution+i);for(unsigned j=0;j<=m;++j)zc(&matrix[i][j]); }zc(&x);zc(&y);zc(&z);mpq_clears(t,pivot,energy,minimum,error,NULL);return !ok;
}
static unsigned common(unsigned a,unsigned b) { while(b) { unsigned r=a%b;a=b;b=r; }return a; }
static int mobius(unsigned n) { int sign=1;for(unsigned p=2;p<=n/p;++p)if(n%p==0) { n/=p;sign=-sign;if(n%p==0)return 0; }return n>1?-sign:sign; }
static int shells(int argc,char **argv)
{
    int inverse=argc==3&&!strcmp(argv[2],"--from-prefixes");if(inverse)--argc;
    if(argc!=2)return 1;
    Complex P[FO_VALUES];mpq_t prefix[FO_VALUES+1],logs[FO_VALUES+1],x,y,error;
    for(unsigned i=0;i<FO_VALUES;++i)zi(P+i);
    for(unsigned i=0;i<=FO_VALUES;++i) { mpq_init(prefix[i]);mpq_init(logs[i]); }mpq_inits(x,y,error,NULL);
    unsigned N;int ok=list(argv[1],P,FO_VALUES,&N)&&real_list(P,N,-1);
    if(ok) {
        if(inverse)for(unsigned n=1;n<=N;++n)mpq_set(prefix[n],P[n-1].re);
        else for(unsigned n=1;n<=N;++n)for(unsigned m=1;m<=n;++m) { qs(x,P[m-1].re,n/m,1);mpq_add(prefix[n],prefix[n],x); }
        for(unsigned m=1;m<=N&&ok;++m) { qi(x,0,1);for(unsigned d=1;d<=m;++d)if(m%d==0) { mpq_sub(y,prefix[m/d],prefix[m/d-1]);qs(y,y,mobius(d),1);mpq_add(x,x,y); }if(inverse)mpq_set(P[m-1].re,x);else ok=mpq_equal(x,P[m-1].re); }
        if(inverse)for(unsigned n=1;n<=N&&ok;++n) { qi(x,0,1);for(unsigned m=1;m<=n;++m) { qs(y,P[m-1].re,n/m,1);mpq_add(x,x,y); }ok=mpq_equal(x,prefix[n]); }
        for(unsigned d=2;d<=N;++d)if(mobius(d)) { unsigned v=d;for(unsigned p=2;p<=v;++p)if(v%p==0) { unsigned multiplicity=0;while(v%p==0) { v/=p;++multiplicity; }qs(x,prefix[N/d],-mobius(d)*(long)multiplicity,1);mpq_add(logs[p],logs[p],x); } }
        if(ok) { for(unsigned n=1;n<=N;++n)gmp_printf("cutoff=%u primitive_shell=%Qd square_prefix=%Qd\n",n,P[n-1].re,prefix[n]);for(unsigned p=2;p<=N;++p)if(mpq_sgn(logs[p]))gmp_printf("log_prime=%u coefficient=%Qd\n",p,logs[p]); }
    }
    for(unsigned i=0;i<FO_VALUES;++i)zc(P+i);
    for(unsigned i=0;i<=FO_VALUES;++i) { mpq_clear(prefix[i]);mpq_clear(logs[i]); }mpq_clears(x,y,error,NULL);return !ok;
}
static int registers(int argc,char **argv)
{
    if(argc!=5)return 1;
    Complex moduli[FO_FIELDS],residues[FO_FIELDS],amplitudes[FO_FIELDS],weights[FO_VALUES];
    for(unsigned i=0;i<FO_FIELDS;++i) { zi(moduli+i);zi(residues+i);zi(amplitudes+i); }for(unsigned i=0;i<FO_VALUES;++i)zi(weights+i);
    unsigned n,k,N;int ok=list(argv[1],moduli,FO_FIELDS,&n)&&list(argv[2],residues,FO_FIELDS,&k)&&k==n&&list(argv[3],amplitudes,FO_FIELDS,&k)&&k==n&&list(argv[4],weights,FO_VALUES,&N)&&real_list(moduli,n,1)&&real_list(residues,n,0)&&real_list(weights,N,0);
    unsigned d[FO_FIELDS],r[FO_FIELDS];for(unsigned i=0;i<n&&ok;++i) { ok=whole(moduli[i].re)&&whole(residues[i].re)&&mpq_cmp_ui(moduli[i].re,10000,1)<=0&&mpq_cmp(residues[i].re,moduli[i].re)<0;if(ok) { d[i]=(unsigned)mpz_get_ui(mpq_numref(moduli[i].re));r[i]=(unsigned)mpz_get_ui(mpq_numref(residues[i].re)); } }
    Complex sum,z;zi(&sum);zi(&z);mpq_t energy,pairs,diagonal,weight,x;mpq_inits(energy,pairs,diagonal,weight,x,NULL);
    if(ok) {
        for(unsigned a=1;a<=N;++a) { zz(&sum);for(unsigned i=0;i<n;++i)if(a%d[i]==r[i])za(&sum,&sum,amplitudes+i);zn(x,&sum);mpq_mul(x,x,weights[a-1].re);mpq_add(energy,energy,x); }
        for(unsigned i=0;i<n;++i)for(unsigned j=0;j<n;++j) {
            qi(weight,0,1);for(unsigned a=1;a<=N;++a)if(a%d[i]==r[i]&&a%d[j]==r[j])mpq_add(weight,weight,weights[a-1].re);
            zm(&z,amplitudes+i,amplitudes+j,1);mpq_mul(x,weight,z.re);mpq_add(pairs,pairs,x);if(i==j)mpq_add(diagonal,diagonal,x);
        }
        ok=mpq_equal(energy,pairs);if(ok) { qp("energy",energy);qp("ordered_pair_energy",pairs);qp("diagonal_energy",diagonal);mpq_sub(x,pairs,diagonal);qp("signed_cross_energy",x);for(unsigned i=0;i<n;++i)for(unsigned j=i+1;j<n;++j)printf("left=%u right=%u compatible=%u\n",i,j,r[i]%common(d[i],d[j])==r[j]%common(d[i],d[j])); }
    }
    for(unsigned i=0;i<FO_FIELDS;++i) { zc(moduli+i);zc(residues+i);zc(amplitudes+i); }for(unsigned i=0;i<FO_VALUES;++i)zc(weights+i);zc(&sum);zc(&z);mpq_clears(energy,pairs,diagonal,weight,x,NULL);return !ok;
}
static int harmonics(int argc,char **argv)
{
    int matrix=argc>1&&!strcmp(argv[argc-1],"--matrix");if(matrix)--argc;
    if(argc!=5)return 1;
    unsigned q=0,n=0,k=0;Complex frequency[FO_FIELDS],amplitude[FO_FIELDS],z;
    for(unsigned i=0;i<FO_FIELDS;++i) { zi(frequency+i);zi(amplitude+i); }zi(&z);
    mpq_t theta,continuous,sampled,x;mpq_inits(theta,continuous,sampled,x,NULL);
    int ok=integer(argv[1],&q,10000)&&q>0&&rational(argv[2],theta)&&(mpq_sgn(theta)==0||mpq_cmp_ui(theta,1,2)==0)&&list(argv[3],frequency,FO_FIELDS,&n)&&list(argv[4],amplitude,FO_FIELDS,&k)&&n==k&&real_list(frequency,n,-1);
    long freq[FO_FIELDS];for(unsigned i=0;i<n&&ok;++i) { mpq_abs(x,frequency[i].re);ok=whole(frequency[i].re)&&mpq_cmp_ui(x,10000,1)<=0;if(ok)freq[i]=mpz_get_si(mpq_numref(frequency[i].re)); }
    if(ok) {
        for(unsigned i=0;i<n;++i)for(unsigned j=0;j<n;++j) {
            zm(&z,amplitude+i,amplitude+j,1);long difference=freq[j]-freq[i];
            if(!difference)mpq_add(continuous,continuous,z.re);
            if(difference%(long)q==0) { int sign=mpq_sgn(theta)&&((difference/(long)q)%2)?-1:1;qs(x,z.re,sign,1);mpq_add(sampled,sampled,x); }
        }
        qp("continuous_energy",continuous);qp("sampled_energy",sampled);mpq_sub(x,continuous,sampled);qp("defect",x);puts("Exact Fourier aliasing at shift 0 or 1/2; signed frequencies and complex amplitudes are retained.");
        if(matrix)ok=fo_harmonic_matrix(q,theta,freq,amplitude,n);
    }
    for(unsigned i=0;i<FO_FIELDS;++i) { zc(frequency+i);zc(amplitude+i); }zc(&z);mpq_clears(theta,continuous,sampled,x,NULL);return !ok;
}
void field_observation_help(void)
{
    puts("Exact fields under specified readings, grids and observation weights\n\n"
         "  nfield field-observation clocks q shift frequencies phases amplitudes [--matrix]\n"
         "  nfield field-observation pulses q shift lefts rights amplitudes left-readings right-readings [--matrix]\n"
         "  nfield field-observation harmonics q shift frequencies amplitudes [--matrix]\n"
         "  nfield field-observation segments q shift boundaries starts slopes readings\n"
         "  nfield field-observation native-cycle cutoff readings\n"
         "  nfield field-observation tail-bound cutoff old-envelope new-envelope head [tolerance]\n"
         "  nfield field-observation work old-weights new-weights field addition\n"
         "  nfield field-observation native-boundary first-address readings\n"
         "  nfield field-observation native-variation first-address first-field second-field\n"
         "  nfield field-observation invariants weights field row [row ...]\n"
         "  nfield field-observation register moduli residues amplitudes weights\n"
         "  nfield field-observation shells values [--from-prefixes]\n"
         "  nfield field-observation verify\n\n"
         "Lists are comma-separated exact rationals. Complex readings use real:imag.\n"
         "Matching lists have the same length; at most 16 fields or 256 addresses.\n"
         "Grid q=1..10000, rational shift in [0,1). Clocks use positive integer\n"
         "frequencies <=120 (sum <=512), phases in [0,1), midpoint reset readings.\n"
         "Pulses have 0<=left<right<=1 and explicit endpoint readings. A full-circle\n"
         "pulse must assign the same reading at 0 and 1. Overlap is retained.\n"
         "Harmonics: signed integer frequencies -10000..10000, shift 0 or 1/2.\n"
         "Amplitudes multiply exp(2*pi*i*frequency*x); Fourier aliasing is exact.\n"
         "Segments: increasing boundaries starting at 0, below 1; independent complex\n"
         "starts, slopes and boundary readings. Includes the regular curvature term.\n"
         "Native-cycle lists start at residue zero, length <=256, cutoff <=1000000.\n"
         "Tail-bound uses supplied nonnegative envelopes and exact rational heads.\n"
         "Weights are nonnegative. Invariants require positive weights and 1..8\n"
         "independent rows; their minimum applies to every field with those readings.\n"
         "Registers retain ordered pairs on addresses 1..number-of-weights.\n"
         "Shell output gives exact prefixes and formal prime-log coefficients.\n"
         "--from-prefixes recovers signed primitive shells from supplied square\n"
         "prefixes at cutoffs 1..length (prefix zero is zero), then checks reconstruction.\n"
         "--matrix appends exact continuous, sampled and defect matrices for the\n"
         "supplied components. Clocks and pulses also resolve all boundary matrices.\n"
         "Complex amplitudes and actual endpoint readings belong to each component;\n"
         "subsequent coefficients act by conjugate(z) H z. Rows start at zero.\n"
         "All identities are finite. Limit or uniform estimates require their stated hypotheses.");
}
int field_observation_verify(void)
{
    char *pulse[]={"pulses","4","0","0","1/2","1","1/2","1/2"};
    char *clock[]={"clocks","5","1/2","1,2","0,1/3","1,-1"};
    int ok=!grid(8,pulse,1)&&!grid(6,clock,0);if(ok)puts("Field observations: PASS (finite boundary identities)");return ok;
}
int field_observation_command(int argc,char **argv)
{
    if(!argc||(argc==1&&(!strcmp(argv[0],"help")||!strcmp(argv[0],"--help")))) { field_observation_help();return 0; }
    if(argc==1&&!strcmp(argv[0],"verify"))return !field_observation_verify();
    int status=1;
    if(!strcmp(argv[0],"clocks"))status=grid(argc,argv,0);
    else if(!strcmp(argv[0],"pulses"))status=grid(argc,argv,1);
    else if(!strcmp(argv[0],"segments"))status=segments(argc,argv);
    else if(!strcmp(argv[0],"tail-bound"))status=tail_bound(argc,argv);
    else if(!strcmp(argv[0],"native-cycle"))status=native_cycle(argc,argv);
    else if(!strcmp(argv[0],"harmonics"))status=harmonics(argc,argv);
    else if(!strcmp(argv[0],"work")||!strcmp(argv[0],"native-boundary")||!strcmp(argv[0],"native-variation"))status=weighted(argc,argv);
    else if(!strcmp(argv[0],"invariants"))status=invariant(argc,argv);
    else if(!strcmp(argv[0],"register"))status=registers(argc,argv);
    else if(!strcmp(argv[0],"shells"))status=shells(argc,argv);
    if(status)fputs("Invalid field-observation inputs or dependent invariant rows; see help field-observation.\n",stderr);
    return status;
}
