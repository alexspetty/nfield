#define _POSIX_C_SOURCE 200809L
#include "native_refinement.h"
#include "nfield.h"

#include <errno.h>
#include <fcntl.h>
#include <gmp.h>
#include <mpfr.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Parameterized orthogonal traces with complete-period native Gram audits. */
enum { PREC = 256, TOP = 16, DIM = TOP + 1, SUPPORT = 21 };
/* Each library caller keeps its own precision. Larger detector solves need
 * additional guard bits against interval dependency growth. */
static __thread mpfr_prec_t calculation_precision = PREC;
enum { MAX_COLLISION_OBSERVATIONS = 42, MAX_SHELL_DIMENSION = TOP };
typedef struct { mpfr_t lo, hi; } Interval;
typedef struct { unsigned checks, failures; const char *first_error; } Audit;
enum {
    D, CAPACITY, ROW_NORM, CONDITIONED_TARGET, CONDITIONED_ORIGIN,
    GAMMA, OMEGA, GAIN, RESPONSE, COST, CAPACITY_STEP,
    BLOCK_GAIN, BLOCK_RESPONSE, BLOCK_COST, CERTIFICATE, CAPTURE, INVISIBLE,
    NORMALIZED, ENDPOINT_NORMALIZED, LOG_NORMALIZED, DIAGONAL, CROSS, FIELDS
};
typedef struct {
    Interval value[FIELDS], target[DIM], origin[DIM], direction[DIM];
} Frame;
typedef struct {
    Audit audit;
    int first, last;
    unsigned period;
    Interval gram[DIM][DIM], conditioned[DIM][DIM], h[DIM], u[DIM], eta[SUPPORT+1];
    Frame frame[DIM];
    mpq_t raw[DIM];
} Run;
typedef struct {
    int base,modulus,count,finite_orbit_rank,projected_rank,projected_rank_exact;
    int uniform_residue_mean_zero_exact;
    int multiplier[MAX_COLLISION_OBSERVATIONS],selected[MAX_SHELL_DIMENSION];
    Interval mean[MAX_COLLISION_OBSERVATIONS],norm[MAX_COLLISION_OBSERVATIONS];
    Interval coupling[MAX_COLLISION_OBSERVATIONS][DIM];
    Interval omega[MAX_COLLISION_OBSERVATIONS][DIM];
    Interval response[MAX_COLLISION_OBSERVATIONS];
    Interval gram[MAX_COLLISION_OBSERVATIONS][MAX_COLLISION_OBSERVATIONS];
    Interval basis[MAX_SHELL_DIMENSION][DIM];
    Interval collective,capture,missed,normalized;
    int prefix_rank[DIM],prefix_rank_exact[DIM];
    Interval prefix_collective[DIM],prefix_capture[DIM],prefix_missed[DIM];
} CollisionFamily;

static void solve(Run *r,const Interval *rhs,int last,Interval *x);

static int check(Audit *a, int ok, const char *message)
{
    ++a->checks;
    if (!ok) { ++a->failures; if (!a->first_error) a->first_error = message; }
    return ok;
}
static void init(Interval *a)
{ mpfr_init2(a->lo, calculation_precision); mpfr_init2(a->hi, calculation_precision); mpfr_set_zero(a->lo, 0); mpfr_set_zero(a->hi, 0); }
static void clear(Interval *a) { mpfr_clear(a->lo); mpfr_clear(a->hi); }
static void init_array(Interval *a, int n) { for (int i=0; i<n; ++i) init(a+i); }
static void clear_array(Interval *a, int n) { for (int i=0; i<n; ++i) clear(a+i); }
static void rat(Interval *a, long n, unsigned long d)
{
    mpfr_set_si(a->lo,n,MPFR_RNDD); mpfr_div_ui(a->lo,a->lo,d,MPFR_RNDD);
    mpfr_set_si(a->hi,n,MPFR_RNDU); mpfr_div_ui(a->hi,a->hi,d,MPFR_RNDU);
}
static void set(Interval *a, const Interval *b)
{ mpfr_set(a->lo,b->lo,MPFR_RNDD); mpfr_set(a->hi,b->hi,MPFR_RNDU); }
static void from_q(Interval *a, const mpq_t q)
{ mpfr_set_q(a->lo,q,MPFR_RNDD); mpfr_set_q(a->hi,q,MPFR_RNDU); }
static void add(Interval *c, const Interval *a, const Interval *b)
{
    mpfr_t l,h; mpfr_inits2(calculation_precision,l,h,(mpfr_ptr)0);
    mpfr_add(l,a->lo,b->lo,MPFR_RNDD); mpfr_add(h,a->hi,b->hi,MPFR_RNDU);
    mpfr_set(c->lo,l,MPFR_RNDD); mpfr_set(c->hi,h,MPFR_RNDU); mpfr_clears(l,h,(mpfr_ptr)0);
}
static void sub(Interval *c, const Interval *a, const Interval *b)
{
    mpfr_t l,h; mpfr_inits2(calculation_precision,l,h,(mpfr_ptr)0);
    mpfr_sub(l,a->lo,b->hi,MPFR_RNDD); mpfr_sub(h,a->hi,b->lo,MPFR_RNDU);
    mpfr_set(c->lo,l,MPFR_RNDD); mpfr_set(c->hi,h,MPFR_RNDU); mpfr_clears(l,h,(mpfr_ptr)0);
}
static void mul(Interval *c, const Interval *a, const Interval *b)
{
    mpfr_t l,h,t; mpfr_inits2(calculation_precision,l,h,t,(mpfr_ptr)0);
    mpfr_set_inf(l,1); mpfr_set_inf(h,-1);
    for (int i=0;i<2;++i) for (int j=0;j<2;++j) {
        mpfr_srcptr x=i?a->hi:a->lo, y=j?b->hi:b->lo;
        mpfr_mul(t,x,y,MPFR_RNDD); if(mpfr_less_p(t,l)) mpfr_set(l,t,MPFR_RNDD);
        mpfr_mul(t,x,y,MPFR_RNDU); if(mpfr_greater_p(t,h)) mpfr_set(h,t,MPFR_RNDU);
    }
    mpfr_set(c->lo,l,MPFR_RNDD); mpfr_set(c->hi,h,MPFR_RNDU); mpfr_clears(l,h,t,(mpfr_ptr)0);
}
static void scale(Interval *c,const Interval *a,long n,unsigned long d)
{ Interval b; init(&b); rat(&b,n,d); mul(c,a,&b); clear(&b); }
static void divide(Audit *a,Interval *c,const Interval *x,const Interval *y)
{
    if(!check(a,mpfr_sgn(y->lo)>0,"positive denominator")) { rat(c,0,1); return; }
    Interval inv; init(&inv);
    mpfr_ui_div(inv.lo,1,y->hi,MPFR_RNDD); mpfr_ui_div(inv.hi,1,y->lo,MPFR_RNDU);
    mul(c,x,&inv); clear(&inv);
}
static void square(Interval *c,const Interval *a)
{
    mpfr_t l,h,t; mpfr_inits2(calculation_precision,l,h,t,(mpfr_ptr)0);
    mpfr_sqr(h,a->lo,MPFR_RNDU); mpfr_sqr(t,a->hi,MPFR_RNDU);
    if(mpfr_greater_p(t,h)) mpfr_set(h,t,MPFR_RNDU);
    if(mpfr_sgn(a->lo)<=0 && mpfr_sgn(a->hi)>=0) mpfr_set_zero(l,0);
    else {
        mpfr_sqr(l,a->lo,MPFR_RNDD); mpfr_sqr(t,a->hi,MPFR_RNDD);
        if(mpfr_less_p(t,l)) mpfr_set(l,t,MPFR_RNDD);
    }
    mpfr_set(c->lo,l,MPFR_RNDD); mpfr_set(c->hi,h,MPFR_RNDU); mpfr_clears(l,h,t,(mpfr_ptr)0);
}
static void root(Audit *a,Interval *c,const Interval *x)
{
    if(!check(a,mpfr_sgn(x->lo)>=0,"nonnegative square root")) { rat(c,0,1); return; }
    mpfr_sqrt(c->lo,x->lo,MPFR_RNDD); mpfr_sqrt(c->hi,x->hi,MPFR_RNDU);
}
static void equal(Audit *a,const Interval *x,const Interval *y,const char *message)
{
    Interval t; init(&t); sub(&t,x,y);
    check(a,mpfr_number_p(t.lo) && mpfr_number_p(t.hi) &&
          mpfr_sgn(t.lo)<=0 && mpfr_sgn(t.hi)>=0,message);
    /* A wide interval must not pass merely because it contains zero. */
    mpfr_sub(t.hi,t.hi,t.lo,MPFR_RNDU);
    check(a,mpfr_cmp_d(t.hi,1e-45)<0,"identity enclosure width below 1e-45");
    clear(&t);
}
static unsigned gcd(unsigned a,unsigned b)
{ while(b) { unsigned t=a%b; a=b; b=t; } return a; }
static void digamma(Interval *a,unsigned n,unsigned d)
{
    rat(a,(long)n,d); /* increasing on the positive real axis */
    mpfr_digamma(a->lo,a->lo,MPFR_RNDD); mpfr_digamma(a->hi,a->hi,MPFR_RNDU);
}
static void gram_entry(Interval *out,unsigned j,unsigned k)
{
    unsigned period=j/gcd(j,k)*k;
    Interval prev,next,t; init(&prev); init(&next); init(&t); rat(out,0,1);
    digamma(&prev,1,period);
    for(unsigned m=1;m<=period;++m) {
        digamma(&next,m+1,period); sub(&t,&next,&prev);
        scale(&t,&t,(long)(m%j)*(m%k),(unsigned long)j*k*period);
        add(out,out,&t); set(&prev,&next);
    }
    clear(&prev); clear(&next); clear(&t);
}
/* The centered lag-one collision table for base two, extended by zero off
 * the units: +1/2 on 1 mod 4 and -1/2 on 3 mod 4. */
static void collision4_value(Interval *out,unsigned m)
{
    unsigned r=m%4;
    rat(out,r==1?1:(r==3?-1:0),2);
}
static void collision4_pair(Interval *out,unsigned j)
{
    unsigned period=4/gcd(4,j)*j;
    Interval prev,next,weight,f,row,t;
    init(&prev); init(&next); init(&weight); init(&f); init(&row); init(&t); rat(out,0,1);
    digamma(&prev,1,period);
    for(unsigned m=1;m<=period;++m) {
        digamma(&next,m+1,period); sub(&weight,&next,&prev); scale(&weight,&weight,1,period); set(&prev,&next);
        collision4_value(&f,m); rat(&row,(long)(m%j),j); mul(&t,&f,&row); mul(&t,&t,&weight); add(out,out,&t);
    }
    clear(&prev); clear(&next); clear(&weight); clear(&f); clear(&row); clear(&t);
}
static void collision4_mean_and_norm(Interval *mean,Interval *norm)
{
    Interval prev,next,weight,f,t;
    init(&prev); init(&next); init(&weight); init(&f); init(&t); rat(mean,0,1); rat(norm,0,1);
    digamma(&prev,1,4);
    for(unsigned m=1;m<=4;++m) {
        digamma(&next,m+1,4); sub(&weight,&next,&prev); scale(&weight,&weight,1,4); set(&prev,&next);
        collision4_value(&f,m); mul(&t,&f,&weight); add(mean,mean,&t); square(&t,&f); mul(&t,&t,&weight); add(norm,norm,&t);
    }
    clear(&prev); clear(&next); clear(&weight); clear(&f); clear(&t);
}
static void family_init(CollisionFamily *family,int base)
{
    memset(family,0,sizeof(*family)); family->base=base;
    for(int i=0;i<MAX_COLLISION_OBSERVATIONS;++i) {
        init(family->mean+i); init(family->norm+i); init(family->response+i);
        init_array(family->coupling[i],DIM); init_array(family->omega[i],DIM);
        init_array(family->gram[i],MAX_COLLISION_OBSERVATIONS);
    }
    for(int i=0;i<MAX_SHELL_DIMENSION;++i) init_array(family->basis[i],DIM);
    init(&family->collective); init(&family->capture); init(&family->missed); init(&family->normalized);
    init_array(family->prefix_collective,DIM); init_array(family->prefix_capture,DIM); init_array(family->prefix_missed,DIM);
}
static void family_clear(CollisionFamily *family)
{
    for(int i=0;i<MAX_COLLISION_OBSERVATIONS;++i) {
        clear(family->mean+i); clear(family->norm+i); clear(family->response+i);
        clear_array(family->coupling[i],DIM); clear_array(family->omega[i],DIM);
        clear_array(family->gram[i],MAX_COLLISION_OBSERVATIONS);
    }
    for(int i=0;i<MAX_SHELL_DIMENSION;++i) clear_array(family->basis[i],DIM);
    clear(&family->collective); clear(&family->capture); clear(&family->missed); clear(&family->normalized);
    clear_array(family->prefix_collective,DIM); clear_array(family->prefix_capture,DIM); clear_array(family->prefix_missed,DIM);
}
static void translated_collision_value(Interval *out,const CollisionCenteredTable *table,int multiplier,unsigned m)
{
    int residue=(int)((long long)multiplier*(m%(unsigned)table->modulus)%table->modulus);
    if(residue==0 || collision_table_gcd(residue,table->modulus)!=1) { rat(out,0,1); return; }
    int fiber=residue%table->base;
    rat(out,(long)table->centered_numerator[residue],(unsigned long)table->fiber_count[fiber]);
}
/* Native residue weights depend on the period, not the unit translation.
 * Evaluate each directed weight once, then apply it to every observation.
 * Each observation keeps the original accumulation and rounding order. */
static void translated_collision_statistics(CollisionFamily *family,const CollisionCenteredTable *table)
{
    Interval prev,next,weight,f,t;
    init(&prev); init(&next); init(&weight); init(&f); init(&t);
    for(int i=0;i<family->count;++i) { rat(family->mean+i,0,1); rat(family->norm+i,0,1); }
    digamma(&prev,1,(unsigned)table->modulus);
    for(unsigned m=1;m<=(unsigned)table->modulus;++m) {
        digamma(&next,m+1,(unsigned)table->modulus); sub(&weight,&next,&prev); scale(&weight,&weight,1,(unsigned)table->modulus); set(&prev,&next);
        for(int i=0;i<family->count;++i) {
            translated_collision_value(&f,table,family->multiplier[i],m);
            mul(&t,&f,&weight); add(family->mean+i,family->mean+i,&t);
            square(&t,&f); mul(&t,&t,&weight); add(family->norm+i,family->norm+i,&t);
        }
    }
    clear(&prev); clear(&next); clear(&weight); clear(&f); clear(&t);
}
static void translated_collision_pairs(CollisionFamily *family,const CollisionCenteredTable *table,unsigned j)
{
    unsigned q=(unsigned)table->modulus,period=q/gcd(q,j)*j;
    Interval prev,next,weight,f,row,t;
    init(&prev); init(&next); init(&weight); init(&f); init(&row); init(&t);
    for(int i=0;i<family->count;++i) rat(&family->coupling[i][j],0,1);
    digamma(&prev,1,period);
    for(unsigned m=1;m<=period;++m) {
        digamma(&next,m+1,period); sub(&weight,&next,&prev); scale(&weight,&weight,1,period); set(&prev,&next);
        rat(&row,(long)(m%j),j);
        for(int i=0;i<family->count;++i) {
            translated_collision_value(&f,table,family->multiplier[i],m);
            mul(&t,&f,&row); mul(&t,&t,&weight); add(&family->coupling[i][j],&family->coupling[i][j],&t);
        }
    }
    clear(&prev); clear(&next); clear(&weight); clear(&f); clear(&row); clear(&t);
}
static int exact_translation_orbit_rank(const CollisionCenteredTable *table,const int *units,int count)
{
    mpq_t matrix[MAX_COLLISION_OBSERVATIONS][MAX_COLLISION_OBSERVATIONS],factor,t;
    for(int i=0;i<MAX_COLLISION_OBSERVATIONS;++i) for(int j=0;j<MAX_COLLISION_OBSERVATIONS;++j) mpq_init(matrix[i][j]);
    mpq_inits(factor,t,NULL);
    for(int i=0;i<count;++i) for(int j=0;j<count;++j) {
        int residue=(int)((long long)units[i]*units[j]%table->modulus),fiber=residue%table->base;
        mpq_set_si(matrix[i][j],table->centered_numerator[residue],table->fiber_count[fiber]); mpq_canonicalize(matrix[i][j]);
    }
    int rank=0;
    for(int column=0;column<count && rank<count;++column) {
        int pivot=rank; while(pivot<count && mpq_sgn(matrix[pivot][column])==0) ++pivot;
        if(pivot==count) continue;
        if(pivot!=rank) for(int j=column;j<count;++j) mpq_swap(matrix[pivot][j],matrix[rank][j]);
        mpq_set(factor,matrix[rank][column]);
        for(int j=column;j<count;++j) mpq_div(matrix[rank][j],matrix[rank][j],factor);
        for(int i=0;i<count;++i) if(i!=rank && mpq_sgn(matrix[i][column])!=0) {
            mpq_set(factor,matrix[i][column]);
            for(int j=column;j<count;++j) { mpq_mul(t,factor,matrix[rank][j]); mpq_sub(matrix[i][j],matrix[i][j],t); }
        }
        ++rank;
    }
    mpq_clears(factor,t,NULL);
    for(int i=0;i<MAX_COLLISION_OBSERVATIONS;++i) for(int j=0;j<MAX_COLLISION_OBSERVATIONS;++j) mpq_clear(matrix[i][j]);
    return rank;
}
static int exact_uniform_residue_mean_zero(const CollisionCenteredTable *table)
{
    mpq_t sum,value; mpq_inits(sum,value,NULL);
    for(int residue=1;residue<table->modulus;++residue) {
        if(collision_table_gcd(residue,table->modulus)!=1) continue;
        int fiber=residue%table->base;
        mpq_set_si(value,table->centered_numerator[residue],table->fiber_count[fiber]);
        mpq_canonicalize(value); mpq_add(sum,sum,value);
    }
    int zero=mpq_sgn(sum)==0; mpq_clears(sum,value,NULL); return zero;
}
static void add_to_span(Run *r,CollisionFamily *owner,const Interval *vector,int label,int upper_rank)
{
    if(owner->projected_rank>=upper_rank) return;
    Interval residual[DIM],dot,t,norm;
    init_array(residual,DIM); init(&dot); init(&t); init(&norm);
    for(int j=r->first+1;j<=r->last;++j) set(residual+j,vector+j);
    for(int b=0;b<owner->projected_rank;++b) {
        rat(&dot,0,1);
        for(int j=r->first+1;j<=r->last;++j) { mul(&t,vector+j,owner->basis[b]+j); add(&dot,&dot,&t); }
        for(int j=r->first+1;j<=r->last;++j) { mul(&t,&dot,owner->basis[b]+j); sub(residual+j,residual+j,&t); }
    }
    for(int j=r->first+1;j<=r->last;++j) { square(&t,residual+j); add(&norm,&norm,&t); }
    if(mpfr_sgn(norm.lo)>0) {
        int b=owner->projected_rank++; owner->selected[b]=label;
        root(&r->audit,&norm,&norm);
        for(int j=r->first+1;j<=r->last;++j) divide(&r->audit,owner->basis[b]+j,residual+j,&norm);
    }
    clear_array(residual,DIM); clear(&dot); clear(&t); clear(&norm);
}
static void finish_span(Run *r,CollisionFamily *family)
{
    Interval dot,t;
    init(&dot); init(&t);
    for(int b=0;b<family->projected_rank;++b) {
        rat(&dot,0,1);
        for(int j=r->first+1;j<=r->last;++j) { mul(&t,r->frame[j].value+GAMMA,family->basis[b]+j); add(&dot,&dot,&t); }
        square(&t,&dot); add(&family->collective,&family->collective,&t);
    }
    divide(&r->audit,&family->capture,&family->collective,r->frame[r->last].value+BLOCK_GAIN);
    sub(&family->missed,r->frame[r->last].value+BLOCK_GAIN,&family->collective);
    mul(&t,r->frame[r->first].value+D,r->frame[r->last].value+D); divide(&r->audit,&family->normalized,&family->collective,&t);
    clear(&dot); clear(&t);
}
static void subspace_overlap_energy(Interval *out,const Run *r,const CollisionFamily *left,const CollisionFamily *right)
{
    Interval dot,t; init(&dot); init(&t); rat(out,0,1);
    for(int a=0;a<left->projected_rank;++a) for(int b=0;b<right->projected_rank;++b) {
        rat(&dot,0,1);
        for(int j=r->first+1;j<=r->last;++j) {
            mul(&t,left->basis[a]+j,right->basis[b]+j); add(&dot,&dot,&t);
        }
        square(&t,&dot); add(out,out,&t);
    }
    clear(&dot); clear(&t);
}
static void span_certificate(Interval *out,const Run *r,const CollisionFamily *span,int rank)
{
    Interval dot,t; init(&dot); init(&t); rat(out,0,1);
    for(int b=0;b<rank;++b) {
        rat(&dot,0,1);
        for(int j=r->first+1;j<=r->last;++j) {
            mul(&t,r->frame[j].value+GAMMA,span->basis[b]+j); add(&dot,&dot,&t);
        }
        square(&t,&dot); add(out,out,&t);
    }
    clear(&dot); clear(&t);
}
static void audit_span_orthonormal(Run *r,const CollisionFamily *span)
{
    Interval dot,t,zero,one; init(&dot); init(&t); init(&zero); init(&one); rat(&one,1,1);
    for(int a=0;a<span->projected_rank;++a) for(int b=0;b<=a;++b) {
        rat(&dot,0,1);
        for(int j=r->first+1;j<=r->last;++j) {
            mul(&t,span->basis[a]+j,span->basis[b]+j); add(&dot,&dot,&t);
        }
        equal(&r->audit,&dot,a==b?&one:&zero,"collision projected basis is orthonormal");
    }
    clear(&dot); clear(&t); clear(&zero); clear(&one);
}
static void vector_detection(Interval *out,const Run *r,const Interval *vector,const CollisionFamily *span)
{
    Interval dot,t; init(&dot); init(&t); rat(out,0,1);
    for(int b=0;b<span->projected_rank;++b) {
        rat(&dot,0,1);
        for(int j=r->first+1;j<=r->last;++j) { mul(&t,vector+j,span->basis[b]+j); add(&dot,&dot,&t); }
        square(&t,&dot); add(out,out,&t);
    }
    clear(&dot); clear(&t);
}
static void calculate_family_prefixes(Run *r,CollisionFamily *family)
{
    for(int end=r->first+1;end<=r->last;++end) {
        CollisionFamily prefix; family_init(&prefix,family->base);
        int prefix_dimension=end-r->first;
        int upper=family->finite_orbit_rank<prefix_dimension?family->finite_orbit_rank:prefix_dimension;
        for(int i=0;i<family->count;++i) {
            Interval truncated[DIM]; init_array(truncated,DIM);
            for(int j=r->first+1;j<=end;++j) set(truncated+j,&family->omega[i][j]);
            add_to_span(r,&prefix,truncated,family->multiplier[i],upper);
            clear_array(truncated,DIM);
        }
        prefix.projected_rank_exact=prefix.projected_rank==upper;
        family->prefix_rank[end]=prefix.projected_rank;
        family->prefix_rank_exact[end]=prefix.projected_rank_exact;
        Interval dot,t; init(&dot); init(&t);
        for(int b=0;b<prefix.projected_rank;++b) {
            rat(&dot,0,1);
            for(int j=r->first+1;j<=end;++j) { mul(&t,r->frame[j].value+GAMMA,prefix.basis[b]+j); add(&dot,&dot,&t); }
            square(&t,&dot); add(family->prefix_collective+end,family->prefix_collective+end,&t);
        }
        divide(&r->audit,family->prefix_capture+end,family->prefix_collective+end,r->frame[end].value+BLOCK_GAIN);
        sub(family->prefix_missed+end,r->frame[end].value+BLOCK_GAIN,family->prefix_collective+end);
        clear(&dot); clear(&t); family_clear(&prefix);
    }
}
static int calculate_collision_family(Run *r,CollisionFamily *family)
{
    CollisionCenteredTable table={0};
    if(!collision_centered_table_build(family->base,1,&table)) return 0;
    family->modulus=table.modulus;
    family->uniform_residue_mean_zero_exact=exact_uniform_residue_mean_zero(&table);
    check(&r->audit,family->uniform_residue_mean_zero_exact,"collision family exact uniform residue mean zero");
    for(int a=1;a<table.modulus;++a) if(collision_table_gcd(a,table.modulus)==1) family->multiplier[family->count++]=a;
    if(family->count>MAX_COLLISION_OBSERVATIONS) { collision_centered_table_free(&table); return 0; }
    family->finite_orbit_rank=exact_translation_orbit_rank(&table,family->multiplier,family->count);
    translated_collision_statistics(family,&table);
    for(int j=2;j<=r->last;++j) translated_collision_pairs(family,&table,(unsigned)j);
    for(int i=0;i<family->count;++i) {
        for(int j=r->first+1;j<=r->last;++j) {
            Interval t; init(&t);
            for(int k=2;k<=j;++k) { mul(&t,r->frame[j].direction+k,&family->coupling[i][k]); add(&family->omega[i][j],&family->omega[i][j],&t); }
            mul(&t,r->frame[j].value+GAMMA,&family->omega[i][j]); add(&family->response[i],&family->response[i],&t); clear(&t);
        }
    }
    for(int i=0;i<family->count;++i) for(int k=0;k<=i;++k) {
        Interval t; init(&t);
        for(int j=r->first+1;j<=r->last;++j) { mul(&t,&family->omega[i][j],&family->omega[k][j]); add(&family->gram[i][k],&family->gram[i][k],&t); }
        set(&family->gram[k][i],&family->gram[i][k]); clear(&t);
    }
    /* Recompute every observation from the two independently optimized
     * endpoints.  This audits both the shell cost H_ii and response h_i;
     * neither equality relies on the innovation coordinates above. */
    for(int i=0;i<family->count;++i) {
        Interval c4[DIM],c8[DIM],p4,p8,q,h,t;
        init_array(c4,DIM); init_array(c8,DIM);
        init(&p4); init(&p8); init(&q); init(&h); init(&t);
        solve(r,family->coupling[i],r->first,c4); solve(r,family->coupling[i],r->last,c8);
        for(int j=2;j<=r->first;++j) { mul(&t,c4+j,&family->coupling[i][j]); add(&p4,&p4,&t); }
        for(int j=2;j<=r->last;++j) { mul(&t,c8+j,&family->coupling[i][j]); add(&p8,&p8,&t); }
        sub(&q,&p8,&p4); equal(&r->audit,&q,&family->gram[i][i],"collision family endpoint and innovation costs agree");
        for(int j=2;j<=r->last;++j) { sub(&q,c8+j,c4+j); mul(&t,r->h+j,&q); add(&h,&h,&t); }
        equal(&r->audit,&h,&family->response[i],"collision family endpoint and innovation responses agree");
        clear_array(c4,DIM); clear_array(c8,DIM);
        clear(&p4); clear(&p8); clear(&q); clear(&h); clear(&t);
    }
    int shell=r->last-r->first;
    int upper=family->finite_orbit_rank<shell?family->finite_orbit_rank:shell;
    for(int i=0;i<family->count;++i) add_to_span(r,family,family->omega[i],family->multiplier[i],upper);
    family->projected_rank_exact=family->projected_rank==upper;
    finish_span(r,family); calculate_family_prefixes(r,family); collision_centered_table_free(&table); return 1;
}
static void linear(Interval *out,const Interval *coeff,int last,unsigned m)
{
    Interval t; init(&t); rat(out,0,1);
    for(int j=2;j<=last;++j) { scale(&t,coeff+j,(long)(m%(unsigned)j),(unsigned)j); add(out,out,&t); }
    clear(&t);
}
static void solve(Run *r,const Interval *rhs,int last,Interval *x)
{
    Interval a[TOP][DIM],pivot,t,u;
    for(int i=0;i<TOP;++i) init_array(a[i],DIM);
    init(&pivot); init(&t); init(&u); int n=last-1;
    for(int i=0;i<n;++i) {
        for(int j=0;j<n;++j) set(&a[i][j],&r->gram[i+2][j+2]);
        set(&a[i][n],rhs+i+2);
    }
    for(int k=0;k<n && !r->audit.failures;++k) {
        set(&pivot,&a[k][k]);
        for(int j=k;j<=n;++j) divide(&r->audit,&a[k][j],&a[k][j],&pivot);
        for(int i=k+1;i<n;++i) {
            set(&t,&a[i][k]);
            for(int j=k;j<=n;++j) { mul(&u,&t,&a[k][j]); sub(&a[i][j],&a[i][j],&u); }
        }
    }
    if(!r->audit.failures) for(int i=n-1;i>=0;--i) {
        set(x+i+2,&a[i][n]);
        for(int j=i+1;j<n;++j) { mul(&u,&a[i][j],x+j+2); sub(x+i+2,x+i+2,&u); }
        divide(&r->audit,x+i+2,x+i+2,&a[i][i]);
    }
    for(int i=2;i<=last;++i) {
        rat(&t,0,1);
        for(int j=2;j<=last;++j) { mul(&u,&r->gram[i][j],x+j); add(&t,&t,&u); }
        equal(&r->audit,&t,rhs+i,"independent original normal equation");
    }
    for(int i=0;i<TOP;++i) clear_array(a[i],DIM);
    clear(&pivot); clear(&t); clear(&u);
}
static void source(Run *r)
{
    const unsigned labels[]={9,7,13,11,21}, den[]={5,5,5,3,3};
    const int num[]={2,-1,-2,-1,-1};
    mpq_t eta[SUPPORT+1],c,t,z,mean,norm,closed;
    for(int m=0;m<=SUPPORT;++m) mpq_init(eta[m]);
    mpq_inits(c,t,z,mean,norm,closed,NULL);
    for(int i=0;i<5;++i) {
        unsigned j=labels[i]; mpq_set_si(c,num[i],den[i]); mpq_canonicalize(c);
        mpq_set_ui(t,j+1,1); mpq_mul(t,t,c); mpq_add(eta[j],eta[j],t);
        mpq_set_ui(t,j-1,1); mpq_mul(t,t,c); mpq_sub(eta[j-1],eta[j-1],t);
    }
    for(unsigned m=1;m<=SUPPORT;++m) {
        from_q(r->eta+m,eta[m]); mpq_set_ui(t,1,m*(m+1));
        mpq_mul(z,t,eta[m]); mpq_add(mean,mean,z); mpq_mul(z,z,eta[m]); mpq_add(norm,norm,z);
    }
    check(&r->audit,mpq_sgn(mean)==0,"exact origin mean zero");
    mpq_set_ui(t,262,225); check(&r->audit,mpq_equal(norm,t),"exact eta norm 262/225");
    for(int j=2;j<=r->last;++j) {
        mpq_set_ui(closed,0,1);
        for(unsigned m=1;m<=SUPPORT;++m) {
            mpq_set_ui(t,m%(unsigned)j,(unsigned)j*m*(m+1)); mpq_canonicalize(t);
            mpq_mul(t,t,eta[m]); mpq_add(r->raw[j],r->raw[j],t);
        }
        for(int i=0;i<5;++i) {
            mpq_set_si(c,num[i],den[i]*labels[i]); mpq_canonicalize(c);
            mpq_set_si(t,1-(labels[i]%(unsigned)j==0?j:0),(unsigned)j); mpq_canonicalize(t);
            mpq_mul(t,t,c); mpq_add(closed,closed,t);
        }
        check(&r->audit,mpq_equal(r->raw[j],closed),"exact raw origin divisor-reset identity");
        from_q(r->u+j,r->raw[j]);
    }
    for(int m=0;m<=SUPPORT;++m) mpq_clear(eta[m]);
    mpq_clears(c,t,z,mean,norm,closed,NULL);
}
static void run_init(Run *r,int first,int last)
{
    r->first=first; r->last=last; r->period=1;
    for(int j=0;j<DIM;++j) {
        init_array(r->gram[j],DIM); init_array(r->conditioned[j],DIM);
        init_array(r->frame[j].value,FIELDS); init_array(r->frame[j].target,DIM);
        init_array(r->frame[j].origin,DIM); init_array(r->frame[j].direction,DIM); mpq_init(r->raw[j]);
        if(j>=2 && j<=last) r->period=r->period/gcd(r->period,(unsigned)j)*(unsigned)j;
    }
    init_array(r->h,DIM); init_array(r->u,DIM); init_array(r->eta,SUPPORT+1);
}
static void run_clear(Run *r)
{
    for(int j=0;j<DIM;++j) {
        clear_array(r->gram[j],DIM); clear_array(r->conditioned[j],DIM);
        clear_array(r->frame[j].value,FIELDS); clear_array(r->frame[j].target,DIM);
        clear_array(r->frame[j].origin,DIM); clear_array(r->frame[j].direction,DIM); mpq_clear(r->raw[j]);
    }
    clear_array(r->h,DIM); clear_array(r->u,DIM); clear_array(r->eta,SUPPORT+1);
}
static void calculate(Run *r)
{
    Interval one,t,sqrt2,norm,coeff[DIM],logfactor,zero;
    init(&one); init(&t); init(&sqrt2); init(&norm); init_array(coeff,DIM); init(&logfactor); init(&zero);
    rat(&one,1,1); rat(&sqrt2,2,1); root(&r->audit,&sqrt2,&sqrt2);
    rat(&logfactor,r->first,1); mpfr_log(logfactor.lo,logfactor.lo,MPFR_RNDD); mpfr_log(logfactor.hi,logfactor.hi,MPFR_RNDU); add(&logfactor,&logfactor,&one);
    source(r);
    for(int j=2;j<=r->last;++j) {
        rat(r->h+j,j,1); mpfr_log(r->h[j].lo,r->h[j].lo,MPFR_RNDD); mpfr_log(r->h[j].hi,r->h[j].hi,MPFR_RNDU); scale(r->h+j,r->h+j,1,(unsigned)j);
        for(int k=2;k<=j;++k) { gram_entry(&r->gram[j][k],(unsigned)j,(unsigned)k); set(&r->gram[k][j],&r->gram[j][k]); }
    }
    for(int j=1;j<=r->last && !r->audit.failures;++j) {
        Frame *f=r->frame+j; Interval *v=f->value;
        solve(r,r->h,j,f->target); solve(r,r->u,j,f->origin);
        set(v+D,&one);
        for(int k=2;k<=j;++k) { mul(&t,f->target+k,r->h+k); sub(v+D,v+D,&t); }
        divide(&r->audit,v+CAPACITY,&one,v+D);
        if(j==1) continue;
        solve(r,r->gram[j],j-1,coeff);
        set(v+ROW_NORM,&r->gram[j][j]); set(v+CONDITIONED_TARGET,r->h+j); set(v+CONDITIONED_ORIGIN,r->u+j);
        for(int k=2;k<j;++k) {
            mul(&t,coeff+k,&r->gram[j][k]); sub(v+ROW_NORM,v+ROW_NORM,&t);
            mul(&t,coeff+k,r->h+k); sub(v+CONDITIONED_TARGET,v+CONDITIONED_TARGET,&t);
            mul(&t,coeff+k,r->u+k); sub(v+CONDITIONED_ORIGIN,v+CONDITIONED_ORIGIN,&t);
            sub(f->direction+k,&zero,coeff+k);
        }
        rat(f->direction+j,1,1); root(&r->audit,&norm,v+ROW_NORM);
        for(int k=2;k<=j;++k) divide(&r->audit,f->direction+k,f->direction+k,&norm);
        divide(&r->audit,v+GAMMA,v+CONDITIONED_TARGET,&norm);
        divide(&r->audit,v+CONDITIONED_ORIGIN,v+CONDITIONED_ORIGIN,&sqrt2);
        divide(&r->audit,v+OMEGA,v+CONDITIONED_ORIGIN,&norm);
        square(v+GAIN,v+GAMMA); mul(v+RESPONSE,v+GAMMA,v+OMEGA); square(v+COST,v+OMEGA);
        sub(v+CAPACITY_STEP,v+CAPACITY,r->frame[j-1].value+CAPACITY);
        sub(&t,r->frame[j-1].value+D,v+D); equal(&r->audit,&t,v+GAIN,"one-step gain from separate endpoint optimizers");
        mul(&t,r->frame[j-1].value+D,v+D); divide(&r->audit,&t,v+GAIN,&t);
        equal(&r->audit,&t,v+CAPACITY_STEP,"raw gain and normalized capacity cost agree");
        if(j<=r->first) continue;
        Interval *prev=r->frame[j-1].value;
        add(v+BLOCK_GAIN,prev+BLOCK_GAIN,v+GAIN); add(v+BLOCK_RESPONSE,prev+BLOCK_RESPONSE,v+RESPONSE); add(v+BLOCK_COST,prev+BLOCK_COST,v+COST);
        square(&t,v+RESPONSE); add(v+DIAGONAL,prev+DIAGONAL,&t);
        square(&t,v+BLOCK_RESPONSE); sub(v+CROSS,&t,v+DIAGONAL);
        if(mpfr_zero_p(v[BLOCK_COST].lo) && mpfr_zero_p(v[BLOCK_COST].hi)) rat(v+CERTIFICATE,0,1);
        else divide(&r->audit,v+CERTIFICATE,&t,v+BLOCK_COST);
        if(mpfr_zero_p(v[BLOCK_GAIN].lo) && mpfr_zero_p(v[BLOCK_GAIN].hi)) rat(v+CAPTURE,0,1);
        else divide(&r->audit,v+CAPTURE,v+CERTIFICATE,v+BLOCK_GAIN);
        sub(v+INVISIBLE,v+BLOCK_GAIN,v+CERTIFICATE);
        square(&t,r->frame[r->first].value+D); divide(&r->audit,v+NORMALIZED,v+CERTIFICATE,&t);
        mul(&t,r->frame[r->first].value+D,v+D); divide(&r->audit,v+ENDPOINT_NORMALIZED,v+CERTIFICATE,&t);
        mul(v+LOG_NORMALIZED,v+NORMALIZED,&logfactor);
        sub(&t,r->frame[r->first].value+D,v+D); equal(&r->audit,&t,v+BLOCK_GAIN,"full block gain telescopes");
        sub(&t,v+CAPACITY,r->frame[r->first].value+CAPACITY); mul(&t,&t,v+CAPTURE);
        equal(&r->audit,&t,v+ENDPOINT_NORMALIZED,"capacity capture normalization");
        /* Original-row Gram after conditioning on all rows <= first. */
        solve(r,r->gram[j],r->first,coeff);
        for(int k=r->first+1;k<=r->last;++k) {
            set(&r->conditioned[j][k],&r->gram[j][k]);
            for(int l=2;l<=r->first;++l) { mul(&t,coeff+l,&r->gram[l][k]); sub(&r->conditioned[j][k],&r->conditioned[j][k],&t); }
        }
    }
    for(int j=r->first+1;j<=r->last;++j) for(int k=r->first+1;k<j;++k)
        equal(&r->audit,&r->conditioned[j][k],&r->conditioned[k][j],"conditioned Gram symmetry");
    clear(&one); clear(&t); clear(&sqrt2); clear(&norm); clear_array(coeff,DIM); clear(&logfactor); clear(&zero);
}

/* All periodic objects use the COMPLETE infinite residue weights.
 * Finite eta is paired separately on addresses 1..21, never periodized. */
static void audit_period(Run *r)
{
    enum { RESIDUAL_NORM, RESIDUAL_MEAN, STEP_CAPACITY_NORM, SHELL_NORM,
           ORIGIN_NORM, PAIR, FINITE_PAIR, FINITE_ORIGIN, DIRECT_FIELDS };
    Interval sums[DIM][DIRECT_FIELDS], ortho[DIM][DIM], old[DIM][DIM];
    Interval rv[DIM],wv[DIM],ev[DIM],xv[DIM],prev,next,weight,one,t,z,g,zero,root2,total;
    for(int j=0;j<DIM;++j) { init_array(sums[j],DIRECT_FIELDS); init_array(ortho[j],DIM); init_array(old[j],DIM); }
    init_array(rv,DIM); init_array(wv,DIM); init_array(ev,DIM); init_array(xv,DIM);
    Interval *temps[]={&prev,&next,&weight,&one,&t,&z,&g,&zero,&root2,&total};
    for(unsigned i=0;i<sizeof(temps)/sizeof(*temps);++i) init(temps[i]);
    rat(&one,1,1); rat(&root2,2,1); root(&r->audit,&root2,&root2); digamma(&prev,1,r->period);
    for(unsigned m=1;m<=r->period && !r->audit.failures;++m) {
        digamma(&next,m+1,r->period); sub(&weight,&next,&prev); scale(&weight,&weight,1,r->period); set(&prev,&next);
        check(&r->audit,mpfr_sgn(weight.lo)>0,"positive complete residue weight"); add(&total,&total,&weight);
        for(int j=1;j<=r->last;++j) {
            Frame *f=r->frame+j; Interval *s=sums[j];
            linear(&t,f->target,j,m); sub(rv+j,&one,&t); divide(&r->audit,xv+j,rv+j,f->value+D);
            linear(wv+j,f->origin,j,m); divide(&r->audit,wv+j,wv+j,&root2);
            linear(ev+j,f->direction,j,m);
            square(&t,rv+j); mul(&t,&t,&weight); add(s+RESIDUAL_NORM,s+RESIDUAL_NORM,&t);
            mul(&t,rv+j,&weight); add(s+RESIDUAL_MEAN,s+RESIDUAL_MEAN,&t);
            for(int k=2;k<=j;++k) { scale(&t,rv+j,(long)(m%(unsigned)k),(unsigned)k); mul(&t,&t,&weight); add(&old[j][k],&old[j][k],&t); }
            if(j>1) {
                sub(&t,xv+j,xv+j-1); square(&t,&t); mul(&t,&t,&weight); add(s+STEP_CAPACITY_NORM,s+STEP_CAPACITY_NORM,&t);
                for(int k=2;k<=j;++k) { mul(&t,ev+j,ev+k); mul(&t,&t,&weight); add(&ortho[j][k],&ortho[j][k],&t); }
                sub(&t,rv+j-1,rv+j); mul(&z,f->value+GAMMA,ev+j); equal(&r->audit,&t,&z,"gain direction equals separate residual difference at each residue");
            }
            if(j<=r->first) continue;
            sub(&g,rv+r->first,rv+j); sub(&z,wv+j,wv+r->first);
            square(&t,&g); mul(&t,&t,&weight); add(s+SHELL_NORM,s+SHELL_NORM,&t);
            square(&t,&z); mul(&t,&t,&weight); add(s+ORIGIN_NORM,s+ORIGIN_NORM,&t);
            mul(&t,&g,&z); mul(&t,&t,&weight); add(s+PAIR,s+PAIR,&t);
        }
    }
    equal(&r->audit,&total,&one,"complete residue weights sum to one");
    for(unsigned m=1;m<=SUPPORT;++m) {
        scale(&weight,r->eta+m,1,(unsigned long)m*(m+1)); divide(&r->audit,&weight,&weight,&root2);
        for(int j=1;j<=r->last;++j) {
            linear(rv+j,r->frame[j].target,j,m); linear(wv+j,r->frame[j].origin,j,m); divide(&r->audit,wv+j,wv+j,&root2);
            if(j<=r->first) continue;
            sub(&t,rv+j,rv+r->first); mul(&t,&t,&weight); add(&sums[j][FINITE_PAIR],&sums[j][FINITE_PAIR],&t);
            sub(&t,wv+j,wv+r->first); mul(&t,&t,&weight); add(&sums[j][FINITE_ORIGIN],&sums[j][FINITE_ORIGIN],&t);
        }
    }
    for(int j=1;j<=r->last;++j) {
        Interval *v=r->frame[j].value,*s=sums[j];
        equal(&r->audit,s+RESIDUAL_NORM,v+D,"complete residual norm agrees with optimizer energy");
        equal(&r->audit,s+RESIDUAL_MEAN,v+D,"complete residual mean agrees with energy");
        for(int k=2;k<=j;++k) {
            equal(&r->audit,&old[j][k],&zero,"all old constraints retained");
            equal(&r->audit,&ortho[j][k],j==k?&one:&zero,"ordered directions are orthonormal in infinite norm");
        }
        if(j>1) equal(&r->audit,s+STEP_CAPACITY_NORM,v+CAPACITY_STEP,"complete normalized correction cost");
        if(j<=r->first) continue;
        equal(&r->audit,s+SHELL_NORM,v+BLOCK_GAIN,"complete direct block gain");
        equal(&r->audit,s+ORIGIN_NORM,v+BLOCK_COST,"complete projected-origin cost");
        equal(&r->audit,s+PAIR,v+BLOCK_RESPONSE,"complete periodic signed response");
        equal(&r->audit,s+FINITE_PAIR,v+BLOCK_RESPONSE,"unperiodized finite origin signed response");
        equal(&r->audit,s+FINITE_ORIGIN,v+BLOCK_COST,"finite origin pairing equals full projection cost");
    }
    for(int j=0;j<DIM;++j) { clear_array(sums[j],DIRECT_FIELDS); clear_array(ortho[j],DIM); clear_array(old[j],DIM); }
    clear_array(rv,DIM); clear_array(wv,DIM); clear_array(ev,DIM); clear_array(xv,DIM);
    for(unsigned i=0;i<sizeof(temps)/sizeof(*temps);++i) clear(temps[i]);
}

static void emit(FILE *f,const char *key,const Interval *a,int comma)
{
    fprintf(f,"%s\"%s\":{\"lo\":\"",comma?",":"",key);
    mpfr_out_str(f,10,42,a->lo,MPFR_RNDD); fputs("\",\"hi\":\"",f);
    mpfr_out_str(f,10,42,a->hi,MPFR_RNDU); fputs("\"}",f);
}
static void emit_coeff(FILE *out,const char *name,const Interval *a,int last)
{
    fprintf(out,",\"%s\":[",name);
    for(int k=2;k<=last;++k) { fprintf(out,"%s{\"clock\":%d,",k>2?",":"",k); emit(out,"coefficient",a+k,0); fputc('}',out); }
    fputc(']',out);
}
static void output(Run *r,FILE *out,int json)
{
    static const char *names[FIELDS]={
        "D","capacity","conditioned_row_norm","conditioned_target","conditioned_origin_psi",
        "gamma","omega_psi","step_gain","signed_origin_contribution_psi","step_origin_cost_psi","capacity_increment",
        "block_gain","block_response_psi","block_cost_psi","certificate_L","capture_fraction","invisible_gain",
        "L_over_D_first_squared","L_over_D_first_D_last","one_plus_log_first_L_over_D_first_squared",
        "response_square_diagonal","response_square_cross"
    };
    if(json) {
        fprintf(out,"{\"schema\":\"nfield.native-refinement.v1\",\"status\":\"PASS\",\"first\":%d,\"last\":%d,\"period\":%u,\"precision_bits\":256,\"mpfr_version\":\"%s\",\"gmp_version\":\"%s\",\"observation_truncation\":false,\"complete_period_audit\":%s,\"uniform_lower_bound_proved\":false,\"origin\":\"psi=T4*d3; eta=sqrt(2)*psi\",\"checks\":%u,\"failures\":%u,\"frames\":[",r->first,r->last,r->period,mpfr_get_version(),gmp_version,r->last<=8?"true":"false",r->audit.checks,r->audit.failures);
        for(int j=1;j<=r->last;++j) {
            Frame *f=r->frame+j;
            fprintf(out,"%s{\"N\":%d,",j>1?",":"",j); emit(out,names[D],f->value+D,0); emit(out,names[CAPACITY],f->value+CAPACITY,1);
            if(j>1) {
                fputs(",\"raw_origin_eta\":\"",out); mpq_out_str(out,10,r->raw[j]); fputc('"',out);
                fputs(",\"raw_reset_pulses\":[",out);
                const int pulses[]={7,9,11,13,21}; int count=0;
                for(int i=0;i<5;++i) if(pulses[i]%j==0) fprintf(out,"%s%d",count++?",":"",pulses[i]);
                fputc(']',out);
                for(int k=ROW_NORM;k<=CAPACITY_STEP;++k) emit(out,names[k],f->value+k,1);
            }
            if(j>r->first) for(int k=BLOCK_GAIN;k<FIELDS;++k) emit(out,names[k],f->value+k,1);
            emit_coeff(out,"target_projection",f->target,j); emit_coeff(out,"eta_projection",f->origin,j); emit_coeff(out,"unit_direction",f->direction,j);
            fputc('}',out);
        }
        fputs("],\"raw_gram\":[",out);
        for(int j=2;j<=r->last;++j) for(int k=2;k<=j;++k) {
            fprintf(out,"%s{\"j\":%d,\"k\":%d,",j==2 && k==2?"":",",j,k);
            emit(out,"value",&r->gram[j][k],0); fputc('}',out);
        }
        fputs("],\"conditioned_gram\":[",out);
        for(int j=r->first+1;j<=r->last;++j) for(int k=r->first+1;k<=r->last;++k) {
            fprintf(out,"%s{\"j\":%d,\"k\":%d,",j==r->first+1 && k==r->first+1?"":",",j,k);
            emit(out,"value",&r->conditioned[j][k],0); fputc('}',out);
        }
        fputs("],\"signed_response_pairs\":[",out); int count=0; Interval t; init(&t);
        for(int j=r->first+1;j<=r->last;++j) for(int k=j+1;k<=r->last;++k) {
            mul(&t,r->frame[j].value+RESPONSE,r->frame[k].value+RESPONSE); scale(&t,&t,2,1);
            fprintf(out,"%s{\"j\":%d,\"k\":%d,",count++?",":"",j,k); emit(out,"twice_product",&t,0); fputc('}',out);
        }
        clear(&t); fputs("]}\n",out);
    } else {
        fprintf(out,"Native refinement: %d -> %d; full infinite norm; period=%u; 256-bit intervals\n",r->first,r->last,r->period);
        fputs(" N      D_N              C_N          signed origin step       block capture\n",out);
        for(int j=1;j<=r->last;++j) {
            Interval *v=r->frame[j].value;
            mpfr_fprintf(out,"%2d  %.12RNf  %.12RNf",j,v[D].lo,v[CAPACITY].lo);
            if(j>r->first) mpfr_fprintf(out,"   % .12RNf          %.9RNf",v[RESPONSE].lo,v[CAPTURE].lo);
            fputc('\n',out);
        }
        Interval *v=r->frame[r->last].value;
        mpfr_fprintf(out,"Block response=% .15RNf cost=%.15RNf L=%.15RNf gain=%.15RNf\n",v[BLOCK_RESPONSE].lo,v[BLOCK_COST].lo,v[CERTIFICATE].lo,v[BLOCK_GAIN].lo);
        mpfr_fprintf(out,"(1+log first)*L/D_first^2=%.15RNf\n",v[LOG_NORMALIZED].lo);
        fprintf(out,"PASS: %u checks; finite diagnostic; uniform lower bound OPEN.\n",r->audit.checks);
    }
}

int native_refinement_trace(int first,int last,FILE *out,int json)
{
    if(!out || first<1 || last>TOP || first>=last) {
        fprintf(stderr,"native-refinement requires 1 <= first < last <= 16\n"); return 1;
    }
    Run *r=calloc(1,sizeof(*r));
    if(!r) { fprintf(stderr,"native-refinement: allocation failed\n"); return 1; }
    run_init(r,first,last); calculate(r); if(!r->audit.failures && last<=8) audit_period(r);
    int failed=r->audit.failures!=0;
    if(failed) fprintf(stderr,"native-refinement FAILED: %s (%u failed checks)\n",r->audit.first_error,r->audit.failures);
    else output(r,out,json);
    if(ferror(out)) { fprintf(stderr,"native-refinement: output write failed\n"); failed=1; }
    run_clear(r); free(r); mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE); return failed;
}

int native_refinement_collision4_calibration(FILE *out,int json)
{
    Run *r=calloc(1,sizeof(*r));
    Interval u[DIM],p4,p8,h,hcheck,q,qcheck,j,capture,normalized,t,mean,norm,omega[DIM];
    if(!out || !r) { fprintf(stderr,"native-refinement collision4: allocation or output failed\n"); free(r); return 1; }
    for(int k=0;k<DIM;++k) { init(u+k); init(omega+k); }
    init(&p4); init(&p8); init(&h); init(&hcheck); init(&q); init(&qcheck); init(&j); init(&capture); init(&normalized); init(&t); init(&mean); init(&norm);
    run_init(r,4,8); calculate(r); if(!r->audit.failures) audit_period(r);
    collision4_mean_and_norm(&mean,&norm);
    check(&r->audit,mpfr_sgn(mean.lo)>0,"collision4 centered table has positive native mean");
    check(&r->audit,mpfr_sgn(norm.lo)>0,"collision4 centered table has positive native norm");
    for(int k=2;k<=8;++k) collision4_pair(u+k,(unsigned)k);
    solve(r,u,4,r->frame[4].origin); /* temporary endpoint projection coefficients */
    for(int k=2;k<=4;++k) { mul(&t,r->frame[4].origin+k,u+k); add(&p4,&p4,&t); }
    solve(r,u,8,r->frame[8].origin);
    for(int k=2;k<=8;++k) { mul(&t,r->frame[8].origin+k,u+k); add(&p8,&p8,&t); }
    sub(&q,&p8,&p4);
    check(&r->audit,mpfr_sgn(q.lo)>0,"collision4 shell projection has positive norm");
    for(int k=2;k<=8;++k) {
        mul(&t,r->frame[8].target+k,u+k); add(&h,&h,&t);
        if(k<=4) { mul(&t,r->frame[4].target+k,u+k); sub(&h,&h,&t); }
    }
    for(int k=5;k<=8;++k) {
        for(int l=2;l<=k;++l) { mul(&t,r->frame[k].direction+l,u+l); add(omega+k,omega+k,&t); }
        mul(&t,r->frame[k].value+GAMMA,omega+k); add(&hcheck,&hcheck,&t);
        square(&t,omega+k); add(&qcheck,&qcheck,&t);
    }
    equal(&r->audit,&h,&hcheck,"collision4 endpoint and innovation responses agree");
    equal(&r->audit,&q,&qcheck,"collision4 endpoint and innovation costs agree");
    square(&j,&h); divide(&r->audit,&j,&j,&q);
    divide(&r->audit,&capture,&j,r->frame[8].value+BLOCK_GAIN);
    mul(&t,r->frame[4].value+D,r->frame[8].value+D); divide(&r->audit,&normalized,&j,&t);
    int failed=r->audit.failures!=0;
    if(failed) fprintf(stderr,"native-refinement collision4 FAILED: %s (%u failed checks)\n",r->audit.first_error,r->audit.failures);
    else if(json) {
        fprintf(out,"{\"schema\":\"nfield.native-refinement.collision4-calibration.v1\",\"status\":\"PASS\",\"first\":4,\"last\":8,\"period\":840,\"precision_bits\":256,\"extension\":\"centered base-2 lag-one table; zero off units\",\"checks\":%u,\"failures\":0",r->audit.checks);
        emit(out,"native_mean",&mean,1); emit(out,"native_norm_squared",&norm,1); emit(out,"shell_projection_norm_squared",&q,1); emit(out,"signed_response",&h,1); emit(out,"certificate_J",&j,1); emit(out,"capture_fraction",&capture,1); emit(out,"normalized_certificate",&normalized,1);
        fputs(",\"innovations\":[",out);
        for(int k=5;k<=8;++k) { fprintf(out,"%s{\"clock\":%d,",k>5?",":"",k); emit(out,"omega",omega+k,0); emit(out,"gamma",r->frame[k].value+GAMMA,1); mul(&t,omega+k,r->frame[k].value+GAMMA); emit(out,"signed_contribution",&t,1); fputc('}',out); }
        fputs("]}\n",out);
    } else {
        mpfr_fprintf(out,"Collision4 calibration: 4 -> 8; complete infinite native norm; period=840\n");
        mpfr_fprintf(out,"native mean=%.15RNf norm^2=%.15RNf\n",mean.lo,norm.lo);
        mpfr_fprintf(out,"shell cost=%.15RNf response=% .15RNf J=%.15RNf capture=%.9RNf normalized=%.15RNf\n",q.lo,h.lo,j.lo,capture.lo,normalized.lo);
        for(int k=5;k<=8;++k) { mul(&t,omega+k,r->frame[k].value+GAMMA); mpfr_fprintf(out,"clock %d omega=% .15RNf signed=% .15RNf\n",k,omega[k].lo,t.lo); }
        fprintf(out,"PASS: %u checks; finite calibration, no lower bound proved.\n",r->audit.checks);
    }
    if(ferror(out)) failed=1;
    for(int k=0;k<DIM;++k) { clear(u+k); clear(omega+k); }
    clear(&p4); clear(&p8); clear(&h); clear(&hcheck); clear(&q); clear(&qcheck); clear(&j); clear(&capture); clear(&normalized); clear(&t); clear(&mean); clear(&norm);
    run_clear(r); free(r); mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE); return failed;
}

static void emit_family(FILE *out,const Run *r,const CollisionFamily *family,int comma)
{
    fprintf(out,"%s{\"base\":%d,\"modulus\":%d,\"translations\":%d,\"uniform_residue_mean_zero_exact\":%s,\"finite_orbit_rank\":%d,\"projected_shell_rank\":%d,\"projected_rank_exact\":%s,\"selected_multipliers\":[",
            comma?",":"",family->base,family->modulus,family->count,family->uniform_residue_mean_zero_exact?"true":"false",family->finite_orbit_rank,family->projected_rank,family->projected_rank_exact?"true":"false");
    for(int b=0;b<family->projected_rank;++b) fprintf(out,"%s%d",b?",":"",family->selected[b]);
    fputc(']',out); emit(out,"collective_certificate",&family->collective,1); emit(out,"capture_fraction",&family->capture,1);
    emit(out,"missed_gain",&family->missed,1); emit(out,"normalized_certificate",&family->normalized,1);
    fputs(",\"observations\":[",out);
    for(int i=0;i<family->count;++i) {
        fprintf(out,"%s{\"multiplier\":%d,",i?",":"",family->multiplier[i]);
        emit(out,"native_mean",family->mean+i,0); emit(out,"native_norm_squared",family->norm+i,1); emit(out,"response",family->response+i,1);
        fputs(",\"omega\":[",out);
        for(int j=r->first+1;j<=r->last;++j) { fprintf(out,"%s{\"clock\":%d,",j>r->first+1?",":"",j); emit(out,"value",&family->omega[i][j],0); fputc('}',out); }
        fputs("]}",out);
    }
    fputs("],\"observation_gram\":[",out); int entries=0;
    for(int i=0;i<family->count;++i) for(int k=0;k<=i;++k) {
        fprintf(out,"%s{\"left_multiplier\":%d,\"right_multiplier\":%d,",entries++?",":"",family->multiplier[i],family->multiplier[k]);
        emit(out,"value",&family->gram[i][k],0); fputc('}',out);
    }
    fputs("],\"prefixes\":[",out);
    for(int end=r->first+1;end<=r->last;++end) {
        fprintf(out,"%s{\"last\":%d,\"projected_rank\":%d,\"projected_rank_exact\":%s,",end>r->first+1?",":"",end,family->prefix_rank[end],family->prefix_rank_exact[end]?"true":"false");
        emit(out,"collective_certificate",family->prefix_collective+end,0);
        emit(out,"capture_fraction",family->prefix_capture+end,1);
        emit(out,"missed_gain",family->prefix_missed+end,1); fputc('}',out);
    }
    fputs("]}",out);
}

int native_refinement_collision_families(int first,int last,FILE *out,int json)
{
    Run *r=calloc(1,sizeof(*r));
    CollisionFamily base2,base3,base5,base7,combined,extended;
    if(!out || !r || first<1 || last>TOP || first>=last || last-first>MAX_SHELL_DIMENSION) { fprintf(stderr,"native-refinement collision-families: require 1 <= first < last <= 16\n"); free(r); return 1; }
    family_init(&base2,2); family_init(&base3,3); family_init(&base5,5); family_init(&base7,7);
    family_init(&combined,0); family_init(&extended,0);
    run_init(r,first,last); calculate(r); if(!r->audit.failures && last<=8) audit_period(r);
    if(!r->audit.failures && (!calculate_collision_family(r,&base2) || !calculate_collision_family(r,&base3) || !calculate_collision_family(r,&base5)))
        check(&r->audit,0,"collision centered table construction");
    int shell=last-first;
    for(int i=0;i<base2.count;++i) add_to_span(r,&combined,base2.omega[i],200+base2.multiplier[i],shell);
    int rank_at_4=combined.projected_rank;
    for(int i=0;i<base3.count;++i) add_to_span(r,&combined,base3.omega[i],300+base3.multiplier[i],shell);
    int rank_at_36=combined.projected_rank;
    for(int i=0;i<base5.count;++i) add_to_span(r,&combined,base5.omega[i],500+base5.multiplier[i],shell);
    int rank_at_900=combined.projected_rank;
    int tower_finite_rank=base2.finite_orbit_rank+base3.finite_orbit_rank+base5.finite_orbit_rank;
    int tower_upper=tower_finite_rank<shell?tower_finite_rank:shell;
    combined.projected_rank_exact=combined.projected_rank==tower_upper;
    finish_span(r,&combined);
    audit_span_orthonormal(r,&base2); audit_span_orthonormal(r,&base3);
    audit_span_orthonormal(r,&base5); audit_span_orthonormal(r,&combined);
    Interval overlap_4_9,overlap_4_25,overlap_9_25,integer;
    Interval certificate_4,certificate_36,certificate_900,marginal_9,marginal_25,interaction_4_9;
    Interval blind[DIM],blind_norm,blind_response,dot,t;
    init(&overlap_4_9); init(&overlap_4_25); init(&overlap_9_25); init(&integer);
    init(&certificate_4); init(&certificate_36); init(&certificate_900);
    init(&marginal_9); init(&marginal_25); init(&interaction_4_9);
    init_array(blind,DIM); init(&blind_norm); init(&blind_response); init(&dot); init(&t);
    subspace_overlap_energy(&overlap_4_9,r,&base2,&base3);
    subspace_overlap_energy(&overlap_4_25,r,&base2,&base5);
    subspace_overlap_energy(&overlap_9_25,r,&base3,&base5);
    check(&r->audit,collision_table_gcd(4,9)==1 && collision_table_gcd(36,25)==1,"CRT tower factors are coprime");
    check(&r->audit,mpfr_sgn(overlap_4_9.lo)>0,"native projection creates positive q4-q9 overlap");
    if(base5.projected_rank==shell) {
        rat(&integer,base2.projected_rank,1); equal(&r->audit,&overlap_4_25,&integer,"full q25 shell contains q4 projected layer");
        rat(&integer,base3.projected_rank,1); equal(&r->audit,&overlap_9_25,&integer,"full q25 shell contains q9 projected layer");
    }
    span_certificate(&certificate_4,r,&combined,rank_at_4);
    span_certificate(&certificate_36,r,&combined,rank_at_36);
    span_certificate(&certificate_900,r,&combined,rank_at_900);
    sub(&marginal_9,&certificate_36,&certificate_4);
    sub(&marginal_25,&certificate_900,&certificate_36);
    sub(&interaction_4_9,&certificate_36,&certificate_4); sub(&interaction_4_9,&interaction_4_9,&base3.collective);
    equal(&r->audit,&certificate_4,&base2.collective,"first CRT layer certificate agrees with q4 family");
    equal(&r->audit,&certificate_900,&combined.collective,"full CRT tower certificate agrees with combined family");
    int blind_codimension=shell-combined.projected_rank;
    int has_target_blind_direction=blind_codimension==1 && mpfr_sgn(combined.missed.lo)>0;
    if(has_target_blind_direction) {
        for(int j=first+1;j<=last;++j) set(blind+j,r->frame[j].value+GAMMA);
        for(int b=0;b<combined.projected_rank;++b) {
            rat(&dot,0,1);
            for(int j=first+1;j<=last;++j) { mul(&t,r->frame[j].value+GAMMA,combined.basis[b]+j); add(&dot,&dot,&t); }
            for(int j=first+1;j<=last;++j) { mul(&t,&dot,combined.basis[b]+j); sub(blind+j,blind+j,&t); }
        }
        for(int j=first+1;j<=last;++j) { square(&t,blind+j); add(&blind_norm,&blind_norm,&t); }
        equal(&r->audit,&blind_norm,&combined.missed,"blind target component norm equals missed gain");
        root(&r->audit,&blind_norm,&blind_norm);
        for(int j=first+1;j<=last;++j) divide(&r->audit,blind+j,blind+j,&blind_norm);
        for(int j=first+1;j<=last;++j) { mul(&t,r->frame[j].value+GAMMA,blind+j); add(&blind_response,&blind_response,&t); }
        equal(&r->audit,&blind_response,&blind_norm,"oriented blind direction response equals residual norm");
    }
    int extend_with_49=blind_codimension>0;
    int rank_at_44100=rank_at_900;
    Interval blind_detection_49; init(&blind_detection_49);
    if(extend_with_49) {
        if(!calculate_collision_family(r,&base7)) check(&r->audit,0,"modulus-49 centered table construction");
        check(&r->audit,base7.finite_orbit_rank==18,"base-seven exact finite rank");
        for(int i=0;i<base2.count;++i) add_to_span(r,&extended,base2.omega[i],200+base2.multiplier[i],shell);
        for(int i=0;i<base3.count;++i) add_to_span(r,&extended,base3.omega[i],300+base3.multiplier[i],shell);
        for(int i=0;i<base5.count;++i) add_to_span(r,&extended,base5.omega[i],500+base5.multiplier[i],shell);
        for(int i=0;i<base7.count;++i) add_to_span(r,&extended,base7.omega[i],700+base7.multiplier[i],shell);
        rank_at_44100=extended.projected_rank;
        int extended_finite_rank=tower_finite_rank+base7.finite_orbit_rank;
        int extended_upper=extended_finite_rank<shell?extended_finite_rank:shell;
        extended.projected_rank_exact=extended.projected_rank==extended_upper;
        finish_span(r,&extended); audit_span_orthonormal(r,&base7); audit_span_orthonormal(r,&extended);
        if(has_target_blind_direction) {
            vector_detection(&blind_detection_49,r,blind,&base7);
            if(base7.projected_rank==shell) { rat(&integer,1,1); equal(&r->audit,&blind_detection_49,&integer,"q49 layer detects the normalized blind direction completely"); }
        }
        if(extended.projected_rank==shell) equal(&r->audit,&extended.collective,r->frame[last].value+BLOCK_GAIN,"extended CRT tower reconstructs shell gain");
    }
    check(&r->audit,base2.finite_orbit_rank==1,"base-two exact finite rank");
    check(&r->audit,base3.finite_orbit_rank==2,"base-three exact finite rank");
    check(&r->audit,base5.finite_orbit_rank==8,"base-five exact finite rank");
    if(base5.projected_rank==shell) equal(&r->audit,&base5.collective,r->frame[last].value+BLOCK_GAIN,"full-rank base-five family reconstructs shell gain");
    if(combined.projected_rank==shell) equal(&r->audit,&combined.collective,r->frame[last].value+BLOCK_GAIN,"combined family reconstructs shell gain");
    Interval q4mean,q4norm,q4pair;
    init(&q4mean); init(&q4norm); init(&q4pair); collision4_mean_and_norm(&q4mean,&q4norm);
    equal(&r->audit,&q4mean,&base2.mean[0],"generic base-two mean agrees with collision4 control");
    equal(&r->audit,&q4norm,&base2.norm[0],"generic base-two norm agrees with collision4 control");
    for(int j=2;j<=last;++j) { collision4_pair(&q4pair,(unsigned)j); equal(&r->audit,&q4pair,&base2.coupling[0][j],"generic base-two row pairing agrees with collision4 control"); }
    clear(&q4mean); clear(&q4norm); clear(&q4pair);
    int failed=r->audit.failures!=0;
    if(failed) fprintf(stderr,"native-refinement collision-families FAILED: %s (%u failed checks)\n",r->audit.first_error,r->audit.failures);
    else if(json) {
        fprintf(out,"{\"schema\":\"nfield.native-refinement.collision-families.v1\",\"status\":\"PASS\",\"first\":%d,\"last\":%d,\"period\":%u,\"precision_bits\":256,\"complete_period_audit\":%s,\"extension\":\"fiber-centered lag-one tables; zero off units; all unit translations\",\"checks\":%u,\"failures\":0,\"families\":[",first,last,r->period,last<=8?"true":"false",r->audit.checks);
        emit_family(out,r,&base2,0); emit_family(out,r,&base3,1); emit_family(out,r,&base5,1); if(extend_with_49) emit_family(out,r,&base7,1);
        fprintf(out,"],\"combined\":{\"finite_tower_rank\":%d,\"projected_shell_rank\":%d,\"projected_rank_exact\":%s,\"selected_observations\":[",tower_finite_rank,combined.projected_rank,combined.projected_rank_exact?"true":"false");
        for(int b=0;b<combined.projected_rank;++b) {
            int code=combined.selected[b];
            fprintf(out,"%s{\"base\":%d,\"multiplier\":%d}",b?",":"",code/100,code%100);
        }
        fputc(']',out);
        emit(out,"collective_certificate",&combined.collective,1); emit(out,"capture_fraction",&combined.capture,1); emit(out,"missed_gain",&combined.missed,1); emit(out,"normalized_certificate",&combined.normalized,1);
        fprintf(out,",\"blind_codimension\":%d",blind_codimension);
        if(has_target_blind_direction) {
            emit(out,"blind_target_response",&blind_response,1); fputs(",\"blind_direction\":[",out);
            for(int j=first+1;j<=last;++j) { fprintf(out,"%s{\"clock\":%d,",j>first+1?",":"",j); emit(out,"coefficient",blind+j,0); fputc('}',out); }
            fputc(']',out);
        }
        fprintf(out,"},\"profinite_tower\":{\"quotients\":[1,4,36,900],\"haar_cross_layer_orthogonal_exact\":true,\"native_union_ranks\":[%d,%d,%d],\"native_rank_increments\":[%d,%d,%d],\"cumulative_certificates\":[",
                rank_at_4,rank_at_36,rank_at_900,rank_at_4,rank_at_36-rank_at_4,rank_at_900-rank_at_36);
        fputs("{\"quotient\":4,",out); emit(out,"value",&certificate_4,0); fputs("},{\"quotient\":36,",out); emit(out,"value",&certificate_36,0); fputs("},{\"quotient\":900,",out); emit(out,"value",&certificate_900,0); fputs("}],\"marginal_certificates\":[",out);
        fputs("{\"adjoined_modulus\":4,",out); emit(out,"value",&certificate_4,0); fputs("},{\"adjoined_modulus\":9,",out); emit(out,"value",&marginal_9,0); fputs("},{\"adjoined_modulus\":25,",out); emit(out,"value",&marginal_25,0); fputs("}]",out);
        emit(out,"q4_q9_interaction_surplus",&interaction_4_9,1);
        fputs(",\"native_cross_layer_overlap\":[",out);
        fputs("{\"left_modulus\":4,\"right_modulus\":9,",out); emit(out,"hilbert_schmidt_squared",&overlap_4_9,0); fputs("},",out);
        fputs("{\"left_modulus\":4,\"right_modulus\":25,",out); emit(out,"hilbert_schmidt_squared",&overlap_4_25,0); fputs("},",out);
        fputs("{\"left_modulus\":9,\"right_modulus\":25,",out); emit(out,"hilbert_schmidt_squared",&overlap_9_25,0); fputs("}]}",out);
        if(extend_with_49) {
            fprintf(out,",\"extension_49\":{\"quotient\":44100,\"adjoined_modulus\":49,\"finite_layer_rank\":%d,\"projected_layer_rank\":%d,\"projected_rank_exact\":%s,\"extended_tower_rank\":%d,\"rank_increment\":%d",
                    base7.finite_orbit_rank,base7.projected_rank,base7.projected_rank_exact?"true":"false",rank_at_44100,rank_at_44100-rank_at_900);
            emit(out,"collective_certificate",&extended.collective,1); emit(out,"capture_fraction",&extended.capture,1); emit(out,"missed_gain",&extended.missed,1);
            if(has_target_blind_direction) emit(out,"prior_blind_detection_fraction",&blind_detection_49,1);
            fputc('}',out);
        }
        fputs("}\n",out);
    } else {
        fprintf(out,"Collision translated families on native shell %d -> %d\n",first,last);
        const CollisionFamily *families[]={&base2,&base3,&base5};
        for(unsigned i=0;i<sizeof(families)/sizeof(*families);++i)
            mpfr_fprintf(out,"q=%d translations=%d finite-rank=%d projected-rank=%d capture=%.12RNf certificate=%.15RNf missed=%.15RNf\n",
                         families[i]->modulus,families[i]->count,families[i]->finite_orbit_rank,families[i]->projected_rank,families[i]->capture.lo,families[i]->collective.lo,families[i]->missed.lo);
        for(int end=first+1;end<=last;++end)
            mpfr_fprintf(out,"  q=9 prefix %d->%d rank=%d capture=%.12RNf certificate=%.15RNf missed=%.15RNf\n",
                         first,end,base3.prefix_rank[end],base3.prefix_capture[end].lo,base3.prefix_collective[end].lo,base3.prefix_missed[end].lo);
        mpfr_fprintf(out,"combined projected-rank=%d capture=%.12RNf certificate=%.15RNf\n",combined.projected_rank,combined.capture.lo,combined.collective.lo);
        fprintf(out,"CRT tower 1|4|36|900: exact Haar cross-layer overlap=0; native union ranks=%d,%d,%d\n",rank_at_4,rank_at_36,rank_at_900);
        mpfr_fprintf(out,"native overlap energy q4/q9=%.15RNf q4/q25=%.15RNf q9/q25=%.15RNf\n",overlap_4_9.lo,overlap_4_25.lo,overlap_9_25.lo);
        mpfr_fprintf(out,"tower certificates q4=%.15RNf q4+q9=%.15RNf full=%.15RNf; q4/q9 surplus=% .15RNf\n",certificate_4.lo,certificate_36.lo,certificate_900.lo,interaction_4_9.lo);
        if(has_target_blind_direction) {
            mpfr_fprintf(out,"one-dimensional blind target response=%.15RNf; signed clock coordinates:",blind_response.lo);
            for(int j=first+1;j<=last;++j) mpfr_fprintf(out," %d:% .9RNf",j,blind[j].lo);
            fputc('\n',out);
        }
        if(extend_with_49)
            mpfr_fprintf(out,"adjoin q49: finite-rank=%d projected-rank=%d extended-rank=%d capture=%.12RNf prior-blind-detection=%.12RNf\n",base7.finite_orbit_rank,base7.projected_rank,rank_at_44100,extended.capture.lo,blind_detection_49.lo);
        fprintf(out,"PASS: %u checks; full-shell reconstruction is not a lower bound.\n",r->audit.checks);
    }
    if(ferror(out)) failed=1;
    clear(&overlap_4_9); clear(&overlap_4_25); clear(&overlap_9_25); clear(&integer);
    clear(&certificate_4); clear(&certificate_36); clear(&certificate_900);
    clear(&marginal_9); clear(&marginal_25); clear(&interaction_4_9);
    clear_array(blind,DIM); clear(&blind_norm); clear(&blind_response); clear(&dot); clear(&t);
    clear(&blind_detection_49);
    family_clear(&base2); family_clear(&base3); family_clear(&base5); family_clear(&base7); family_clear(&combined); family_clear(&extended);
    run_clear(r); free(r); mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE); return failed;
}

#include "native_arithmetic.h"
#include "native_directional.h"
#include "native_refinement_detector.inc"
#include "native_probe_transport.inc"

void native_refinement_help(void)
{
    puts("Native refinement: signed responses in the complete infinite native norm\n\n"
         "  nfield native-refinement detector N [--json]\n"
         "  nfield native-refinement transport N [--json]\n"
         "  nfield native-refinement probe-transport N [--json]\n"
         "  nfield native-refinement packet scale [--json]\n"
         "  nfield native-refinement copy-cost ratio count\n"
         "  nfield native-refinement kernel left-clock right-clock\n"
         "  nfield native-refinement mask-capture first last [base]\n"
         "  nfield native-refinement trace FIRST LAST [--json]\n"
         "  nfield native-refinement trace FIRST LAST --output NEW.json\n"
         "  nfield native-refinement collision4 [--json]\n"
         "  nfield native-refinement collision-families [FIRST LAST] [--json]\n"
         "  nfield native-refinement verify\n"
         "  nfield verify native-refinement\n\n"
         "Detector uses N=2..100 and refinement through 4N, with every eligible depth.\n"
         "Larger detectors can exceed the browser budget; run them locally.\n"
         "Transport uses N=2..8. Packet scales 2..4 retain the fixed boundary.\n"
         "Probe transport uses N=2..8, pairs depth h with h+2 at 4N, and retains\n"
         "signed response drift and the complete Gram loss. Larger cases are local.\n"
         "Copy ratios 2..10000, counts 1..10000; the sharp bound is universal.\n"
         "Kernel clocks 2..64 compare complete-period and short-sum evaluations.\n"
         "Mask capture: 2<=first<last<=200, base 2..10 (default 10).\n"
         "It compares polarity differences, address indicators and their joint span.\n"
         "Mask capture uses numerical complete-norm projections, not certified intervals.\n"
         "It reports signed terminal pairings, the complete Gram and joint capture.\n"
         "Trace range: 1 <= FIRST < LAST <= 16.\n"
         "Fixed origin psi=T4*d3, GMP rational source and directed 256-bit MPFR.\n"
         "Every old row and every repetition of the common period is retained.\n"
         "JSON includes optimizer coefficients, signed steps, costs, Gram and pair terms.\n"
         "--output creates a new JSON file exclusively; it never replaces a run.\n"
         "Verification checks finite identities, not the open uniform lower bound.");
    native_arithmetic_help();
}
int native_refinement_verify(void)
{
    FILE *f=tmpfile();
    if(!f) { perror("native-refinement tmpfile"); return 0; }
    int status=native_refinement_trace(4,6,f,0);
    if(fclose(f)!=0) status=1;
    if(!status) {
        f=tmpfile();
        if(!f) { perror("native-refinement tmpfile"); return 0; }
        status=native_refinement_collision4_calibration(f,0);
        if(fclose(f)!=0) status=1;
    }
    if(!status) {
        f=tmpfile();
        if(!f) { perror("native-refinement tmpfile"); return 0; }
        status=native_refinement_collision_families(4,8,f,0);
        if(fclose(f)!=0) status=1;
    }
    if(!status) puts("Native refinement complete-period, fixed-origin, and translated collision-family checks: PASS (finite scope)");
    return status==0;
}
static int frame_arg(const char *s)
{
    if(!s || !*s) return -1;
    for(const char *p=s;*p;++p) if(*p<'0' || *p>'9') return -1;
    errno=0; char *end=NULL; long n=strtol(s,&end,10);
    return errno || *end || n<1 || n>TOP ? -1 : (int)n;
}
static int native_bounded_arg(const char *s,unsigned max,unsigned *out)
{
    if(!s||!*s)return 0;
    for(const char *p=s;*p;++p)if(*p<'0'||*p>'9')return 0;
    errno=0;char *end;unsigned long n=strtoul(s,&end,10);if(errno||*end||n>max)return 0;*out=(unsigned)n;return 1;
}
int native_refinement_command(int argc,char **argv)
{
    if(argc==0 || (argc==1 && (!strcmp(argv[0],"--help") || !strcmp(argv[0],"help")))) { native_refinement_help(); return 0; }
    if(argc==1 && !strcmp(argv[0],"verify")) return !native_refinement_verify();
    int arithmetic_status=native_arithmetic_command(argc,argv);
    if(arithmetic_status>=0)return arithmetic_status;
    if((argc==3||argc==4)&&!strcmp(argv[0],"mask-capture")) {
        unsigned first,last,base=10;
        if(native_bounded_arg(argv[1],200,&first)&&native_bounded_arg(argv[2],200,&last)&&(argc==3||native_bounded_arg(argv[3],10,&base)))return native_directional_capture(first,last,base,stdout);
        goto invalid;
    }
    if(argc>=1 && (!strcmp(argv[0],"packet")||!strcmp(argv[0],"transport")||!strcmp(argv[0],"probe-transport"))) {
        if(argc==2 || (argc==3 && !strcmp(argv[2],"--json"))) {
            int N=frame_arg(argv[1]);
            if(N>0) {
                if(!strcmp(argv[0],"probe-transport"))return native_refinement_probe_transport((unsigned)N,stdout,argc==3);
                return !strcmp(argv[0],"packet")?native_packet((unsigned)N,stdout,argc==3):native_transport((unsigned)N,stdout,argc==3);
            }
        }
        goto invalid;
    }
    if(argc==3 && (!strcmp(argv[0],"copy-cost")||!strcmp(argv[0],"kernel"))) {
        unsigned q,count;
        if(native_bounded_arg(argv[1],10000,&q) && native_bounded_arg(argv[2],10000,&count))return !strcmp(argv[0],"kernel")?native_kernel(q,count,stdout):native_copy_cost(q,count,stdout);
        goto invalid;
    }
    if(argc>=1 && !strcmp(argv[0],"detector")) {
        if(argc==2 || (argc==3 && !strcmp(argv[2],"--json"))) {
            unsigned N;
            if(native_bounded_arg(argv[1],100,&N) && N>=2) return native_refinement_detector(N,stdout,argc==3);
        }
        goto invalid;
    }
    if((argc==1 && !strcmp(argv[0],"collision4")) || (argc==2 && !strcmp(argv[0],"collision4") && !strcmp(argv[1],"--json")))
        return native_refinement_collision4_calibration(stdout,argc==2);
    if(argc>=1 && !strcmp(argv[0],"collision-families")) {
        if(argc==1) return native_refinement_collision_families(4,8,stdout,0);
        if(argc==2 && !strcmp(argv[1],"--json")) return native_refinement_collision_families(4,8,stdout,1);
        if(argc==3 || argc==4) {
            int first=frame_arg(argv[1]),last=frame_arg(argv[2]);
            if(first>0 && last>first && (argc==3 || !strcmp(argv[3],"--json")))
                return native_refinement_collision_families(first,last,stdout,argc==4);
        }
        goto invalid;
    }
    int json=0; const char *path=NULL;
    if(argc<3 || strcmp(argv[0],"trace")) goto invalid;
    int first=frame_arg(argv[1]),last=frame_arg(argv[2]);
    if(first<1 || last<1 || first>=last) goto invalid;
    for(int i=3;i<argc;++i) {
        if(!strcmp(argv[i],"--json") && !json) json=1;
        else if(!strcmp(argv[i],"--output") && !path && i+1<argc) { path=argv[++i]; if(!*path || !strncmp(path,"--",2)) goto invalid; }
        else goto invalid;
    }
    if(!path) return native_refinement_trace(first,last,stdout,json);
    /* Calculate into a temporary stream before creating a durable run. */
    FILE *buffer=tmpfile(); if(!buffer) { perror("native-refinement tmpfile"); return 1; }
    int status=native_refinement_trace(first,last,buffer,1);
    if(status || fflush(buffer)!=0 || fseek(buffer,0,SEEK_SET)!=0) { fclose(buffer); return 1; }
    int fd=open(path,O_WRONLY|O_CREAT|O_EXCL,0666);
    if(fd<0) { perror(path); fclose(buffer); return 1; }
    FILE *out=fdopen(fd,"w");
    if(!out) { perror(path); close(fd); fclose(buffer); return 1; }
    char block[8192]; size_t n;
    while((n=fread(block,1,sizeof(block),buffer))!=0) if(fwrite(block,1,n,out)!=n) { status=1; break; }
    if(ferror(buffer)) status=1;
    if(fclose(out)!=0) status=1;
    if(fclose(buffer)!=0) status=1;
    if(status) fprintf(stderr,"native-refinement: incomplete output at %s\n",path);
    else printf("Saved finite native refinement %d -> %d: %s\n",first,last,path);
    return status;
invalid:
    fprintf(stderr,"Invalid native-refinement arguments; require 1 <= FIRST < LAST <= 16; see help native-refinement\n");
    return 1;
}
