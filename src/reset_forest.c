#include "reset_forest.h"
#include "collision_sampling.h"
#include <stdlib.h>
#include <stdint.h>

const char *const reset_forest_names[RF_VALUE_COUNT] = {
    "continuous_energy", "sampled_energy", "defect", "origin_contact",
    "corrected_defect", "forest_work", "complement_work", "forest_absolute_work",
    "restoration_work", "complement_clock_work", "curvature", "signed_work_bound"
};

static unsigned rf_gcd(unsigned a, unsigned b)
{ while (b) { unsigned r=a%b; a=b; b=r; } return a; }

static int rf_prime(unsigned p)
{
    if (p<3 || p>RESET_FOREST_MAX_PRIME || !(p&1)) return 0;
    for (unsigned d=3; d<=p/d; d+=2) if (p%d==0) return 0;
    return 1;
}

static unsigned rf_rough(unsigned k, unsigned n)
{
    unsigned g;
    while ((g=rf_gcd(k,n))>1) k/=g;
    return k;
}

static void rf_scale(mpq_t out, const mpq_t in, long a, unsigned long b)
{
    mpq_t factor;
    mpq_init(factor);
    mpq_set_si(factor,a,b); mpq_canonicalize(factor);
    mpq_mul(out,in,factor); mpq_clear(factor);
}

void reset_forest_init(ResetForest *out)
{
    out->prime=out->cutoff=out->grid=out->count=0;
    mpz_init(out->divisor);
    for (unsigned i=0;i<RESET_FOREST_MAX_PRIME;i++) {
        out->rough[i]=out->selected[i]=out->projection[i]=out->population[i]=0;
        mpq_inits(out->signed_work[i],out->absolute_work[i],out->clock_work[i],NULL);
    }
    for (unsigned i=0;i<RF_VALUE_COUNT;i++) mpq_init(out->value[i]);
}

static void rf_fraction(mpq_t out, int64_t numerator, unsigned long denominator)
{
    uint64_t magnitude=numerator<0?(uint64_t)(-numerator):(uint64_t)numerator;
    mpz_import(mpq_numref(out),1,1,sizeof(magnitude),0,0,&magnitude);
    if (numerator<0) mpz_neg(mpq_numref(out),mpq_numref(out));
    mpz_set_ui(mpq_denref(out),denominator); mpq_canonicalize(out);
}

void reset_forest_clear(ResetForest *out)
{
    mpz_clear(out->divisor);
    for (unsigned i=0;i<RESET_FOREST_MAX_PRIME;i++)
        mpq_clears(out->signed_work[i],out->absolute_work[i],out->clock_work[i],NULL);
    for (unsigned i=0;i<RF_VALUE_COUNT;i++) mpq_clear(out->value[i]);
}

int reset_forest_return_divisor(mpz_t out, unsigned p, unsigned window)
{
    if (!rf_prime(p) || window<3 || window>31) return 0;
    unsigned n=p-1, q=p*p;
    mpz_t value,a,b;
    mpz_inits(value,a,b,NULL);
    mpz_set_ui(value,15);
    mpz_mul_ui(value,value,n*q+1);
    mpz_mul_ui(value,value,n*n-n-1);
    for (unsigned j=1;j<=window;j+=2) {
        mpz_ui_pow_ui(a,q,j); mpz_ui_pow_ui(b,n,j);
        mpz_sub(a,a,b); mpz_mul(value,value,a);
    }
    mpz_set(out,value); mpz_clears(value,a,b,NULL);
    return 1;
}

int reset_forest_compute(ResetForest *out, unsigned p, const mpz_t divisor)
{
    if (!out || !rf_prime(p) || mpz_sgn(divisor)<=0) return 0;
    unsigned n=p-1, q=p*p;
    out->prime=p; out->cutoff=n; out->grid=q; out->count=0;
    mpz_set(out->divisor,divisor);
    for (unsigned i=0;i<RF_VALUE_COUNT;i++) mpq_set_ui(out->value[i],0,1);
    for (unsigned k=0;k<RESET_FOREST_MAX_PRIME;k++) {
        out->population[k]=0;
        mpq_set_ui(out->signed_work[k],0,1);
        mpq_set_ui(out->absolute_work[k],0,1);
        mpq_set_ui(out->clock_work[k],0,1);
    }
    for (unsigned k=1;k<=n;k++) {
        unsigned r=rf_rough(k,n);
        unsigned residue=(unsigned)mpz_fdiv_ui(divisor,r);
        out->rough[k]=r;
        out->selected[k]=(residue==0);
        out->projection[k]=(k/r)*rf_gcd(r,residue);
        out->population[out->projection[k]]++;
        if (k>=2 && out->selected[k]) out->count++;
    }
    mpq_t term,harmonic,half_harmonic;
    mpq_inits(term,harmonic,half_harmonic,NULL);
    for (unsigned k=1;k<=n;k++) {
        mpq_set_ui(term,1,k); mpq_add(harmonic,harmonic,term);
        if (k<2) continue;
        /* b is k*B_N(a/k); t is 2*k*psi(Q*a/k).
         * Including all harmonics and every residue preserves the complete
         * clock. Only the primitive reset reading restricts gcd(a,k)=1.
         * At p<=251 the integer accumulators fit int64_t. */
        int64_t signed_sum=0, absolute_sum=0, clock_sum=0;
        for (unsigned a=1;a<k;a++) {
            long b=0;
            for (unsigned h=1;h<=n;h++) {
                unsigned r=(h*a)%k;
                if (r) b+=2L*r-(long)k;
            }
            unsigned r=(q*a)%k;
            long t=r?2L*r-(long)k:0;
            int64_t product=(int64_t)b*t;
            clock_sum+=product;
            if (rf_gcd(a,k)==1) {
                signed_sum+=product;
                absolute_sum+=product<0?-product:product;
            }
        }
        rf_fraction(out->signed_work[k],signed_sum,2UL*k*k);
        rf_scale(out->signed_work[k],out->signed_work[k],n/k,1);
        rf_fraction(out->absolute_work[k],absolute_sum,2UL*k*k);
        rf_scale(out->absolute_work[k],out->absolute_work[k],n/k,1);
        rf_fraction(out->clock_work[k],clock_sum,4UL*k*k);
        unsigned sector=out->selected[k]?RF_FOREST:RF_OTHER;
        mpq_add(out->value[sector],out->value[sector],out->signed_work[k]);
        if (out->selected[k]) {
            mpq_add(out->value[RF_ABSOLUTE],out->value[RF_ABSOLUTE],out->absolute_work[k]);
            rf_scale(term,out->clock_work[k],2L*(1L-(long)out->population[k]),1);
            mpq_add(out->value[RF_RESTORATION],out->value[RF_RESTORATION],term);
            mpq_set_ui(half_harmonic,0,1);
            for (unsigned h=1;h<=k/2;h++) {
                mpq_set_ui(term,1,h); mpq_add(half_harmonic,half_harmonic,term);
            }
            mpq_mul(term,half_harmonic,half_harmonic);
            rf_scale(term,term,n,2);
            mpq_add(out->value[RF_SIGNED_BOUND],out->value[RF_SIGNED_BOUND],term);
        } else {
            rf_scale(term,out->clock_work[k],2,1);
            mpq_add(out->value[RF_OTHER_CLOCKS],out->value[RF_OTHER_CLOCKS],term);
        }
    }
    collision_sampling_capacity_q(out->value[RF_CONTINUOUS],n);
    collision_sampling_energy_q(out->value[RF_SAMPLED],p);
    mpq_sub(out->value[RF_DEFECT],out->value[RF_CONTINUOUS],out->value[RF_SAMPLED]);
    mpq_set_ui(out->value[RF_CONTACT],n*n,q); mpq_canonicalize(out->value[RF_CONTACT]);
    mpq_sub(out->value[RF_CORRECTED],out->value[RF_DEFECT],out->value[RF_CONTACT]);
    rf_scale(out->value[RF_CURVATURE],harmonic,-(long)n,3UL*p*p*p);
    mpq_clears(term,harmonic,half_harmonic,NULL);
    return 1;
}
