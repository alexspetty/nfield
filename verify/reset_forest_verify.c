#include "../src/reset_forest.h"
#include <stdio.h>

static unsigned test_gcd(unsigned a, unsigned b)
{ while (b) { unsigned t=a%b; a=b; b=t; } return a; }

/* Direct Gram and sampled-field definitions, independent of the capacity
 * and digit-floor algorithms used by the operation. */
static void direct_energies(mpq_t continuous, mpq_t sampled, unsigned p)
{
    unsigned n=p-1,q=p*p;
    mpq_t term,value;
    mpq_inits(term,value,NULL);
    mpq_set_ui(continuous,0,1); mpq_set_ui(sampled,0,1);
    for (unsigned i=1;i<=n;i++) for (unsigned j=1;j<=n;j++) {
        unsigned g=test_gcd(i,j);
        mpq_set_ui(term,g*g,3UL*i*j); mpq_canonicalize(term);
        mpq_add(continuous,continuous,term);
    }
    for (unsigned a=0;a<q;a++) {
        mpq_set_ui(value,0,1);
        for (unsigned h=1;h<=n;h++) {
            unsigned r=(h*a)%q;
            mpq_set_si(term,r?2L*r-(long)q:0,q); mpq_canonicalize(term);
            mpq_add(value,value,term);
        }
        mpq_mul(value,value,value); mpq_add(sampled,sampled,value);
    }
    mpq_set_ui(term,1,q); mpq_mul(sampled,sampled,term);
    mpq_clears(term,value,NULL);
}

int reset_forest_verify(void)
{
    const unsigned primes[]={3,5,7,11,13,17,31,43};
    unsigned checks=0,failures=0,cases=0;
#define CHECK(condition) do { checks++; if (!(condition)) { failures++; \
    fprintf(stderr,"reset-forest check failed at line %d, p=%u\n",__LINE__,p); } } while (0)
    mpz_t divisor; mpz_init(divisor);
    mpq_t continuous,sampled,a,b,c;
    mpq_inits(continuous,sampled,a,b,c,NULL);
    ResetForest r; reset_forest_init(&r);
    for (unsigned index=0;index<sizeof(primes)/sizeof(primes[0]);index++) {
        unsigned p=primes[index];
        direct_energies(continuous,sampled,p);
        for (unsigned choice=0;choice<4;choice++) {
            if (choice==3) CHECK(reset_forest_return_divisor(divisor,p,3));
            else mpz_set_ui(divisor,choice==0?1:choice==1?2:30);
            CHECK(reset_forest_compute(&r,p,divisor)); cases++;
            CHECK(mpq_equal(continuous,r.value[RF_CONTINUOUS]));
            CHECK(mpq_equal(sampled,r.value[RF_SAMPLED]));
            mpq_add(a,r.value[RF_FOREST],r.value[RF_OTHER]);
            mpq_set_ui(b,4,r.grid); mpq_mul(a,a,b);
            mpq_add(a,a,r.value[RF_CONTACT]); mpq_add(a,a,r.value[RF_CURVATURE]);
            CHECK(mpq_equal(a,r.value[RF_DEFECT]));
            mpq_add(a,r.value[RF_OTHER_CLOCKS],r.value[RF_RESTORATION]);
            CHECK(mpq_equal(a,r.value[RF_OTHER]));
            mpq_set_ui(a,0,1);
            unsigned population=0;
            for (unsigned k=1;k<=r.cutoff;k++) {
                CHECK(r.projection[k]<=k && k%r.projection[k]==0);
                CHECK(r.selected[r.projection[k]]);
                unsigned mass=0;
                for (unsigned j=k;j<=r.cutoff;j+=k) mass+=r.population[j];
                CHECK(mass==(r.selected[k]?r.cutoff/k:0));
                population+=r.population[k];
                mpq_set_ui(b,2*r.population[k],1);
                mpq_mul(b,b,r.clock_work[k]); mpq_add(a,a,b);
                mpq_abs(b,r.signed_work[k]);
                CHECK(mpq_cmp(b,r.absolute_work[k])<=0);
            }
            CHECK(population==r.cutoff);
            CHECK(mpq_equal(a,r.value[RF_FOREST]));
            mpq_abs(a,r.value[RF_FOREST]);
            CHECK(mpq_cmp(a,r.value[RF_SIGNED_BOUND])<=0);
            CHECK(mpq_cmp(a,r.value[RF_ABSOLUTE])<=0);
            mpq_abs(a,r.value[RF_RESTORATION]);
            CHECK(mpq_cmp(a,r.value[RF_SIGNED_BOUND])<=0);
            if (p==31 && choice==3) {
                CHECK(r.count==26);
                for (unsigned k=2;k<=30;k++)
                    CHECK(r.selected[k]==(k!=17 && k!=23 && k!=29));
                CHECK(r.population[1]==4);
            }
            if (p==5) {
                CHECK(mpq_cmp_ui(r.value[RF_DEFECT],143,225)==0);
                mpq_set_si(c,-1,225);
                CHECK(mpq_equal(c,r.value[RF_CORRECTED]));
            }
        }
        mpq_set(a,r.value[RF_DEFECT]);
        mpz_set_ui(divisor,0);
        CHECK(!reset_forest_compute(&r,p,divisor));
        CHECK(mpq_equal(a,r.value[RF_DEFECT]));
    }
    {
        unsigned p=31;
        /* Large D exercises valuation saturation without machine conversion. */
        mpz_ui_pow_ui(divisor,2,4096); mpz_mul_ui(divisor,divisor,17*17);
        CHECK(reset_forest_compute(&r,p,divisor));
        CHECK(r.selected[17] && !r.selected[19]);
        CHECK(!reset_forest_compute(&r,9,divisor));
        CHECK(!reset_forest_return_divisor(divisor,31,2));
    }
    reset_forest_clear(&r); mpz_clear(divisor);
    mpq_clears(continuous,sampled,a,b,c,NULL);
    printf("Reset forest verification: %u/%u finite checks passed across %u selections.\n",
           checks-failures,checks,cases);
    puts("Direct field/Gram energies, reset identity, source masses, restoration and finite bounds.");
    puts("This checks finite computations; it does not establish uniform complementary decay.");
    return failures==0;
#undef CHECK
}
