#include "reset_forest_contracts.h"
#include "../src/reset_forest.h"
#include <stdio.h>
#include <string.h>

typedef struct {
    const char *check_id;
    const char *domain;
} Contract;

typedef struct {
    unsigned assertions;
    unsigned failures;
    unsigned cases;
} ContractResult;

#define PANEL "p in {3,5,7,11,13,17,31,43}; N=p-1; Q=p^2; D in {1,2,30,return-divisor(p,3)}; unit source"
#include "reset_forest_contracts_source.inc"

static const Contract contracts[] = {
 {"forest.opening.continuous", "N=4; exact continuous energy, expected 23/9"},
 {"forest.opening.grid", "N=4; Q=25; complete rational grid, expected 48/25"},
 {"forest.opening.sampled", "N=4; Q=25; exact rational representative of the real sampled energy, expected 48/25"},
 {"forest.opening.corrected", "N=4; Q=25; origin-restored defect, expected -1/225"},
 {"forest.opening.defect", "p=5; N=4; Q=25; defect, expected 143/225"},
 {"forest.work.split", PANEL},
 {"forest.work.decomposition", PANEL},
 {"forest.work.remainder", PANEL},
 {"source.collapse_total_mass", FS_SOURCE_DOMAIN},
 {"source.collapse_reset_mass", FS_SOURCE_DOMAIN},
 {"forest.work.selected", PANEL},
 {"forest.work.restoration", PANEL},
 {"forest.work.finite-bound", PANEL},
#include "reset_forest_contracts_source_rows.inc"
};
static const size_t contract_count = sizeof(contracts)/sizeof(contracts[0]);

static unsigned gcd_small(unsigned a,unsigned b)
{ while(b){unsigned r=a%b;a=b;b=r;} return a; }

/* Direct definitions use rational arithmetic and complete grids. They do not
 * call the capacity/energy algorithms used by reset_forest_compute. */
static void energies(mpq_t continuous,mpq_t sampled,unsigned n,unsigned q)
{
    mpq_t x,t;mpq_inits(x,t,NULL);
    mpq_set_ui(continuous,0,1);mpq_set_ui(sampled,0,1);
    for(unsigned i=1;i<=n;i++)for(unsigned j=1;j<=n;j++){
        unsigned g=gcd_small(i,j);
        mpq_set_ui(t,g*g,3UL*i*j);mpq_canonicalize(t);
        mpq_add(continuous,continuous,t);
    }
    for(unsigned a=0;a<q;a++){
        mpq_set_ui(x,0,1);
        for(unsigned h=1;h<=n;h++){
            unsigned r=(h*a)%q;
            mpq_set_si(t,r?2L*r-(long)q:0,q);mpq_canonicalize(t);
            mpq_add(x,x,t);
        }
        mpq_mul(x,x,x);mpq_add(sampled,sampled,x);
    }
    mpq_set_ui(t,1,q);mpq_mul(sampled,sampled,t);
    mpq_clears(x,t,NULL);
}

/* P_k is the primitive reset reading and W_k is the complete clock reading.
 * Separate primitive/full sums retain nonunits and midpoint endpoints. */
static void clock_row(mpq_t primitive,mpq_t full,unsigned n,unsigned q,unsigned k)
{
    mpq_t field,psi,t;mpq_inits(field,psi,t,NULL);
    mpq_set_ui(primitive,0,1);mpq_set_ui(full,0,1);
    for(unsigned a=1;a<k;a++){
        mpq_set_ui(field,0,1);
        for(unsigned h=1;h<=n;h++){
            unsigned r=(h*a)%k;
            mpq_set_si(t,r?2L*r-(long)k:0,k);mpq_canonicalize(t);
            mpq_add(field,field,t);
        }
        unsigned r=(q*a)%k;
        mpq_set_si(psi,r?2L*r-(long)k:0,2UL*k);mpq_canonicalize(psi);
        mpq_mul(t,field,psi);mpq_add(full,full,t);
        if(gcd_small(a,k)==1)mpq_add(primitive,primitive,t);
    }
    mpq_set_ui(t,n/k,1);mpq_mul(primitive,primitive,t);
    mpq_set_ui(t,1,2);mpq_mul(full,full,t);
    mpq_clears(field,psi,t,NULL);
}

static void assertion(ContractResult *r,int ok)
{r->assertions++;if(!ok)r->failures++;}

static ContractResult contract_run(size_t index)
{
    ContractResult result={0,0,0};
    if(index>=contract_count){result.failures=1;return result;}
    if(index==8)return forest_source_run(FS_TOTAL);
    if(index==9)return forest_source_run(FS_RESET_MASS);
    if(index>=13)return forest_source_run(fs_kinds[index-13]);
    ResetForest f;reset_forest_init(&f);
    mpz_t d,omega;mpz_inits(d,omega,NULL);
    mpq_t a,b,c,t,continuous,sampled,primitive,full,selected,other,restoration,bound;
    mpq_inits(a,b,c,t,continuous,sampled,primitive,full,selected,other,restoration,bound,NULL);
    if(index<5){
        static const int slots[]={RF_CONTINUOUS,RF_SAMPLED,RF_SAMPLED,RF_CORRECTED,RF_DEFECT};
        static const long numerator[]={23,48,48,-1,143};
        static const unsigned denominator[]={9,25,25,225,225};
        mpz_set_ui(d,1);int ok=reset_forest_compute(&f,5,d);
        assertion(&result,ok);result.cases=1;
        if(ok){
            mpq_set_si(a,numerator[index],denominator[index]);mpq_canonicalize(a);
            assertion(&result,mpq_equal(f.value[slots[index]],a));
            energies(continuous,sampled,4,25);
            if(index==0)mpq_set(b,continuous);
            else if(index==1||index==2)mpq_set(b,sampled);
            else{
                mpq_sub(b,continuous,sampled);
                if(index==3){mpq_set_ui(c,16,25);mpq_sub(b,b,c);}
            }
            assertion(&result,mpq_equal(b,a));
        }
    }else{
        const unsigned primes[]={3,5,7,11,13,17,31,43};
        for(size_t pi=0;pi<sizeof(primes)/sizeof(primes[0]);pi++){
            unsigned p=primes[pi],n=p-1,q=p*p;
            energies(continuous,sampled,n,q);
            for(unsigned choice=0;choice<4;choice++){
                if(choice==3){if(!reset_forest_return_divisor(d,p,3)){assertion(&result,0);continue;}}
                else mpz_set_ui(d,choice==0?1:choice==1?2:30);
                int ok=reset_forest_compute(&f,p,d);assertion(&result,ok);result.cases++;
                if(!ok)continue;
                /* N^N contains every N-supported prime power needed up to N. */
                mpz_ui_pow_ui(omega,n,n);mpz_mul(omega,omega,d);
                unsigned population[RESET_FOREST_MAX_PRIME]={0};
                for(unsigned j=1;j<=n;j++)population[mpz_gcd_ui(NULL,omega,j)]++;
                mpq_set_ui(selected,0,1);mpq_set_ui(other,0,1);
                mpq_set_ui(restoration,0,1);mpq_set_ui(bound,0,1);mpq_set_ui(b,0,1);
                for(unsigned k=2;k<=n;k++){
                    int in=mpz_divisible_ui_p(omega,k);
                    clock_row(primitive,full,n,q,k);
                    mpq_add(in?selected:other,in?selected:other,primitive);
                    if(in){
                        mpq_set_si(t,2L*(1L-population[k]),1);mpq_mul(t,t,full);
                        mpq_add(restoration,restoration,t);
                        mpq_set_ui(a,0,1);
                        for(unsigned h=1;h<=k/2;h++){mpq_set_ui(t,1,h);mpq_add(a,a,t);}
                        mpq_mul(a,a,a);mpq_set_ui(t,n,2);mpq_canonicalize(t);mpq_mul(a,a,t);mpq_add(bound,bound,a);
                        mpq_set_ui(t,2UL*population[k],1);mpq_mul(t,t,full);mpq_add(b,b,t);
                    }
                }
                switch(index){
                case 5:
                    mpq_add(a,selected,other);mpq_add(c,f.value[RF_FOREST],f.value[RF_OTHER]);
                    assertion(&result,mpq_equal(a,c));
                    assertion(&result,mpq_equal(selected,f.value[RF_FOREST]));
                    assertion(&result,mpq_equal(other,f.value[RF_OTHER]));break;
                case 6: case 7:
                    mpq_set_ui(t,n*n,q);mpq_canonicalize(t);
                    assertion(&result,mpq_equal(t,f.value[RF_CONTACT]));
                    mpq_sub(a,continuous,sampled);mpq_set_ui(t,1,1);mpq_sub(a,a,t);
                    if(index==7){mpq_set_ui(t,4,q);mpq_mul(c,other,t);mpq_sub(a,a,c);mpq_set(c,selected);}
                    else mpq_add(c,selected,other);
                    mpq_set_ui(t,4,q);mpq_mul(c,c,t);
                    mpq_set_si(t,-2,p);mpq_canonicalize(t);mpq_add(c,c,t);
                    mpq_set_ui(t,1,q);mpq_add(c,c,t);
                    mpq_set_ui(t,0,1);
                    for(unsigned h=1;h<=n;h++){mpq_set_ui(primitive,1,h);mpq_add(t,t,primitive);}
                    mpq_set_si(primitive,-(long)n,3UL*p*p*p);mpq_canonicalize(primitive);mpq_mul(t,t,primitive);
                    assertion(&result,mpq_equal(t,f.value[RF_CURVATURE]));
                    mpq_add(c,c,t);
                    assertion(&result,mpq_equal(a,c));
                    assertion(&result,mpq_equal(selected,f.value[RF_FOREST]));
                    assertion(&result,mpq_equal(other,f.value[RF_OTHER]));
                    mpq_sub(a,continuous,sampled);assertion(&result,mpq_equal(a,f.value[RF_DEFECT]));break;
                case 8:{
                    unsigned total=0;
                    for(unsigned k=1;k<=n;k++){total+=f.population[k];assertion(&result,f.population[k]==population[k]);}
                    assertion(&result,total==n);break;}
                case 9:
                    for(unsigned k=1;k<=n;k++){
                        unsigned mass=0;for(unsigned j=k;j<=n;j+=k)mass+=f.population[j];
                        assertion(&result,mass==(mpz_divisible_ui_p(omega,k)?n/k:0));
                    }break;
                case 10:
                    assertion(&result,mpq_equal(b,selected));
                    assertion(&result,mpq_equal(selected,f.value[RF_FOREST]));
                    for(unsigned k=1;k<=n;k++)assertion(&result,f.population[k]==population[k]);
                    break;
                case 11:
                    assertion(&result,mpq_equal(restoration,f.value[RF_RESTORATION]));
                    mpq_add(a,f.value[RF_OTHER_CLOCKS],restoration);
                    assertion(&result,mpq_equal(a,other));
                    assertion(&result,mpq_equal(other,f.value[RF_OTHER]));break;
                case 12:
                    mpq_abs(a,selected);assertion(&result,mpq_cmp(a,bound)<=0);
                    mpq_abs(a,restoration);assertion(&result,mpq_cmp(a,bound)<=0);
                    assertion(&result,mpq_equal(bound,f.value[RF_SIGNED_BOUND]));
                    assertion(&result,mpq_equal(selected,f.value[RF_FOREST]));
                    assertion(&result,mpq_equal(restoration,f.value[RF_RESTORATION]));break;
                }
            }
        }
    }
    mpq_clears(a,b,c,t,continuous,sampled,primitive,full,selected,other,restoration,bound,NULL);
    mpz_clears(d,omega,NULL);reset_forest_clear(&f);return result;
}

static void contract_json_string(const char *text)
{
    putchar('"');
    for (const unsigned char *p=(const unsigned char *)text; *p; ++p) {
        if (*p=='"' || *p=='\\') { putchar('\\'); putchar(*p); }
        else if (*p=='\n') fputs("\\n",stdout);
        else if (*p<32) printf("\\u%04x",*p);
        else putchar(*p);
    }
    putchar('"');
}

int reset_forest_contracts_verify(int json)
{
    ContractResult results[sizeof(contracts)/sizeof(contracts[0])];
    size_t passed=0,failed=0;
    unsigned long long cases=0,assertions=0;
    for (size_t i=0; i<contract_count; ++i) {
        results[i]=contract_run(i);
        if (results[i].failures) ++failed; else ++passed;
        cases+=results[i].cases;
        assertions+=results[i].assertions;
    }
    int exit_code=failed ? 1 : 0;
    if (json) {
        printf("{\"schema\":\"nfield.checks.v1\",\"family\":\"reset-forest\","
               "\"suite\":\"contracts\",\"scope\":\"finite-implementation\","
               "\"summary\":{\"checks\":%zu,\"passed\":%zu,\"failed\":%zu,"
               "\"cases\":%llu,\"assertions\":%llu},\"results\":[",
               contract_count,passed,failed,cases,assertions);
        for (size_t i=0; i<contract_count; ++i) {
            if (i) putchar(',');
            fputs("{\"check_id\":",stdout);contract_json_string(contracts[i].check_id);
            fputs(",\"tested_domain\":",stdout);contract_json_string(contracts[i].domain);
            printf(",\"cases\":%u,\"assertions\":%u,\"failures\":%u,\"status\":\"%s\"}",
                   results[i].cases,results[i].assertions,results[i].failures,
                   results[i].failures ? "fail" : "pass");
        }
        printf("],\"exit_code\":%d}\n",exit_code);
    } else {
        puts("Reset forest contracts\n");
        puts("Exact numerical checks on the finite input panels below.");
        puts("Passing these panels does not establish a universal or asymptotic bound.\n");
        for (size_t i=0; i<contract_count; ++i) {
            printf("  %s  %s\n",results[i].failures ? "FAIL" : "PASS",contracts[i].check_id);
            printf("        domain: %s\n",contracts[i].domain);
            printf("        cases=%u assertions=%u failures=%u\n",
                   results[i].cases,results[i].assertions,results[i].failures);
        }
        printf("\n%zu/%zu contract checks passed; %llu cases, %llu assertions.\n",
               passed,contract_count,cases,assertions);
    }
    return exit_code;
}
