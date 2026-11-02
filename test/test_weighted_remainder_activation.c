#define _POSIX_C_SOURCE 200809L
#include "../src/weighted_remainder_activation.h"
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned checks;
static void check(int yes) { ++checks; if (!yes) abort(); }

static void fields(WeightedActivationResult *r, mpq_ptr p[8])
{
    p[0]=r->minimum_increment; p[1]=r->probability_sum; p[2]=r->event_probability;
    p[3]=r->coupled_probability; p[4]=r->active_mean; p[5]=r->active_variance;
    p[6]=r->sperner_bound; p[7]=r->universal_bound_squared;
}

static void seed(WeightedActivationResult *r)
{
    mpq_ptr p[8]; fields(r,p);
    r->dimension=47; r->interval_count=53;
    for (unsigned i=0;i<8;++i) mpq_set_ui(p[i],17+i,1);
}

static void preserved(WeightedActivationResult *r)
{
    mpq_ptr p[8]; fields(r,p);
    check(r->dimension==47 && r->interval_count==53);
    for (unsigned i=0;i<8;++i) check(mpq_cmp_ui(p[i],17+i,1)==0);
}

static void same(WeightedActivationResult *r, WeightedActivationResult *s)
{
    mpq_ptr p[8],q[8]; fields(r,p); fields(s,q);
    check(r->dimension==s->dimension && r->interval_count==s->interval_count);
    for (unsigned i=0;i<8;++i) check(mpq_equal(p[i],q[i]));
}

static void self_test(void)
{
    WeightedActivationResult r, expected;
    weighted_remainder_activation_init(&r); weighted_remainder_activation_init(&expected);
    mpq_t b[2],f[4],a,u,v,bad;
    mpq_inits(a,u,v,bad,NULL);
    for (unsigned i=0;i<2;++i) mpq_init(b[i]);
    for (unsigned i=0;i<4;++i) { mpq_init(f[i]); mpq_set_ui(f[i],(i&1)+(i>>1),1); }
    mpq_set_ui(b[0],1,2); mpq_set_ui(b[1],1,3);
    mpq_set_ui(a,1,1); mpq_set_ui(u,1,1); mpq_set_ui(v,1,1);
    check(weighted_remainder_activation_q(&expected,2,b,2,f,4,a,u,v));
    check(mpq_cmp_ui(expected.event_probability,1,2)==0);
    check(mpq_cmp_ui(expected.sperner_bound,1,2)==0);
    check(mpq_cmp_ui(expected.active_variance,2,9)==0);
    seed(&r);
#define REJECT(expr) do { check(!(expr)); preserved(&r); } while (0)
    REJECT(weighted_remainder_activation_q(&r,13,b,2,f,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,UINT_MAX,b,2,f,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,1,f,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,3,f,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,3,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,5,a,u,v));
    REJECT(weighted_remainder_activation_q(NULL,2,b,2,f,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,NULL,2,f,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,2,NULL,4,a,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,NULL,u,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,a,NULL,v));
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,a,u,NULL));
    for (unsigned i=0;i<4;++i) {
        mpq_set_si(bad,i==0?0:-1,1);
        if (i==2) mpz_set_ui(mpq_denref(bad),0);
        if (i==3) mpz_set_si(mpq_denref(bad),-2);
        REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,bad,u,v));
    }
    mpq_set_ui(bad,2,1);
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,a,u,bad));
    mpq_set_ui(bad,2,1); mpz_set_ui(mpq_denref(bad),4);
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,bad,u,v));
    for (unsigned i=0;i<4;++i) {
        mpq_set_si(b[0],i==0?-1:2,3);
        if (i==2) mpz_set_ui(mpq_denref(b[0]),0);
        if (i==3) mpz_set_ui(mpq_denref(b[0]),4);
        REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,a,u,v));
    }
    mpq_set_ui(b[0],0,1); mpq_set_ui(f[1],0,1);
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,a,u,v)); /* zero-probability edge */
    mpq_set_ui(f[1],1,1); mpq_set_ui(b[0],1,2);
    mpz_set_ui(mpq_denref(f[3]),0);
    REJECT(weighted_remainder_activation_q(&r,2,b,2,f,4,a,u,v));
    mpq_set_ui(f[3],2,1);
    for (unsigned field=0;field<8;++field) for (unsigned input=0;input<3;++input) {
        seed(&r); mpq_ptr p[8]; fields(&r,p);
        mpq_set(p[field],input==0?a:input==1?u:v);
        check(weighted_remainder_activation_q(&r,2,b,2,f,4,
            input==0?p[field]:a,input==1?p[field]:u,input==2?p[field]:v));
        same(&r,&expected);
    }
    check(weighted_remainder_activation_q(&expected,1,b,1,f,2,a,u,v));
    for (unsigned field=0;field<8;++field) {
        seed(&r); mpq_ptr p[8]; fields(&r,p); mpq_set(p[field],b[0]);
        check(weighted_remainder_activation_q(&r,1,(const mpq_t *)p[field],1,f,2,a,u,v));
        same(&r,&expected);
    }
    mpq_set_ui(u,0,1); mpq_set_ui(v,0,1);
    check(weighted_remainder_activation_q(&expected,0,NULL,0,f,1,a,u,v));
    for (unsigned field=0;field<8;++field) {
        seed(&r); mpq_ptr p[8]; fields(&r,p); mpq_set(p[field],f[0]);
        check(weighted_remainder_activation_q(&r,0,NULL,0,(const mpq_t *)p[field],1,a,u,v));
        same(&r,&expected);
    }
    check(mpq_cmp_ui(expected.event_probability,1,1)==0 && expected.dimension==0);
    check(mpq_sgn(expected.minimum_increment)==0);
    weighted_remainder_activation_clear(&r); weighted_remainder_activation_clear(&expected);
    for (unsigned i=0;i<2;++i) mpq_clear(b[i]);
    for (unsigned i=0;i<4;++i) mpq_clear(f[i]);
    mpq_clears(a,u,v,bad,NULL);
    printf("api_checks=%u\n",checks);
}

int main(int argc,char **argv)
{
    if (argc==2 && !strcmp(argv[1],"--self-test")) { self_test(); return 0; }
    if (argc!=2 || strcmp(argv[1],"--stream")) return 2;
    char *line=NULL; size_t size=0;
    while (getline(&line,&size,stdin)>=0) {
        char *args[12]={(char *)"nfield",(char *)"weighted-remainder-state"};
        char *save=NULL; int count=2;
        for (char *s=strtok_r(line," \t\r\n",&save);s;s=strtok_r(NULL," \t\r\n",&save)) {
            if (count==12) { free(line); return 2; } args[count++]=s;
        }
        if (count==2) continue;
        puts("BEGIN"); int status=weighted_remainder_activation_command(count,args);
        printf("exit=%d\nEND\n",status);
    }
    free(line); return 0;
}
