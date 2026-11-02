#include "../src/weighted_remainder_power.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void edge_checks(void)
{
    mpq_t a,b,s,l,h;mpq_inits(a,b,s,l,h,NULL);
    mpq_set_ui(a,5,7);mpq_set_ui(b,11,13);mpq_set_ui(s,3,2);
    CHECK(!weighted_remainder_power_interval_q(a,b,0,s));
    CHECK(!weighted_remainder_power_interval_q(a,b,241,s));
    CHECK(!weighted_remainder_power_interval_q(a,b,~0U,s));
    CHECK(!weighted_remainder_power_interval_q(a,a,2,s));
    CHECK(!weighted_remainder_power_interval_q(NULL,b,2,s));
    CHECK(!weighted_remainder_power_interval_q(a,NULL,2,s));
    CHECK(!weighted_remainder_power_interval_q(a,b,2,NULL));
    mpq_set_si(s,-1,2);CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpq_set_ui(s,1201,100);CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpq_set_ui(s,2,4);CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpz_set_ui(mpq_numref(s),0);mpz_set_ui(mpq_denref(s),2);
    CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpz_set_ui(mpq_numref(s),1);mpz_set_ui(mpq_denref(s),0);
    CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpz_set_si(mpq_denref(s),-2);CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpz_ui_pow_ui(mpq_denref(s),2,256);CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    mpz_ui_pow_ui(mpq_numref(s),2,256);mpz_add_ui(mpq_numref(s),mpq_numref(s),1);
    mpz_ui_pow_ui(mpq_denref(s),2,254);CHECK(!weighted_remainder_power_interval_q(a,b,2,s));
    CHECK(!mpq_cmp_ui(a,5,7) && !mpq_cmp_ui(b,11,13));
    mpq_set_ui(s,3,2);CHECK(weighted_remainder_power_interval_q(l,h,8,s));
    mpq_set(a,s);CHECK(weighted_remainder_power_interval_q(a,b,8,a));
    CHECK(!mpq_cmp(a,l) && !mpq_cmp(b,h));
    mpq_set(b,s);CHECK(weighted_remainder_power_interval_q(a,b,8,b));
    CHECK(!mpq_cmp(a,l) && !mpq_cmp(b,h));
    mpq_set_ui(s,1,3);CHECK(weighted_remainder_power_interval_q(a,b,8,s));
    CHECK(mpq_cmp_ui(a,1,2)<=0 && mpq_cmp_ui(b,1,2)>=0);
    mpq_set_ui(s,0,1);CHECK(weighted_remainder_power_interval_q(a,b,240,s));
    CHECK(!mpq_cmp_ui(a,1,1) && !mpq_cmp(a,b));
    mpq_set_ui(s,12,1);CHECK(weighted_remainder_power_interval_q(a,b,240,s));
    mpz_ui_pow_ui(mpq_denref(l),240,12);mpz_set_ui(mpq_numref(l),1);
    CHECK(!mpq_cmp(a,l) && !mpq_cmp(a,b));
    mpz_ui_pow_ui(mpq_numref(s),2,255);mpz_sub_ui(mpq_numref(s),mpq_numref(s),1);
    mpz_ui_pow_ui(mpq_denref(s),2,252);
    CHECK(weighted_remainder_power_interval_q(a,b,239,s));
    CHECK(mpq_sgn(a)>0 && mpq_cmp(a,b)<=0 && mpq_cmp_ui(b,1,1)<=0);
    mpq_clears(a,b,s,l,h,NULL);printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();mpq_t lo,hi,s;mpq_inits(lo,hi,s,NULL);unsigned n;char value[1024];
    while (scanf("%u %1023s",&n,value)==2) {
        int parsed=mpq_set_str(s,value,10)==0;
        if (parsed && mpz_sgn(mpq_denref(s))>0) mpq_canonicalize(s);
        int ok=parsed && weighted_remainder_power_interval_q(lo,hi,n,s);
        printf("P %d",ok);if (ok) gmp_printf(" %Qd %Qd",lo,hi);putchar('\n');
    }
    mpq_clears(lo,hi,s,NULL);return 0;
}
