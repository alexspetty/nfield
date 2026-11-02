#include "weighted_remainder_power.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned checks;
static void check(int ok) { ++checks;if (!ok) { fprintf(stderr,"transcendental edge %u failed\n",checks);exit(1); } }
static void edges(void)
{
    mpq_t a,b,l,u,x,y;mpq_inits(a,b,l,u,x,y,NULL);
    const char *bad[]={"0","-1","2/2","1/0","1/-2",
      "115792089237316195423570985008687907853269984665640564039457584007913129639936",
      "1/115792089237316195423570985008687907853269984665640564039457584007913129639936"};
    for (unsigned i=0;i<sizeof bad/sizeof bad[0];++i) {
        check(!mpq_set_str(a,bad[i],10));mpq_set_si(l,77,13);mpq_set_si(u,-88,17);
        check(!weighted_remainder_rational_log_interval_q(l,u,a));
        check(!mpq_cmp_si(l,77,13) && !mpq_cmp_si(u,-88,17));
    }
    mpq_set_ui(a,1,2);mpq_set_ui(b,3,4);
    check(!weighted_remainder_rational_log_interval_q(l,l,a));
    check(!weighted_remainder_rational_log_interval_q(NULL,u,a));
    check(!weighted_remainder_rational_log_interval_q(l,NULL,a));
    check(!weighted_remainder_rational_log_interval_q(l,u,NULL));
    check(weighted_remainder_rational_log_interval_q(x,y,a));
    mpq_set(l,a);check(weighted_remainder_rational_log_interval_q(l,u,l));
    check(!mpq_cmp(l,x) && !mpq_cmp(u,y));
    mpq_set(u,a);check(weighted_remainder_rational_log_interval_q(l,u,u));
    check(!mpq_cmp(l,x) && !mpq_cmp(u,y));
    const char *ebad[][2]={{"-1","1"},{"0","2"},{"3/4","1/2"},{"2/2","1"},{"0","1/0"},
      {"0","1/-2"},{"1/115792089237316195423570985008687907853269984665640564039457584007913129639936","1"}};
    for (unsigned i=0;i<sizeof ebad/sizeof ebad[0];++i) {
        check(!mpq_set_str(a,ebad[i][0],10));check(!mpq_set_str(b,ebad[i][1],10));
        mpq_set_si(l,77,13);mpq_set_si(u,-88,17);
        check(!weighted_remainder_small_exp_interval_q(l,u,a,b));
        check(!mpq_cmp_si(l,77,13) && !mpq_cmp_si(u,-88,17));
    }
    mpq_set_ui(a,1,2);mpq_set_ui(b,3,4);
    check(!weighted_remainder_small_exp_interval_q(l,l,a,b));
    check(!weighted_remainder_small_exp_interval_q(NULL,u,a,b));
    check(!weighted_remainder_small_exp_interval_q(l,NULL,a,b));
    check(!weighted_remainder_small_exp_interval_q(l,u,NULL,b));
    check(!weighted_remainder_small_exp_interval_q(l,u,a,NULL));
    check(weighted_remainder_small_exp_interval_q(x,y,a,b));
    mpq_set(l,a);mpq_set(u,b);check(weighted_remainder_small_exp_interval_q(l,u,l,u));
    check(!mpq_cmp(l,x) && !mpq_cmp(u,y));
    mpq_set(l,b);mpq_set(u,a);check(weighted_remainder_small_exp_interval_q(l,u,u,l));
    check(!mpq_cmp(l,x) && !mpq_cmp(u,y));
    mpq_clears(a,b,l,u,x,y,NULL);
}
int main(void)
{
    edges();printf("EDGES %u\n",checks);char op,a_text[400],b_text[400];
    while (scanf(" %c %399s",&op,a_text)==2) {
        mpq_t a,b,l,u;mpq_inits(a,b,l,u,NULL);if (mpq_set_str(a,a_text,10)) return 2;
        int ok;
        if (op=='L') ok=weighted_remainder_rational_log_interval_q(l,u,a);
        else if (op=='E') {
            if (scanf(" %399s",b_text)!=1 || mpq_set_str(b,b_text,10)) return 2;
            ok=weighted_remainder_small_exp_interval_q(l,u,a,b);
        } else return 2;
        printf("%c %d",op,ok);if (ok) gmp_printf(" %Qd %Qd",l,u);putchar('\n');
        mpq_clears(a,b,l,u,NULL);
    }
    return ferror(stdin)?2:0;
}
