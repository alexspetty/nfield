#define _POSIX_C_SOURCE 200809L
#include "../src/weighted_remainder_conductor.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned checks;
static void check(int value) { ++checks; if (!value) abort(); }

static int abort_visit(unsigned a, const mpq_t lo, const mpq_t hi, void *context)
{
    (void)a; (void)lo; (void)hi;
    ++*(unsigned *)context;
    return 0;
}

static void self_test(void)
{
    mpq_t out[6], expected[6];
    mpq_ptr ptr[6];
    for (unsigned i = 0; i < 6; ++i) { mpq_inits(out[i], expected[i], NULL); ptr[i] = out[i]; }
    mpz_t a, saved;
    mpz_inits(a, saved, NULL);
    mpz_set_str(a, "-123456789012345678901234567890123456789", 10);
    unsigned bad[][2] = {{0,2},{1,2},{241,2},{2,0},{2,1},{2,241}};
    for (unsigned b = 0; b < sizeof(bad)/sizeof(*bad); ++b) {
        for (unsigned i = 0; i < 6; ++i) mpq_set_ui(out[i], i+17, 1);
        check(!weighted_remainder_conductor_interval_q(out[0],out[1],out[2],out[3],out[4],out[5],
                                                       bad[b][0],a,bad[b][1]));
        for (unsigned i = 0; i < 6; ++i) check(mpq_cmp_ui(out[i], i+17, 1) == 0);
    }
    for (unsigned i = 0; i < 6; ++i) for (unsigned j = i+1; j < 6; ++j) {
        for (unsigned k = 0; k < 6; ++k) { ptr[k] = out[k]; mpq_set_ui(out[k], k+17, 1); }
        ptr[j] = ptr[i];
        check(!weighted_remainder_conductor_interval_q(ptr[0],ptr[1],ptr[2],ptr[3],ptr[4],ptr[5],7,a,31));
        for (unsigned k = 0; k < 6; ++k) check(mpq_cmp_ui(out[k], k+17, 1) == 0);
    }
    for (unsigned i = 0; i < 6; ++i) for (unsigned den = 0; den < 2; ++den) {
        mpz_set_str(a, den ? "123456789012345678901234567890123456789" :
                            "-123456789012345678901234567890123456789", 10);
        check(weighted_remainder_conductor_interval_q(expected[0],expected[1],expected[2],
              expected[3],expected[4],expected[5],11,a,47));
        for (unsigned j = 0; j < 6; ++j) mpq_set_ui(out[j], 1, 1);
        mpz_ptr alias = den ? mpq_denref(out[i]) : mpq_numref(out[i]);
        mpz_set(alias, a);
        check(weighted_remainder_conductor_interval_q(out[0],out[1],out[2],out[3],out[4],out[5],11,alias,47));
        for (unsigned j = 0; j < 6; ++j) check(mpq_equal(out[j],expected[j]));
    }
    mpq_set_ui(out[0], 17, 1); mpq_set_ui(out[1], 18, 1);
    check(!weighted_remainder_beta_interval_q(out[0],out[0],2,7,31));
    unsigned bd[][3] = {{1,7,31},{8,7,31},{2,241,31},{2,7,1}};
    for (unsigned i = 0; i < sizeof(bd)/sizeof(*bd); ++i)
        check(!weighted_remainder_beta_interval_q(out[0],out[1],bd[i][0],bd[i][1],bd[i][2]));
    check(mpq_cmp_ui(out[0],17,1)==0 && mpq_cmp_ui(out[1],18,1)==0);
    unsigned best = 47, count = 53, calls = 0;
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],&best,&count,13,31,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],&best,&count,2,31,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],&best,&count,7,1,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[0],&best,&count,7,31,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],&best,&best,7,31,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],NULL,&count,7,31,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],&best,NULL,7,31,NULL,NULL));
    check(!weighted_remainder_conductor_extrema_q(out[0],out[1],&best,&count,7,31,abort_visit,&calls));
    check(calls==1 && best==47 && count==53);
    check(mpq_cmp_ui(out[0],17,1)==0 && mpq_cmp_ui(out[1],18,1)==0);
    mpz_set_ui(a, 123); mpz_set(saved,a);
    check(!weighted_remainder_conductor_period_z(a,1)); check(mpz_cmp(a,saved)==0);
    check(!weighted_remainder_conductor_period_z(a,241)); check(mpz_cmp(a,saved)==0);
    unsigned bp[][2] = {{2,2},{7,4},{7,3},{7,11},{241,239},{7,0},{7,~0u}};
    for (unsigned i = 0; i < sizeof(bp)/sizeof(*bp); ++i) {
        check(!weighted_remainder_prime_candidate_z(a,bp[i][0],bp[i][1]));
        check(mpz_cmp(a,saved)==0);
    }
    for (unsigned i = 0; i < 6; ++i) mpq_clears(out[i],expected[i],NULL);
    mpz_clears(a,saved,NULL);
    printf("api_checks=%u\n",checks);
}

int main(int argc, char **argv)
{
    if (argc==2 && strcmp(argv[1],"--self-test")==0) { self_test(); return 0; }
    if (argc!=2 || strcmp(argv[1],"--stream")!=0) return 2;
    char *line=NULL;
    size_t size=0;
    while (getline(&line,&size,stdin)>=0) {
        char *args[12]={(char *)"nfield",(char *)"weighted-remainder-state"};
        int count=2;
        char *save=NULL;
        for (char *p=strtok_r(line," \t\r\n",&save);p;p=strtok_r(NULL," \t\r\n",&save)) {
            if (count==12) { free(line); return 2; }
            args[count++]=p;
        }
        if (count<3) continue;
        puts("BEGIN");
        int status=weighted_remainder_conductor_command(count,args);
        printf("exit=%d\nEND\n",status);
    }
    free(line);
    return 0;
}
