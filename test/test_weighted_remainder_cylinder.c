#include "../src/weighted_remainder_cylinder.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static unsigned edge_checks;
#define EDGE(expression) do { assert(expression); ++edge_checks; } while (0)

static void seed(mpq_t *q, unsigned n)
{
    for (unsigned i = 0; i < n; ++i) mpq_set_ui(q[i], 2*i+3, 2*i+5);
}

static void preserved(mpq_t *q, unsigned n)
{
    for (unsigned i = 0; i < n; ++i) EDGE(mpq_cmp_ui(q[i], 2*i+3, 2*i+5) == 0);
}

int main(void)
{
    mpq_t q[5], saved[5], threshold;
    mpz_t address;
    mpz_init_set_si(address, -1);
    mpq_init(threshold);
    for (unsigned i = 0; i < 5; ++i) { mpq_init(q[i]); mpq_init(saved[i]); }
    seed(q, 5);
    const unsigned bad[][2] = {{0,2},{241,240},{2,1},{2,241},{UINT_MAX,240},{2,UINT_MAX}};
    for (unsigned i = 0; i < 6; ++i) {
        EDGE(!weighted_remainder_cylinder_q(q[0],q[1],q[2],q[3],bad[i][0],address,bad[i][1]));
        preserved(q,5);
    }
    for (unsigned i = 0; i < 4; ++i) for (unsigned j = i+1; j < 4; ++j) {
        mpq_ptr v[] = {q[0],q[1],q[2],q[3]}; v[j]=v[i];
        EDGE(!weighted_remainder_cylinder_q(v[0],v[1],v[2],v[3],2,address,2)); preserved(q,5);
    }
    const unsigned bad_position[][2] = {{0,2},{1,2},{3,2},{241,240},{2,1},{2,241},{2,UINT_MAX}};
    for (unsigned i = 0; i < 7; ++i) {
        EDGE(!weighted_remainder_position_q(q[0],q[1],q[2],q[3],q[4],bad_position[i][0],address,bad_position[i][1],threshold));
        EDGE(!weighted_remainder_position_weight_q(q[0],q[1],q[2],bad_position[i][0],address,2,bad_position[i][1]));
        preserved(q,5);
    }
    EDGE(!weighted_remainder_position_weight_q(q[0],q[1],q[2],2,address,UINT_MAX,2)); preserved(q,5);
    for (unsigned i = 0; i < 5; ++i) for (unsigned j = i+1; j < 5; ++j) {
        mpq_ptr v[] = {q[0],q[1],q[2],q[3],q[4]}; v[j]=v[i];
        EDGE(!weighted_remainder_position_q(v[0],v[1],v[2],v[3],v[4],2,address,2,threshold)); preserved(q,5);
        if (j < 3) { EDGE(!weighted_remainder_position_weight_q(v[0],v[1],v[2],2,address,2,2)); preserved(q,5); }
    }
    mpz_set_ui(mpq_denref(threshold),0);
    EDGE(!weighted_remainder_position_q(q[0],q[1],q[2],q[3],q[4],2,address,2,threshold)); preserved(q,5);
    mpq_set_ui(threshold,1,2); mpz_neg(mpq_denref(threshold),mpq_denref(threshold));
    EDGE(!weighted_remainder_position_q(q[0],q[1],q[2],q[3],q[4],2,address,2,threshold)); preserved(q,5);
    mpq_set_ui(threshold,2,4);
    EDGE(!weighted_remainder_position_q(q[0],q[1],q[2],q[3],q[4],2,address,2,threshold)); preserved(q,5);
    mpq_set_ui(threshold,1,3);
    EDGE(weighted_remainder_position_q(saved[0],saved[1],saved[2],saved[3],saved[4],6,address,24,threshold));
    for (unsigned j = 0; j < 5; ++j) {
        mpq_set(q[j],threshold);
        EDGE(weighted_remainder_position_q(q[0],q[1],q[2],q[3],q[4],6,address,24,q[j]));
        for (unsigned i = 0; i < 5; ++i) EDGE(mpq_equal(q[i],saved[i]));
    }
    EDGE(weighted_remainder_cylinder_q(saved[0],saved[1],saved[2],saved[3],6,address,24));
    for (unsigned j = 0; j < 4; ++j) {
        mpq_set_si(q[j],-1,1);
        EDGE(weighted_remainder_cylinder_q(q[0],q[1],q[2],q[3],6,mpq_numref(q[j]),24));
        for (unsigned i = 0; i < 4; ++i) EDGE(mpq_equal(q[i],saved[i]));
    }
    printf("edges %u PASS\n",edge_checks);

    const unsigned moduli[] = {1,2,3,4,6,7,12,24,31,60,120,239,240};
    const unsigned cuts[] = {2,3,6,12,24,31,60,120,239,240};
    const char *addresses[] = {"0","1","-1","-2","99999999999999999999999999999999999999999999999999"};
    const long numerators[] = {-1,0,1,1,1,4};
    const unsigned denominators[] = {3,1,3,2,1,3};
    const unsigned periods[] = {0,1,2,3,4,6,7,12,31,239,240};
    for (unsigned l = 0; l < sizeof(moduli)/sizeof(*moduli); ++l)
      for (unsigned b = 0; b < sizeof(addresses)/sizeof(*addresses); ++b) {
        unsigned L = moduli[l]; mpz_set_str(address,addresses[b],10);
        for (unsigned j = 0; j < sizeof(cuts)/sizeof(*cuts); ++j) {
            unsigned M = cuts[j];
            assert(weighted_remainder_cylinder_q(q[0],q[1],q[2],q[3],L,address,M));
            gmp_printf("cylinder %u %Zd %u %Qd %Qd %Qd %Qd\n",L,address,M,q[0],q[1],q[2],q[3]);
            if (L < 2 || L > M) continue;
            for (unsigned t = 0; t < 6; ++t) {
                mpq_set_si(threshold,numerators[t],denominators[t]);
                assert(weighted_remainder_position_q(q[0],q[1],q[2],q[3],q[4],L,address,M,threshold));
                gmp_printf("position %u %Zd %u %Qd %Qd %Qd %Qd %Qd %Qd\n",L,address,M,threshold,q[0],q[1],q[2],q[3],q[4]);
            }
            for (unsigned t = 0; t < sizeof(periods)/sizeof(*periods); ++t) {
                unsigned k = periods[t];
                assert(weighted_remainder_position_weight_q(q[0],q[1],q[2],L,address,k,M));
                gmp_printf("weight %u %Zd %u %u %Qd %Qd %Qd\n",L,address,k,M,q[0],q[1],q[2]);
            }
        }
      }
    /* Exhaust every residue for a separate set of modest cylinders. */
    for (unsigned L = 2; L <= 16; ++L) for (unsigned a = 0; a < L; ++a) {
        mpz_set_ui(address,a);
        assert(weighted_remainder_cylinder_q(q[0],q[1],q[2],q[3],L,address,24));
        gmp_printf("cylinder %u %Zd 24 %Qd %Qd %Qd %Qd\n",L,address,q[0],q[1],q[2],q[3]);
    }
    for (unsigned i = 0; i < 5; ++i) { mpq_clear(q[i]); mpq_clear(saved[i]); }
    mpq_clear(threshold); mpz_clear(address);
    return 0;
}
