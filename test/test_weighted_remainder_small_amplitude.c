#include "weighted_remainder_small_amplitude.h"
#include <stdio.h>
#include <stdlib.h>

#define FIELDS(X) X(three_prefix) X(three_lower) X(three_upper) X(catalan_prefix) X(catalan_lower) X(catalan_upper) \
    X(six_prefix) X(six_lower) X(six_upper) X(induced_prefix_rhs) X(induced_factor) X(induced_lower) X(induced_upper) \
    X(l_tail_upper) X(zeta_lower) X(zeta_upper) X(sqrt_three_lower) X(sqrt_three_upper) \
    X(eta_three_lower) X(eta_three_upper) X(eta_four_lower) X(eta_four_upper) \
    X(eta_six_direct_lower) X(eta_six_direct_upper) X(eta_six_relation_lower) X(eta_six_relation_upper)
static unsigned edges;
static void check(int ok) { ++edges;if (!ok) { fprintf(stderr,"small amplitude edge %u failed\n",edges);exit(1); } }
static void edge_checks(void)
{
    WeightedRemainderSmallAmplitude s;weighted_remainder_small_amplitude_init(&s);
    s.cutoff=71;s.zeta_cutoff=72;
#define SET(f) mpq_set_si(s.f,-13,11);
    FIELDS(SET)
#undef SET
    unsigned bad[][2]={{0,1},{241,1},{1,0},{1,241},{~0u,1}};
    for (unsigned i=0;i<5;++i) {
        check(!weighted_remainder_small_amplitude_compute(&s,bad[i][0],bad[i][1]));
        check(s.cutoff==71 && s.zeta_cutoff==72);
#define SAME(f) check(!mpq_cmp_si(s.f,-13,11));
        FIELDS(SAME)
#undef SAME
    }
    check(!weighted_remainder_small_amplitude_compute(NULL,1,1));
    check(weighted_remainder_small_amplitude_compute(&s,1,240));
    check(!mpq_cmp_ui(s.three_prefix,1,1) && !mpq_cmp_ui(s.catalan_prefix,1,1) &&
        !mpq_cmp_ui(s.six_prefix,1,1) && !mpq_cmp(s.induced_prefix_rhs,s.six_prefix));
    check(weighted_remainder_small_amplitude_compute(&s,240,1));
    check(!mpq_cmp(s.induced_prefix_rhs,s.six_prefix) && !mpq_cmp_ui(s.induced_factor,5,4));
    weighted_remainder_small_amplitude_clear(&s);
}
int main(void)
{
    edge_checks();printf("EDGES %u\n",edges);unsigned N,K;
    while (scanf(" %u %u",&N,&K)==2) {
        WeightedRemainderSmallAmplitude s;weighted_remainder_small_amplitude_init(&s);
        int ok=weighted_remainder_small_amplitude_compute(&s,N,K);printf("E %d",ok);
        if (ok) {
            printf(" %u %u",s.cutoff,s.zeta_cutoff);
#define PRINT(f) gmp_printf(" %Qd",s.f);
            FIELDS(PRINT)
#undef PRINT
        }
        putchar('\n');weighted_remainder_small_amplitude_clear(&s);
    }
    return ferror(stdin)?2:0;
}
