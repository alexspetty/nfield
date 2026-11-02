#include "weighted_remainder_cotangent.h"
#include <stdio.h>
#include <stdlib.h>

#define FIELDS(X) X(residue_bound) X(unit_residue_bound) X(prefix_lower) X(prefix_upper) \
    X(unit_prefix_lower) X(unit_prefix_upper) X(tail_upper) X(unit_tail_upper) X(lower) X(upper) \
    X(unit_lower) X(unit_upper) X(gcd_prefix_lower) X(gcd_prefix_upper) X(mobius_prefix_lower) \
    X(mobius_prefix_upper) X(gcd_lower) X(gcd_upper) X(mobius_lower) X(mobius_upper) \
    X(zeta_lower) X(zeta_upper) X(delta) X(harmonic_seed_lower) X(harmonic_seed_upper) X(eta_lower) X(eta_upper)
static unsigned edges;
static void check(int ok) { ++edges;if (!ok) { fprintf(stderr,"cotangent edge %u failed\n",edges);exit(1); } }
static void edge_checks(void)
{
    mpq_t a,b,c,d;mpq_inits(a,b,c,d,NULL);mpq_ptr out[]={a,b,c,d};
    for (unsigned i=0;i<4;++i) mpq_set_si(out[i],-17,13);
    for (unsigned i=0;i<4;++i) for (unsigned j=i+1;j<4;++j) {
        mpq_ptr p[]={a,b,c,d};p[j]=p[i];
        check(!weighted_remainder_cotangent_prefix_q(p[0],p[1],p[2],p[3],3,7));
        for (unsigned k=0;k<4;++k) check(!mpq_cmp_si(out[k],-17,13));
    }
    for (unsigned i=0;i<4;++i) {
        mpq_ptr p[]={a,b,c,d};p[i]=NULL;
        check(!weighted_remainder_cotangent_prefix_q(p[0],p[1],p[2],p[3],3,7));
    }
    check(!weighted_remainder_cotangent_prefix_q(a,b,c,d,0,7));
    check(!weighted_remainder_cotangent_prefix_q(a,b,c,d,241,7));
    check(!weighted_remainder_cotangent_prefix_q(a,b,c,d,3,241));
    check(weighted_remainder_cotangent_prefix_q(a,b,c,d,1,240));
    for (unsigned k=0;k<4;++k) check(!mpq_sgn(out[k]));
    check(weighted_remainder_cotangent_prefix_q(a,b,c,d,240,0));
    for (unsigned k=0;k<4;++k) check(!mpq_sgn(out[k]));
    mpq_clears(a,b,c,d,NULL);
    WeightedRemainderCotangent s;weighted_remainder_cotangent_init(&s);
    s.modulus=71;s.cutoff=72;s.zeta_cutoff=73;
#define SET(f) mpq_set_si(s.f,-13,11);
    FIELDS(SET)
#undef SET
    unsigned bad[][3]={{0,1,1},{241,1,1},{3,0,1},{3,241,1},{3,1,0},{3,1,241},{~0u,1,1}};
    for (unsigned i=0;i<sizeof(bad)/sizeof(*bad);++i) {
        check(!weighted_remainder_cotangent_compute(&s,bad[i][0],bad[i][1],bad[i][2]));
        check(s.modulus==71 && s.cutoff==72 && s.zeta_cutoff==73);
#define SAME(f) check(!mpq_cmp_si(s.f,-13,11));
        FIELDS(SAME)
#undef SAME
    }
    check(!weighted_remainder_cotangent_compute(NULL,3,7,11));
    check(weighted_remainder_cotangent_compute(&s,1,1,1));
    check(!mpq_sgn(s.lower) && !mpq_sgn(s.upper) && !mpq_sgn(s.unit_lower) && !mpq_sgn(s.unit_upper));
    check(!mpq_cmp_ui(s.eta_lower,1,1) && !mpq_cmp_ui(s.eta_upper,1,1));
    check(weighted_remainder_cotangent_compute(&s,2,240,240));
    check(!mpq_sgn(s.tail_upper) && !mpq_sgn(s.unit_tail_upper) &&
        !mpq_cmp_ui(s.eta_lower,1,2) && !mpq_cmp_ui(s.eta_upper,1,2));
    weighted_remainder_cotangent_clear(&s);
}
int main(void)
{
    edge_checks();printf("EDGES %u\n",edges);
    char mode;unsigned q,N,K;
    while (scanf(" %c %u %u %u",&mode,&q,&N,&K)==4) {
        if (mode=='P') {
            mpq_t a,b,c,d;mpq_inits(a,b,c,d,NULL);
            int ok=weighted_remainder_cotangent_prefix_q(a,b,c,d,q,N);printf("P %d",ok);
            if (ok) gmp_printf(" %Qd %Qd %Qd %Qd",a,b,c,d);
            putchar('\n');mpq_clears(a,b,c,d,NULL);
        } else if (mode=='C') {
            WeightedRemainderCotangent s;weighted_remainder_cotangent_init(&s);
            int ok=weighted_remainder_cotangent_compute(&s,q,N,K);printf("C %d",ok);
            if (ok) {
                printf(" %u %u %u",s.modulus,s.cutoff,s.zeta_cutoff);
#define PRINT(f) gmp_printf(" %Qd",s.f);
                FIELDS(PRINT)
#undef PRINT
            }
            putchar('\n');weighted_remainder_cotangent_clear(&s);
        } else return 2;
    }
    return ferror(stdin)?3:0;
}
