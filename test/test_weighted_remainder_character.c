#include "weighted_remainder_character.h"
#include "finite_character_core.h"
#include <stdio.h>
#include <stdlib.h>

#define CFIELDS(X) X(cotangent_coefficient) X(l_one_conjugate) X(l_two_prefix) X(l_two) X(mixed_product)
#define MFIELDS(X) X(delta) X(zeta_lower) X(zeta_upper) X(denominator_lower) X(denominator_upper) \
    X(eta_lower) X(eta_upper) X(positive_amplitude_lower) X(positive_amplitude_upper)
static unsigned edges;
static void check(int ok) { ++edges;if (!ok) { fprintf(stderr,"character edge %u failed\n",edges);exit(1); } }
static void rect_print(const WeightedRemainderComplex *s)
{
    gmp_printf(" %Qd %Qd %Qd %Qd",s->real_lower,s->real_upper,s->imag_lower,s->imag_upper);
}
static void rect_sentinel(WeightedRemainderComplex *s)
{
    mpq_set_si(s->real_lower,-31,7);mpq_set_si(s->real_upper,11,13);
    mpq_set_si(s->imag_lower,-17,19);mpq_set_si(s->imag_upper,23,29);
}
static int rect_unchanged(const WeightedRemainderComplex *s)
{
    return !mpq_cmp_si(s->real_lower,-31,7) && !mpq_cmp_si(s->real_upper,11,13) &&
        !mpq_cmp_si(s->imag_lower,-17,19) && !mpq_cmp_si(s->imag_upper,23,29);
}
static void edge_checks(void)
{
    WeightedRemainderCharacter c;weighted_remainder_character_init(&c);
    c.modulus=91;c.index=92;c.conductor=93;c.denominator=94;c.cutoff=95;mpq_set_si(c.l_two_tail,-13,11);
#define SENT(f) rect_sentinel(&c.f);
    CFIELDS(SENT)
#undef SENT
    unsigned invalid[][3]={{0,0,1},{1,0,1},{241,1,1},{3,3,1},{3,1,0},{3,1,241},
        {3,0,1},{2,0,240},{240,~0u,1},{~0u,1,1}};
    for (unsigned i=0;i<sizeof(invalid)/sizeof(*invalid);++i) {
        check(!weighted_remainder_character_compute(&c,invalid[i][0],invalid[i][1],invalid[i][2]));
        check(c.modulus==91 && c.index==92 && c.conductor==93 && c.denominator==94 && c.cutoff==95);
        check(!mpq_cmp_si(c.l_two_tail,-13,11));
#define SAME(f) check(rect_unchanged(&c.f));
        CFIELDS(SAME)
#undef SAME
    }
    check(!weighted_remainder_character_compute(NULL,3,1,1));
    check(weighted_remainder_character_compute(&c,3,1,1));
    check(c.modulus==3 && c.conductor==3 && c.cutoff==1);
    check(weighted_remainder_character_compute(&c,6,1,240));
    check(c.modulus==6 && c.conductor==3 && c.cutoff==240);
    weighted_remainder_character_clear(&c);
    WeightedRemainderMixedMoment m;weighted_remainder_mixed_moment_init(&m);
    m.modulus=71;m.cutoff=72;m.zeta_cutoff=73;m.period_cutoff=74;
    m.character_count=75;m.odd_count=76;m.induced_odd_count=77;rect_sentinel(&m.mixed_moment);
#define SET(f) mpq_set_si(m.f,-13,11);
    MFIELDS(SET)
#undef SET
    unsigned bad[][4]={{1,1,1,2},{241,1,1,2},{2,0,1,2},{2,241,1,2},
        {2,1,0,2},{2,1,241,2},{2,1,1,1},{2,1,1,241}};
    for (unsigned i=0;i<sizeof(bad)/sizeof(*bad);++i) {
        check(!weighted_remainder_mixed_moment_compute(&m,bad[i][0],bad[i][1],bad[i][2],bad[i][3]));
        check(m.modulus==71 && m.cutoff==72 && m.zeta_cutoff==73 && m.period_cutoff==74 &&
            m.character_count==75 && m.odd_count==76 && m.induced_odd_count==77);
        check(rect_unchanged(&m.mixed_moment));
#define SAME(f) check(!mpq_cmp_si(m.f,-13,11));
        MFIELDS(SAME)
#undef SAME
    }
    check(!weighted_remainder_mixed_moment_compute(NULL,2,1,1,2));
    check(weighted_remainder_mixed_moment_compute(&m,2,1,240,2));
    check(m.odd_count==0 && m.induced_odd_count==0 && !mpq_cmp_ui(m.eta_lower,1,2) &&
        !mpq_cmp_ui(m.eta_upper,1,2) && !mpq_cmp_ui(m.positive_amplitude_lower,1,2) &&
        !mpq_cmp_ui(m.positive_amplitude_upper,1,2));
    check(weighted_remainder_mixed_moment_compute(&m,6,240,1,7));
    check(m.odd_count==1 && m.induced_odd_count==1);
    weighted_remainder_mixed_moment_clear(&m);
}
int main(void)
{
    edge_checks();printf("EDGES %u\n",edges);
    char mode;unsigned q,a,b,c;
    while (scanf(" %c %u %u %u %u",&mode,&q,&a,&b,&c)==5) {
        if (mode=='C') {
            WeightedRemainderCharacter s;weighted_remainder_character_init(&s);
            int ok=weighted_remainder_character_compute(&s,q,a,b);printf("C %d",ok);
            if (ok) {
                printf(" %u %u %u %u %u",s.modulus,s.index,s.conductor,s.denominator,s.cutoff);
#define PRINT(f) rect_print(&s.f);
                CFIELDS(PRINT)
#undef PRINT
                gmp_printf(" %Qd",s.l_two_tail);
            }
            putchar('\n');weighted_remainder_character_clear(&s);
        } else if (mode=='A') {
            FiniteCharacterTable table={0};
            int ok=q>=2 && q<=240 && a>=1 && a<=240 && finite_character_table_build((int)q,&table);
            unsigned count=0;if (ok) for (int i=0;i<table.count;++i) if (table.odd[i]) ++count;
            printf("A %d %u\n",ok,count);
            if (ok) for (int i=0;i<table.count;++i) if (table.odd[i]) {
                WeightedRemainderCharacter s;weighted_remainder_character_init(&s);
                if (!weighted_remainder_character_compute(&s,q,(unsigned)i,a)) return 2;
                printf("R %u %u %u %u %u",s.modulus,s.index,s.conductor,s.denominator,s.cutoff);
                for (unsigned r=0;r<q;++r) printf(" %d",table.phase[i*q+r]);
#define PRINT(f) rect_print(&s.f);
                CFIELDS(PRINT)
#undef PRINT
                gmp_printf(" %Qd\n",s.l_two_tail);weighted_remainder_character_clear(&s);
            }
            finite_character_table_free(&table);
        } else if (mode=='M') {
            WeightedRemainderMixedMoment s;weighted_remainder_mixed_moment_init(&s);
            int ok=weighted_remainder_mixed_moment_compute(&s,q,a,b,c);printf("M %d",ok);
            if (ok) {
                printf(" %u %u %u %u %u %u %u",s.modulus,s.cutoff,s.zeta_cutoff,s.period_cutoff,
                    s.character_count,s.odd_count,s.induced_odd_count);rect_print(&s.mixed_moment);
#define PRINT(f) gmp_printf(" %Qd",s.f);
                MFIELDS(PRINT)
#undef PRINT
            }
            putchar('\n');weighted_remainder_mixed_moment_clear(&s);
        } else return 3;
    }
    return ferror(stdin)?4:0;
}
