#include "../src/weighted_remainder_complex.h"
#include "../src/finite_character_core.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void edge_checks(void)
{
    mpq_t a,b,c,d;mpq_inits(a,b,c,d,NULL);mpq_ptr v[]={a,b,c,d};
    for (unsigned i=0;i<4;++i) mpq_set_ui(v[i],i+1,i+2);
    unsigned invalid[][2]={{0,0},{241,0},{~0U,0},{1,1},{2,2},{240,240},{240,~0U}};
    for (unsigned i=0;i<7;++i) CHECK(!weighted_remainder_complex_phase_q(a,b,c,d,invalid[i][0],invalid[i][1]));
    for (unsigned i=0;i<4;++i) {
        mpq_ptr args[]={a,b,c,d};args[i]=NULL;
        CHECK(!weighted_remainder_complex_phase_q(args[0],args[1],args[2],args[3],2,1));
        for (unsigned j=i+1;j<4;++j) {
            mpq_ptr pair[]={a,b,c,d};pair[j]=pair[i];
            CHECK(!weighted_remainder_complex_phase_q(pair[0],pair[1],pair[2],pair[3],2,1));
        }
    }
    for (unsigned i=0;i<4;++i) CHECK(!mpq_cmp_ui(v[i],i+1,i+2));
    CHECK(weighted_remainder_complex_phase_q(a,b,c,d,1,0));
    CHECK(!mpq_cmp_ui(a,1,1) && !mpq_cmp_ui(b,1,1) && !mpq_sgn(c) && !mpq_sgn(d));
    CHECK(weighted_remainder_complex_phase_q(a,b,c,d,2,1));
    CHECK(!mpq_cmp_si(a,-1,1) && !mpq_cmp_si(b,-1,1) && !mpq_sgn(c) && !mpq_sgn(d));
    FiniteCharacterTable t={0};CHECK(!finite_character_table_build(2,NULL));
    CHECK(!finite_character_table_build(1,&t));CHECK(!finite_character_table_build(513,&t));
    CHECK(!t.phase && !t.conductor && !t.odd);CHECK(finite_character_table_build(8,&t));
    int *saved=t.phase;CHECK(!finite_character_table_build(12,&t));CHECK(t.phase==saved && t.modulus==8);
    finite_character_table_free(&t);finite_character_table_free(&t);
    CHECK(!t.phase && !t.conductor && !t.odd && !t.count);
    mpq_clears(a,b,c,d,NULL);printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();mpq_t a,b,c,d;mpq_inits(a,b,c,d,NULL);char op;unsigned q,k;
    while (scanf(" %c %u %u",&op,&q,&k)==3) {
        if (op=='P') {
            int ok=weighted_remainder_complex_phase_q(a,b,c,d,q,k);printf("P %d",ok);
            if (ok) gmp_printf(" %Qd %Qd %Qd %Qd",a,b,c,d);
            putchar('\n');
        } else if (op=='T') {
            FiniteCharacterTable t={0};int ok=q<=512 && finite_character_table_build((int)q,&t);
            printf("T %d",ok);
            if (ok) printf(" %d %d %d",t.modulus,t.count,t.denominator);
            putchar('\n');
            if (ok) for (int ch=0;ch<t.count;++ch) {
                printf("R %d %d %u",ch,t.conductor[ch],t.odd[ch]);
                for (int r=0;r<t.modulus;++r) printf(" %d",t.phase[(size_t)ch*t.modulus+r]);
                putchar('\n');
            }
            finite_character_table_free(&t);
        } else return 2;
    }
    mpq_clears(a,b,c,d,NULL);return 0;
}
