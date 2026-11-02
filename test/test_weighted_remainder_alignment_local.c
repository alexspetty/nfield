#include "../src/weighted_remainder_alignment_local.h"
#include <stdio.h>
#include <stdlib.h>
#define FIELDS(X) X(reset_factor) X(reset_numerator) X(reset_average) \
    X(alignment_factor) X(alignment_numerator) X(alignment_average) \
    X(alignment_tail) X(limiting_factor) X(limiting_average) \
    X(reset_factor_relative_loss) X(reset_average_loss) \
    X(alignment_factor_relative_loss) X(alignment_average_loss) \
    X(absent_factor) X(absent_average)
static unsigned checks;
static void require(int yes) { ++checks;if (!yes) exit(7); }
int main(void)
{
    WeightedRemainderAlignmentLocal s;weighted_remainder_alignment_local_init(&s);
    require(!weighted_remainder_alignment_local_compute(NULL,2,1));
    s.prime=37;s.valuation=29;
#define SEED(f) mpq_set_si(s.f,-31,7);
    FIELDS(SEED)
#undef SEED
    unsigned rejected[][2]={{0,0},{1,1},{4,2},{240,1},{241,1},{2,241},{239,1000000}};
    for (unsigned j=0;j<sizeof(rejected)/sizeof(*rejected);++j) {
        require(!weighted_remainder_alignment_local_compute(&s,rejected[j][0],rejected[j][1]));
        require(s.prime==37 && s.valuation==29);
#define SAME(f) require(mpq_cmp_si(s.f,-31,7)==0);
        FIELDS(SAME)
#undef SAME
    }
    unsigned p,v;
    while (scanf("%u %u",&p,&v)==2) {
        int ok=weighted_remainder_alignment_local_compute(&s,p,v);
        printf("%u %u %d",p,v,ok);
        if (ok) {
            require(s.prime==p && s.valuation==v);
#define PRINT(f) gmp_printf(" %Qd",s.f);
            FIELDS(PRINT)
#undef PRINT
        }
        putchar('\n');
    }
    weighted_remainder_alignment_local_clear(&s);fprintf(stderr,"C_ASSERTIONS %u\n",checks);return 0;
}
