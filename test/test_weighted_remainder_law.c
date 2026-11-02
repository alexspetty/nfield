#include "weighted_remainder_law.h"
#include <stdio.h>
#include <stdlib.h>
#define CHECK(x) do { if (!(x)) { fprintf(stderr,"law API assertion at %d\n",__LINE__);exit(1); } } while (0)
int main(void)
{
    WeightedRemainderLaw s;weighted_remainder_law_init(&s);
    mpq_t a,b,margin,hold;mpq_inits(a,b,margin,hold,NULL);mpq_set_ui(margin,1,10);
    CHECK(weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,3,2,a,b,margin));
    CHECK(s.period==6 && mpq_sgn(s.finite)>0);
    CHECK(!weighted_remainder_law_compute(NULL,WEIGHTED_LAW_MOMENT,3,2,a,b,margin));
    CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,3,2,NULL,b,margin));
    CHECK(!weighted_remainder_law_compute(&s,(WeightedRemainderLawOperation)99,3,2,a,b,margin));
    mpq_set(hold,s.finite);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.finite));
    mpq_set(hold,s.absolute);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.absolute));
    mpq_set(hold,s.full_lower);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.full_lower));
    mpq_set(hold,s.full_upper);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.full_upper));
    mpq_set(hold,s.squared_l2_error);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.squared_l2_error));
    mpq_set(hold,s.probability_error);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.probability_error));
    mpq_set(hold,s.finite_expanded);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.finite_expanded));
    mpq_set(hold,s.real_lower);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.real_lower));
    mpq_set(hold,s.real_upper);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.real_upper));
    mpq_set(hold,s.rounding_width);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.rounding_width));
    mpq_set(hold,s.characteristic_error_upper);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_MOMENT,13,2,a,b,margin));CHECK(!mpq_cmp(hold,s.characteristic_error_upper));
    mpq_set_ui(s.finite,1,7);
    CHECK(weighted_remainder_law_compute(&s,WEIGHTED_LAW_CHARACTERISTIC,3,0,s.finite,b,margin));
    CHECK(mpq_cmp(s.real_lower,s.real_upper)<=0 && mpq_sgn(s.rounding_width)>0);
    mpz_set_ui(mpq_denref(a),0);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_CDF,3,0,a,b,margin));mpq_set_ui(a,0,1);
    mpz_ui_pow_ui(mpq_numref(a),2,256);CHECK(!weighted_remainder_law_compute(&s,WEIGHTED_LAW_CHARACTERISTIC,2,0,a,b,margin));mpq_set_ui(a,0,1);
    mpq_set_si(a,-1,1);mpq_set_ui(b,1,1);
    mpq_t p[3],mean,second;mpq_inits(mean,second,NULL);for (unsigned i=0;i<3;++i) mpq_init(p[i]);
    CHECK(weighted_remainder_law_recurrence_q(p,mean,second,3,3,a,b));CHECK(mpq_cmp_ui(mean,1,1)==0 && mpq_cmp_ui(second,1,1)==0);
    CHECK(!weighted_remainder_law_recurrence_q(p,mean,mean,3,3,a,b));
    CHECK(!weighted_remainder_law_recurrence_q(p,p[1],second,3,3,a,b));
    CHECK(!weighted_remainder_law_recurrence_q(p,mean,second,13,3,a,b));
    mpq_set_si(p[0],-1,1);CHECK(weighted_remainder_law_recurrence_q(p,mean,second,3,3,p[0],b));CHECK(mpq_cmp_ui(p[0],1,1)==0);
    for (unsigned i=0;i<3;++i) mpq_clear(p[i]);
    mpq_clears(mean,second,NULL);
    mpq_clears(a,b,margin,hold,NULL);weighted_remainder_law_clear(&s);
    puts("PASS law API domains, aliases and preservation");return 0;
}
