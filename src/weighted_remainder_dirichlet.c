#include "weighted_remainder_dirichlet.h"

#define FIELDS(X) X(exponent) \
    X(zeta_prefix_lower) X(zeta_prefix_upper) X(zeta_tail_upper) X(zeta_lower) X(zeta_upper) \
    X(doubled_prefix_lower) X(doubled_prefix_upper) X(doubled_tail_upper) X(doubled_lower) X(doubled_upper) \
    X(prefix_lower) X(prefix_upper) X(formula_lower) X(formula_upper) \
    X(special_lower) X(special_upper) X(lower) X(upper) X(tail_upper)
#define DIAGNOSTIC_FIELDS(X) X(two_weight) X(three_halves_weight) X(loss_lower) X(loss_upper) \
    X(margin_lower) X(margin_upper) X(literal_loss_bound) X(literal_margin)

int weighted_remainder_divisor_deficit_q(mpq_t out,unsigned n)
{
    if (!out || n>WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    if (n<2) { mpq_set_ui(out,0,1);return 1; }
    unsigned count=0,remaining=n;
    for (unsigned p=2;p<=remaining;++p) if (remaining%p==0) {
        ++count;do remaining/=p;while (remaining%p==0);
    }
    mpq_set_ui(out,(1U<<(count-1))-1,1);return 1;
}

void weighted_remainder_dirichlet_init(WeightedRemainderDirichlet *s)
{
    s->cutoff=s->specialization=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}

void weighted_remainder_dirichlet_clear(WeightedRemainderDirichlet *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}

static void formula_interval(WeightedRemainderDirichlet *s)
{
    mpq_t c,t;mpq_inits(c,t,NULL);mpq_set_ui(c,2,1);
    mpq_mul(t,c,s->doubled_upper);mpq_mul(s->formula_lower,s->zeta_lower,s->zeta_lower);
    mpq_div(s->formula_lower,s->formula_lower,t);mpq_sub(s->formula_lower,s->formula_lower,s->zeta_upper);
    mpq_mul(t,c,s->doubled_lower);mpq_mul(s->formula_upper,s->zeta_upper,s->zeta_upper);
    mpq_div(s->formula_upper,s->formula_upper,t);mpq_sub(s->formula_upper,s->formula_upper,s->zeta_lower);
    mpq_set_ui(c,1,2);mpq_add(s->formula_lower,s->formula_lower,c);mpq_add(s->formula_upper,s->formula_upper,c);
    mpq_clears(c,t,NULL);
}

int weighted_remainder_dirichlet_compute(WeightedRemainderDirichlet *out,const mpq_t exponent,unsigned N)
{
    if (!out || N<1 || N>WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t l,h,t,c,doubled,previous;mpq_inits(l,h,t,c,doubled,previous,NULL);
    /* Validate canonical input before comparisons; doubling stays inside
     * the power kernel's 256-bit domain. Nothing in out is changed yet. */
    int valid=weighted_remainder_power_interval_q(l,h,1,exponent);
    if (!valid || mpq_cmp_ui(exponent,1,1)<=0 || mpq_cmp_ui(exponent,6,1)>0 ||
        mpz_sizeinbase(mpq_numref(exponent),2)>255 || mpz_sizeinbase(mpq_denref(exponent),2)>255) {
        mpq_clears(l,h,t,c,doubled,previous,NULL);return 0;
    }
    WeightedRemainderDirichlet s;weighted_remainder_dirichlet_init(&s);
    s.cutoff=N;mpq_set(s.exponent,exponent);
    mpq_set_ui(c,2,1);mpq_mul(doubled,s.exponent,c);
    for (unsigned n=1;n<=N;++n) {
        weighted_remainder_power_interval_q(l,h,n,s.exponent);
        mpq_add(s.zeta_prefix_lower,s.zeta_prefix_lower,l);mpq_add(s.zeta_prefix_upper,s.zeta_prefix_upper,h);
        weighted_remainder_divisor_deficit_q(c,n);
        mpq_mul(t,c,l);mpq_add(s.prefix_lower,s.prefix_lower,t);
        mpq_mul(t,c,h);mpq_add(s.prefix_upper,s.prefix_upper,t);
        weighted_remainder_power_interval_q(l,h,n,doubled);
        mpq_add(s.doubled_prefix_lower,s.doubled_prefix_lower,l);mpq_add(s.doubled_prefix_upper,s.doubled_prefix_upper,h);
    }
    mpq_set_ui(c,1,1);mpq_sub(previous,s.exponent,c);
    weighted_remainder_power_interval_q(l,h,N,previous);mpq_div(s.zeta_tail_upper,h,previous);
    mpq_sub(previous,doubled,c);weighted_remainder_power_interval_q(l,h,N,previous);
    mpq_div(s.doubled_tail_upper,h,previous);
    mpq_set(s.zeta_lower,s.zeta_prefix_lower);mpq_add(s.zeta_upper,s.zeta_prefix_upper,s.zeta_tail_upper);
    mpq_set(s.doubled_lower,s.doubled_prefix_lower);mpq_add(s.doubled_upper,s.doubled_prefix_upper,s.doubled_tail_upper);
    formula_interval(&s);
    mpq_set(s.lower,s.formula_lower);
    if (mpq_sgn(s.lower)<0) mpq_set_ui(s.lower,0,1);
    if (mpq_cmp(s.lower,s.prefix_lower)<0) mpq_set(s.lower,s.prefix_lower);
    mpq_set(s.upper,s.formula_upper);
    if (mpq_cmp_ui(s.exponent,2,1)==0) {
        s.specialization=2;
        WeightedRemainderConstants constants;weighted_remainder_constants_init(&constants);
        weighted_remainder_constants_compute(&constants,1);
        mpq_set_ui(c,7,4);mpq_sub(s.special_lower,c,constants.zeta_two_upper);
        mpq_sub(s.special_upper,c,constants.zeta_two_lower);
        mpq_set_ui(c,1,8);if (mpq_cmp(s.special_upper,c)>0) mpq_set(s.special_upper,c);
        weighted_remainder_constants_clear(&constants);
    } else if (mpq_cmp_ui(s.exponent,3,2)==0) {
        s.specialization=3;mpq_set_ui(s.special_upper,67,80);
    }
    if (s.specialization) {
        if (mpq_cmp(s.lower,s.special_lower)<0) mpq_set(s.lower,s.special_lower);
        if (mpq_cmp(s.upper,s.special_upper)>0) mpq_set(s.upper,s.special_upper);
    }
    mpq_sub(s.tail_upper,s.upper,s.prefix_lower);
    /* Move GMP ownership only after every input has been consumed. */
    WeightedRemainderDirichlet old=*out;*out=s;weighted_remainder_dirichlet_clear(&old);
    mpq_clears(l,h,t,c,doubled,previous,NULL);return 1;
}

void weighted_remainder_deficit_diagnostic_init(WeightedRemainderDeficitDiagnostic *s)
{
    weighted_remainder_dirichlet_init(&s->two);weighted_remainder_dirichlet_init(&s->three_halves);
#define INIT(f) mpq_init(s->f);
    DIAGNOSTIC_FIELDS(INIT)
#undef INIT
}

void weighted_remainder_deficit_diagnostic_clear(WeightedRemainderDeficitDiagnostic *s)
{
    weighted_remainder_dirichlet_clear(&s->two);weighted_remainder_dirichlet_clear(&s->three_halves);
#define CLEAR(f) mpq_clear(s->f);
    DIAGNOSTIC_FIELDS(CLEAR)
#undef CLEAR
}

int weighted_remainder_deficit_diagnostic_compute(WeightedRemainderDeficitDiagnostic *out,unsigned N)
{
    if (!out || N<1 || N>WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    WeightedRemainderDeficitDiagnostic s;weighted_remainder_deficit_diagnostic_init(&s);
    mpq_t c,t;mpq_inits(c,t,NULL);
    mpq_set_ui(c,2,1);weighted_remainder_dirichlet_compute(&s.two,c,N);
    mpq_set_ui(c,3,2);weighted_remainder_dirichlet_compute(&s.three_halves,c,N);
    mpq_set_ui(s.two_weight,3,2);mpq_set_ui(s.three_halves_weight,37,100);
    mpq_mul(s.loss_lower,s.two_weight,s.two.lower);mpq_mul(t,s.three_halves_weight,s.three_halves.lower);
    mpq_add(s.loss_lower,s.loss_lower,t);
    mpq_mul(s.loss_upper,s.two_weight,s.two.upper);mpq_mul(t,s.three_halves_weight,s.three_halves.upper);
    mpq_add(s.loss_upper,s.loss_upper,t);
    mpq_set_ui(c,1,1);mpq_sub(s.margin_lower,c,s.loss_upper);mpq_sub(s.margin_upper,c,s.loss_lower);
    mpq_set_ui(s.literal_loss_bound,3979,8000);mpq_set_ui(s.literal_margin,4021,8000);
    WeightedRemainderDeficitDiagnostic old=*out;*out=s;weighted_remainder_deficit_diagnostic_clear(&old);
    mpq_clears(c,t,NULL);return 1;
}
