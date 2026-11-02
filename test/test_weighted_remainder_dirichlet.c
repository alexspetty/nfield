#include "../src/weighted_remainder_dirichlet.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void fields(WeightedRemainderDirichlet *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->exponent,s->zeta_prefix_lower,s->zeta_prefix_upper,s->zeta_tail_upper,s->zeta_lower,s->zeta_upper,
        s->doubled_prefix_lower,s->doubled_prefix_upper,s->doubled_tail_upper,s->doubled_lower,s->doubled_upper,
        s->prefix_lower,s->prefix_upper,s->formula_lower,s->formula_upper,
        s->special_lower,s->special_upper,s->lower,s->upper,s->tail_upper};
    for (unsigned i=0;i<20;++i) v[i]=a[i];
}

static void diagnostic_fields(WeightedRemainderDeficitDiagnostic *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->two_weight,s->three_halves_weight,s->loss_lower,s->loss_upper,
        s->margin_lower,s->margin_upper,s->literal_loss_bound,s->literal_margin};
    for (unsigned i=0;i<8;++i) v[i]=a[i];
}

static int equal(WeightedRemainderDirichlet *a,WeightedRemainderDirichlet *b)
{
    if (a->cutoff!=b->cutoff || a->specialization!=b->specialization) return 0;
    mpq_ptr av[20],bv[20];fields(a,av);fields(b,bv);
    for (unsigned i=0;i<20;++i) if (mpq_cmp(av[i],bv[i])) return 0;
    return 1;
}

static int diagnostic_equal(WeightedRemainderDeficitDiagnostic *a,WeightedRemainderDeficitDiagnostic *b)
{
    if (!equal(&a->two,&b->two) || !equal(&a->three_halves,&b->three_halves)) return 0;
    mpq_ptr av[8],bv[8];diagnostic_fields(a,av);diagnostic_fields(b,bv);
    for (unsigned i=0;i<8;++i) if (mpq_cmp(av[i],bv[i])) return 0;
    return 1;
}

static void edge_checks(void)
{
    mpq_t x,s;mpq_inits(x,s,NULL);mpq_set_ui(x,5,7);
    CHECK(!weighted_remainder_divisor_deficit_q(NULL,2));
    CHECK(!weighted_remainder_divisor_deficit_q(x,241));
    CHECK(!weighted_remainder_divisor_deficit_q(x,~0U));CHECK(!mpq_cmp_ui(x,5,7));
    CHECK(weighted_remainder_divisor_deficit_q(x,0) && !mpq_sgn(x));
    CHECK(weighted_remainder_divisor_deficit_q(x,1) && !mpq_sgn(x));
    CHECK(weighted_remainder_divisor_deficit_q(x,8) && !mpq_sgn(x));
    CHECK(weighted_remainder_divisor_deficit_q(x,6) && !mpq_cmp_ui(x,1,1));
    CHECK(weighted_remainder_divisor_deficit_q(x,210) && !mpq_cmp_ui(x,7,1));
    WeightedRemainderDirichlet a,b;weighted_remainder_dirichlet_init(&a);weighted_remainder_dirichlet_init(&b);
    mpq_set_ui(s,3,2);
    CHECK(weighted_remainder_dirichlet_compute(&a,s,12));CHECK(weighted_remainder_dirichlet_compute(&b,s,12));
    CHECK(!weighted_remainder_dirichlet_compute(&a,s,0));CHECK(equal(&a,&b));
    CHECK(!weighted_remainder_dirichlet_compute(&a,s,241));CHECK(equal(&a,&b));
    CHECK(!weighted_remainder_dirichlet_compute(&a,s,~0U));CHECK(equal(&a,&b));
    CHECK(!weighted_remainder_dirichlet_compute(NULL,s,1));
    CHECK(!weighted_remainder_dirichlet_compute(&a,NULL,1));CHECK(equal(&a,&b));
    mpq_set_ui(s,1,1);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));
    mpq_set_ui(s,601,100);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));
    mpq_set_si(s,-1,1);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));
    mpq_set_ui(s,6,4);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));
    mpz_set_ui(mpq_denref(s),0);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));
    mpz_set_si(mpq_denref(s),-1);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));
    mpz_ui_pow_ui(mpq_numref(s),2,255);mpz_add_ui(mpq_numref(s),mpq_numref(s),1);
    mpz_ui_pow_ui(mpq_denref(s),2,254);CHECK(!weighted_remainder_dirichlet_compute(&a,s,1));CHECK(equal(&a,&b));
    mpq_set_ui(s,10,7);CHECK(weighted_remainder_dirichlet_compute(&b,s,30));
    mpq_ptr av[20];fields(&a,av);
    for (unsigned i=0;i<20;++i) {
        mpq_set(av[i],s);CHECK(weighted_remainder_dirichlet_compute(&a,av[i],30));CHECK(equal(&a,&b));
    }
    mpq_set_ui(s,3,2);CHECK(weighted_remainder_dirichlet_compute(&a,s,1));
    CHECK(a.specialization==3 && !mpq_sgn(a.prefix_upper) && !mpq_cmp_ui(a.special_upper,67,80));
    mpq_set_ui(s,2,1);CHECK(weighted_remainder_dirichlet_compute(&a,s,6));
    CHECK(a.specialization==2 && !mpq_cmp_ui(a.prefix_lower,1,36) && !mpq_cmp(a.prefix_lower,a.prefix_upper));
    WeightedRemainderDeficitDiagnostic da,db;weighted_remainder_deficit_diagnostic_init(&da);weighted_remainder_deficit_diagnostic_init(&db);
    CHECK(weighted_remainder_deficit_diagnostic_compute(&da,12));CHECK(weighted_remainder_deficit_diagnostic_compute(&db,12));
    CHECK(!weighted_remainder_deficit_diagnostic_compute(&da,0));CHECK(diagnostic_equal(&da,&db));
    CHECK(!weighted_remainder_deficit_diagnostic_compute(&da,241));CHECK(diagnostic_equal(&da,&db));
    CHECK(!weighted_remainder_deficit_diagnostic_compute(&da,~0U));CHECK(diagnostic_equal(&da,&db));
    CHECK(!weighted_remainder_deficit_diagnostic_compute(NULL,1));
    CHECK(!mpq_cmp_ui(da.literal_loss_bound,3979,8000) && !mpq_cmp_ui(da.literal_margin,4021,8000));
    CHECK(mpq_cmp(da.loss_upper,da.literal_loss_bound)<=0 && mpq_cmp_ui(da.margin_lower,1,2)>0);
    for (unsigned i=1;i<=8;++i) CHECK(weighted_remainder_deficit_diagnostic_compute(&da,i));
    weighted_remainder_deficit_diagnostic_clear(&da);weighted_remainder_deficit_diagnostic_clear(&db);
    weighted_remainder_dirichlet_clear(&a);weighted_remainder_dirichlet_clear(&b);mpq_clears(x,s,NULL);
    printf("EDGES %u\n",edges);
}

static void print_series(WeightedRemainderDirichlet *s)
{
    printf(" %u %u",s->cutoff,s->specialization);mpq_ptr v[20];fields(s,v);
    for (unsigned i=0;i<20;++i) gmp_printf(" %Qd",v[i]);
}

int main(void)
{
    edge_checks();mpq_t exponent,x;mpq_inits(exponent,x,NULL);
    WeightedRemainderDirichlet s;weighted_remainder_dirichlet_init(&s);
    WeightedRemainderDeficitDiagnostic d;weighted_remainder_deficit_diagnostic_init(&d);
    char op,value[1024];unsigned N;
    while (scanf(" %c %u",&op,&N)==2) {
        int ok;
        if (op=='S') {
            if (scanf(" %1023s",value)!=1) return 2;
            int parsed=mpq_set_str(exponent,value,10)==0;
            if (parsed && mpz_sgn(mpq_denref(exponent))>0) mpq_canonicalize(exponent);
            ok=parsed && weighted_remainder_dirichlet_compute(&s,exponent,N);
            printf("S %d",ok);if (ok) print_series(&s);
        } else if (op=='D') {
            ok=weighted_remainder_deficit_diagnostic_compute(&d,N);printf("D %d",ok);
            if (ok) {
                print_series(&d.two);print_series(&d.three_halves);
                mpq_ptr v[8];diagnostic_fields(&d,v);for (unsigned i=0;i<8;++i) gmp_printf(" %Qd",v[i]);
            }
        } else if (op=='C') {
            ok=weighted_remainder_divisor_deficit_q(x,N);printf("C %d",ok);if (ok) gmp_printf(" %Qd",x);
        } else return 2;
        putchar('\n');
    }
    weighted_remainder_deficit_diagnostic_clear(&d);weighted_remainder_dirichlet_clear(&s);
    mpq_clears(exponent,x,NULL);return 0;
}
