#include "../src/weighted_remainder_increment.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static unsigned edges,profiles;
#define CHECK(x) do { assert(x); ++edges; } while (0)
static const char *shifts[]={"0","1","-1","2","6","37","1000000000",
    "123456789012345678901234567890123456789012345678901234567890",
    "-123456789012345678901234567890123456789012345678901234567890"};
static void rational(mpq_t q,long n,unsigned d)
{ mpq_set_si(q,n,d);mpq_canonicalize(q); }

/* Reference visits all multiples of k in the actual complete residue
 * cycle, counting joint reset events. The period is found by repeated
 * addition. No gcd or Ramanujan formula is used. */
static void references(void)
{
    mpz_t shift;mpz_init(shift);
    for (unsigned s=0;s<9;++s) {
        assert(!mpz_set_str(shift,shifts[s],10));
        printf("shift %u %s\n",s,shifts[s]);
        for (unsigned k=2;k<=240;++k) for (unsigned l=2;l<=k;++l) {
            unsigned L=k;while (L%l) L+=k;
            unsigned h=(unsigned)mpz_fdiv_ui(shift,l),hits=0;
            for (unsigned a=0;a<L;a+=k) if ((a+h)%l==0) ++hits;
            printf("reference %u %u %u %u %u\n",s,k,l,L,hits);
        }
    }
    mpz_clear(shift);
}

static void profile(mpq_t *v,unsigned M,unsigned kind)
{
    unsigned id=profiles++;
    printf("profile %u %u %u\n",id,M,kind);
    for (unsigned k=2;k<=M;++k) if (mpq_sgn(v[k])) gmp_printf("weight %u %u %Qd\n",id,k,v[k]);
    mpq_t a,r,z,o,copy;mpq_inits(a,r,z,o,copy,NULL);
    mpz_t h;mpz_init(h);
    for (unsigned s=0;s<9;++s) {
        assert(!mpz_set_str(h,shifts[s],10));
        assert(weighted_remainder_increment_covariance_q(a,r,z,o,v,M,h));
        gmp_printf("finite %u %u %Qd %Qd %Qd %Qd\n",id,s,a,r,z,o);
    }
    mpq_set(copy,v[2]);mpz_set_si(h,-13);
    CHECK(weighted_remainder_increment_covariance_q(v[2],r,z,o,v,M,h));
    gmp_printf("weight_alias %u %Qd\n",id,v[2]);mpq_set(v[2],copy);
    rational(a,-13,1);
    CHECK(weighted_remainder_increment_covariance_q(a,r,z,o,v,M,mpq_numref(a)));
    gmp_printf("shift_alias %u %Qd\n",id,a);
    mpq_clears(a,r,z,o,copy,NULL);mpz_clear(h);
}

static void print_state(unsigned M,const mpz_t h,WeightedRemainderIncrement *s)
{
    assert(weighted_remainder_increment_compute(s,M,h));
    gmp_printf("state %u %u %Zd %Zd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd\n",
        M,s->binary_exponent,s->shift,s->cutoff_period,s->mass,s->arithmetic,s->ramanujan,s->zero,s->one,
        s->potential_squared_error,s->increment_squared_error,s->cross_upper,s->covariance_error,
        s->full_lower,s->full_upper,s->potential_recurrence_squared_upper,s->covariance_recurrence_loss_upper);
}

int main(void)
{
    mpq_t v[241],a,r,z,o;
    for (unsigned k=0;k<=240;++k) mpq_init(v[k]);
    mpq_inits(a,r,z,o,NULL);rational(a,13,17);rational(r,19,23);rational(z,29,31);rational(o,37,41);
    mpz_t h,L;mpz_inits(h,L,NULL);
    unsigned bad[]={0,1,241,UINT_MAX};
    for (unsigned i=0;i<4;++i) CHECK(!weighted_remainder_increment_covariance_q(a,r,z,o,v,bad[i],h));
    CHECK(!weighted_remainder_increment_covariance_q(a,r,z,o,NULL,2,h));
    for (unsigned i=0;i<4;++i) for (unsigned j=0;j<i;++j) {
        mpq_ptr outs[]={a,r,z,o};outs[i]=outs[j];
        CHECK(!weighted_remainder_increment_covariance_q(outs[0],outs[1],outs[2],outs[3],v,2,h));
    }
    for (unsigned k=0;k<2;++k) {
        rational(v[k],1,1);CHECK(!weighted_remainder_increment_covariance_q(a,r,z,o,v,2,h));rational(v[k],0,1);
    }
    for (int d=-1;d<=2;++d) if (d!=1) {
        mpz_set_ui(mpq_numref(v[2]),d==2 ? 2 : 1);mpz_set_si(mpq_denref(v[2]),d);
        CHECK(!weighted_remainder_increment_covariance_q(a,r,z,o,v,2,h));
    }
    CHECK(mpq_cmp_ui(a,13,17)==0 && mpq_cmp_ui(r,19,23)==0 && mpq_cmp_ui(z,29,31)==0 && mpq_cmp_ui(o,37,41)==0);
    rational(v[2],0,1);
    unsigned cutoffs[]={2,3,4,6,8,12,24,31,60,120,239,240};
    for (unsigned i=0;i<sizeof cutoffs/sizeof *cutoffs;++i) {
        unsigned M=cutoffs[i];
        for (unsigned k=2;k<=M;++k) weighted_remainder_weight_q(v[k],k);
        profile(v,M,0);
        for (unsigned k=2;k<=M;++k) rational(v[k],(long)(k%7)-3,k+3);
        profile(v,M,1);
        for (unsigned k=2;k<=M;++k) rational(v[k],0,1);
        rational(v[M],M==2 ? 1 : 1,M==2 ? 1 : 2);
        if (M>2) rational(v[M-1],1,2);
        profile(v,M,2);
    }
    for (unsigned k=2;k<=240;++k) rational(v[k],0,1);
    profile(v,240,3);
    WeightedRemainderIncrement state;
    weighted_remainder_increment_init(&state);
    mpq_ptr fields[]={state.mass,state.arithmetic,state.ramanujan,state.zero,state.one,
        state.potential_squared_error,state.increment_squared_error,state.cross_upper,state.covariance_error,
        state.full_lower,state.full_upper,state.potential_recurrence_squared_upper,state.covariance_recurrence_loss_upper};
    for (unsigned i=0;i<13;++i) rational(fields[i],13,17);
    mpz_set_ui(state.shift,19);mpz_set_ui(state.cutoff_period,23);state.cutoff=7;state.binary_exponent=11;
    CHECK(!weighted_remainder_increment_compute(NULL,2,h));
    for (unsigned i=0;i<4;++i) {
        CHECK(!weighted_remainder_increment_compute(&state,bad[i],h));
        CHECK(state.cutoff==7 && state.binary_exponent==11 && mpz_cmp_ui(state.shift,19)==0 && mpz_cmp_ui(state.cutoff_period,23)==0);
        for (unsigned j=0;j<13;++j) CHECK(mpq_cmp_ui(fields[j],13,17)==0);
    }
    for (unsigned i=0;i<13;++i) {
        rational(fields[i],-13,1);CHECK(weighted_remainder_increment_compute(&state,12,mpq_numref(fields[i])));
        CHECK(mpz_cmp_si(state.shift,-13)==0);gmp_printf("state_alias 12 -13 %Qd\n",state.arithmetic);
        rational(fields[i],2,13);CHECK(weighted_remainder_increment_compute(&state,12,mpq_denref(fields[i])));
        CHECK(mpz_cmp_ui(state.shift,13)==0);gmp_printf("state_alias 12 13 %Qd\n",state.arithmetic);
    }
    mpz_set_si(state.shift,-13);CHECK(weighted_remainder_increment_compute(&state,12,state.shift));
    CHECK(mpz_cmp_si(state.shift,-13)==0);gmp_printf("state_alias 12 -13 %Qd\n",state.arithmetic);
    mpz_set_si(state.cutoff_period,-13);CHECK(weighted_remainder_increment_compute(&state,12,state.cutoff_period));
    CHECK(mpz_cmp_si(state.shift,-13)==0);gmp_printf("state_alias 12 -13 %Qd\n",state.arithmetic);
    mpz_set_ui(L,1);
    for (unsigned M=2;M<=240;++M) {
        mpz_lcm_ui(L,L,M);print_state(M,L,&state);
        if (M<=12 || M==31 || M==60 || M==120 || M>=239)
            for (unsigned s=0;s<9;++s) { assert(!mpz_set_str(h,shifts[s],10));print_state(M,h,&state); }
    }
    weighted_remainder_increment_clear(&state);
    for (unsigned k=0;k<=240;++k) mpq_clear(v[k]);
    mpq_clears(a,r,z,o,NULL);mpz_clears(h,L,NULL);
    references();printf("edges %u profiles %u\n",edges,profiles);
    return 0;
}
