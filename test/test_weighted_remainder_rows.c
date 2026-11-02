#include "../src/weighted_remainder_rows.h"
#include "../src/weighted_remainder_weights.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static unsigned edges, profiles;
#define CHECK(x) do { assert(x); ++edges; } while (0)

static void rational(mpq_t q, long n, unsigned d)
{
    mpq_set_si(q, n, d); mpq_canonicalize(q);
}

static int equal_rows(const WeightedRemainderRows *a, const WeightedRemainderRows *b)
{
    return a->conductor == b->conductor && a->residue == b->residue &&
        a->radical == b->radical && a->scale == b->scale &&
        a->totient == b->totient && a->jordan_two == b->jordan_two &&
        mpq_equal(a->primitive,b->primitive) && mpq_equal(a->odd,b->odd) &&
        mpq_equal(a->ramanujan,b->ramanujan) &&
        mpq_equal(a->primitive_norm_squared,b->primitive_norm_squared) &&
        mpq_equal(a->odd_norm_squared,b->odd_norm_squared) &&
        mpq_equal(a->ramanujan_norm_squared,b->ramanujan_norm_squared) &&
        mpq_equal(a->radical_descent,b->radical_descent);
}

static void print_row(unsigned q, const mpz_t n, WeightedRemainderRows *s)
{
    assert(weighted_remainder_rows_compute(s,q,n));
    gmp_printf("row %u %Zd %u %u %u %u %u %Qd %Qd %Qd %Qd %Qd %Qd %Qd\n",
        q,n,s->residue,s->radical,s->scale,s->totient,s->jordan_two,
        s->primitive,s->odd,s->ramanujan,s->primitive_norm_squared,
        s->odd_norm_squared,s->ramanujan_norm_squared,s->radical_descent);
}

/* Independent recurrence: subtract the proper divisor rows from each raw
 * remainder/sawtooth/divisibility row. No Mobius, totient or Jordan formula.
 * Complete periods are found by repeated addition, without a gcd formula. */
static void references(void)
{
    long p[241][240] = {{0}}, r[241][240] = {{0}}, c[241][240] = {{0}};
    c[1][0] = 1;
    for (unsigned q=2;q<=240;++q) for (unsigned a=0;a<q;++a) {
        p[q][a] = 2L*a-(long)q+1;
        r[q][a] = a ? 2L*a-(long)q : 0;
        c[q][a] = a ? 0 : (long)q;
        for (unsigned d=1;d<q;++d) if (q%d==0) {
            p[q][a] -= p[d][a%d];
            r[q][a] -= r[d][a%d];
            c[q][a] -= c[d][a%d];
        }
    }
    for (unsigned q=2;q<=240;++q) for (unsigned d=2;d<=q;++d) {
        unsigned L=q;
        while (L%d) L+=q;
        long long pp=0,rr=0,cc=0,pr=0,pc=0,rc=0;
        for (unsigned a=0;a<L;++a) {
            unsigned x=a%q,y=a%d;
            pp+=p[q][x]*p[d][y]; rr+=r[q][x]*r[d][y]; cc+=c[q][x]*c[d][y];
            pr+=p[q][x]*r[d][y]; pc+=p[q][x]*c[d][y]; rc+=r[q][x]*c[d][y];
        }
        printf("reference %u %u %u %lld %lld %lld %lld %lld %lld\n",q,d,L,pp,rr,cc,pr,pc,rc);
    }
}

static void inverse_profile(mpq_t *v, mpq_t *xi, unsigned M, int raw)
{
    unsigned id=profiles++;
    printf("profile %u %u %d\n",id,M,raw);
    mpq_t out;
    mpq_init(out);
    for (unsigned q=2;q<=M;++q) {
        if (!raw) assert(weighted_remainder_weights_amplitude_q(xi[q],v,M,q));
        gmp_printf("input %u %u %Qd\n",id,q,raw ? xi[q] : v[q]);
        gmp_printf("amplitude %u %u %Qd\n",id,q,xi[q]);
    }
    for (unsigned k=2;k<=240;++k) {
        assert(weighted_remainder_mass_inverse_q(out,xi,M,k));
        gmp_printf("inverse %u %u %Qd\n",id,k,out);
    }
    mpq_set(out,xi[2]);
    CHECK(weighted_remainder_mass_inverse_q(xi[2],xi,M,2));
    gmp_printf("inverse_alias %u %Qd\n",id,xi[2]);
    mpq_set(xi[2],out);
    mpq_clear(out);
}

static void recoveries(void)
{
    WeightedRemainderRecovery s;
    weighted_remainder_recovery_init(&s);
    s.period=7; rational(s.beta_lower,13,17); rational(s.beta_upper,19,23);
    rational(s.inverse_tail_error,29,31); rational(s.mass_lower,37,41); rational(s.mass_upper,43,47);
    unsigned bad[]={0,1,241,UINT_MAX};
    CHECK(!weighted_remainder_mass_recovery_compute(NULL,2,2,2));
    for (unsigned i=0;i<4;++i) {
        CHECK(!weighted_remainder_mass_recovery_compute(&s,bad[i],240,2));
        CHECK(!weighted_remainder_mass_recovery_compute(&s,2,bad[i],2));
        CHECK(!weighted_remainder_mass_recovery_compute(&s,2,2,bad[i]));
    }
    CHECK(!weighted_remainder_mass_recovery_compute(&s,3,2,240));
    CHECK(s.period==7 && s.conductor_cutoff==0 && s.period_cutoff==0 && s.quotient==0 &&
          s.period_binary==0 && s.quotient_binary==0 && mpq_cmp_ui(s.beta_lower,13,17)==0 &&
          mpq_cmp_ui(s.beta_upper,19,23)==0 && mpq_cmp_ui(s.inverse_tail_error,29,31)==0 &&
          mpq_cmp_ui(s.mass_lower,37,41)==0 && mpq_cmp_ui(s.mass_upper,43,47)==0);
    for (unsigned Q=2;Q<=240;++Q) for (unsigned d=2;d<=Q;++d) {
        if (Q>24 && d!=2 && d!=3 && d!=Q/2 && d!=Q-1 && d!=Q) continue;
        unsigned cutoffs[]={2,Q,240};
        for (unsigned i=0;i<3;++i) {
            if (i && cutoffs[i]==cutoffs[i-1]) continue;
            assert(weighted_remainder_mass_recovery_compute(&s,d,Q,cutoffs[i]));
            gmp_printf("recovery %u %u %u %u %u %u %Qd %Qd %Qd %Qd %Qd\n",d,Q,cutoffs[i],
                s.quotient,s.period_binary,s.quotient_binary,s.beta_lower,s.beta_upper,
                s.inverse_tail_error,s.mass_lower,s.mass_upper);
        }
    }
    weighted_remainder_recovery_clear(&s);
}

int main(void)
{
    WeightedRemainderRows s,t;
    weighted_remainder_rows_init(&s); weighted_remainder_rows_init(&t);
    mpz_t n;
    mpz_init_set_si(n,-13);
    CHECK(weighted_remainder_rows_compute(&s,12,n));
    CHECK(weighted_remainder_rows_compute(&t,12,n));
    const unsigned bad[]={0,1,241,UINT_MAX};
    CHECK(!weighted_remainder_rows_compute(NULL,2,n));
    for (unsigned i=0;i<4;++i) {
        CHECK(!weighted_remainder_rows_compute(&s,bad[i],n));
        CHECK(equal_rows(&s,&t));
    }
    mpq_ptr fields[]={s.primitive,s.odd,s.ramanujan,s.primitive_norm_squared,
                     s.odd_norm_squared,s.ramanujan_norm_squared,s.radical_descent};
    for (unsigned i=0;i<7;++i) {
        rational(fields[i],-13,1);
        CHECK(weighted_remainder_rows_compute(&s,12,mpq_numref(fields[i])));
        CHECK(equal_rows(&s,&t));
        rational(fields[i],2,13);
        mpz_set_ui(n,13); CHECK(weighted_remainder_rows_compute(&t,12,n));
        CHECK(weighted_remainder_rows_compute(&s,12,mpq_denref(fields[i])));
        CHECK(equal_rows(&s,&t));
        mpz_set_si(n,-13); CHECK(weighted_remainder_rows_compute(&t,12,n));
    }
    const char *large[]={"-1","-13","-1000000000","1000000000",
        "123456789012345678901234567890123456789012345678901234567890",
        "-123456789012345678901234567890123456789012345678901234567890"};
    for (unsigned q=2;q<=240;++q) {
        for (unsigned a=0;a<q;++a) { mpz_set_ui(n,a); print_row(q,n,&s); }
        for (unsigned j=0;j<6;++j) { assert(!mpz_set_str(n,large[j],10)); print_row(q,n,&s); }
    }
    weighted_remainder_rows_clear(&s); weighted_remainder_rows_clear(&t); mpz_clear(n);
    mpq_t v[241],xi[241],out;
    mpq_init(out); rational(out,13,17);
    for (unsigned k=0;k<=240;++k) { mpq_init(v[k]); mpq_init(xi[k]); }
    CHECK(!weighted_remainder_mass_inverse_q(out,NULL,2,2));
    for (unsigned i=0;i<4;++i) {
        CHECK(!weighted_remainder_mass_inverse_q(out,xi,bad[i],2));
        CHECK(!weighted_remainder_mass_inverse_q(out,xi,2,bad[i]));
        CHECK(mpq_cmp_ui(out,13,17)==0);
    }
    for (unsigned k=0;k<=1;++k) {
        rational(xi[k],1,1);
        CHECK(!weighted_remainder_mass_inverse_q(out,xi,2,2));
        CHECK(mpq_cmp_ui(out,13,17)==0);
        rational(xi[k],0,1);
    }
    for (int d=-1;d<=2;++d) if (d!=1) {
        mpz_set_ui(mpq_numref(xi[2]),d==2 ? 2 : 1); mpz_set_si(mpq_denref(xi[2]),d);
        CHECK(!weighted_remainder_mass_inverse_q(out,xi,2,2));
        CHECK(mpq_cmp_ui(out,13,17)==0);
    }
    rational(xi[2],0,1);
    unsigned cutoffs[]={2,3,4,6,12,24,31,32,60,64,120,239,240};
    for (unsigned i=0;i<sizeof cutoffs/sizeof *cutoffs;++i) {
        unsigned M=cutoffs[i];
        for (unsigned k=2;k<=M;++k) weighted_remainder_weight_q(v[k],k);
        inverse_profile(v,xi,M,0);
        for (unsigned k=2;k<=M;++k) rational(v[k],(long)(k%7)-3,k+1);
        inverse_profile(v,xi,M,0);
        for (unsigned k=2;k<=M;++k) rational(xi[k],(long)(k%5)-2,k*k+1);
        inverse_profile(v,xi,M,1);
    }
    for (unsigned k=2;k<=240;++k) rational(v[k],0,1);
    inverse_profile(v,xi,240,0);
    rational(v[2],1,2);rational(v[3],1,2);inverse_profile(v,xi,240,0);
    rational(out,1,48);CHECK(weighted_remainder_perturbed_weights_q(v,240,out));
    inverse_profile(v,xi,240,0);
    for (unsigned k=0;k<=240;++k) { mpq_clear(v[k]);mpq_clear(xi[k]); }
    mpq_clear(out);
    recoveries(); references();
    printf("edges %u profiles %u\n",edges,profiles);
    return 0;
}
