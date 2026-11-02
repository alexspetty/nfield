#include "weighted_remainder_increment.h"
#include "weighted_remainder_rows.h"
#include "weighted_remainder_weights.h"
#include <stdio.h>
#include <string.h>

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };

static unsigned gcd(unsigned a,unsigned b)
{
    while (b) { unsigned r=a%b;a=b;b=r; }
    return a;
}

static void add_scaled(mpq_t sum,const mpq_t product,long coefficient,
                       mpq_t factor,mpq_t term)
{
    mpq_set_si(factor,coefficient,9);mpq_canonicalize(factor);
    mpq_mul(term,product,factor);mpq_add(sum,sum,term);
}

int weighted_remainder_increment_covariance_q(mpq_t arithmetic,mpq_t ramanujan,
                                               mpq_t zero,mpq_t one,
                                               const mpq_t *v,unsigned M,
                                               const mpz_t shift)
{
    mpq_ptr outputs[]={arithmetic,ramanujan,zero,one};
    for (unsigned i=0;i<4;++i) for (unsigned j=0;j<i;++j)
        if (outputs[i]==outputs[j]) return 0;
    mpq_t a,r,z,o,xi,product,factor,term;
    mpq_inits(a,r,z,o,xi,product,factor,term,NULL);
    /* The shared finite-amplitude API validates the whole canonical array,
     * its inactive indices and cutoff before any direct array reads. */
    int ok=weighted_remainder_weights_amplitude_q(xi,v,M,2);
    if (ok) {
        for (unsigned k=2;k<=M;++k) for (unsigned l=2;l<=k;++l) {
            if (!mpq_sgn(v[k]) || !mpq_sgn(v[l])) continue;
            unsigned g=gcd(k,l),copies=k==l ? 1 : 2;
            long coefficient=mpz_divisible_ui_p(shift,g) ? (long)g-1 : -1;
            mpq_mul(product,v[k],v[l]);
            add_scaled(a,product,4L*copies*coefficient,factor,term);
            add_scaled(z,product,4L*copies*((long)g-1),factor,term);
            add_scaled(o,product,g==1 ? 0 : -4L*copies,factor,term);
        }
        WeightedRemainderRows row;
        weighted_remainder_rows_init(&row);
        for (unsigned q=2;q<=M;++q) {
            mpq_set_ui(xi,0,1);
            for (unsigned k=q;k<=M;k+=q) mpq_add(xi,xi,v[k]);
            if (!mpq_sgn(xi)) continue;
            weighted_remainder_rows_compute(&row,q,shift);
            mpq_mul(product,xi,xi);mpq_mul(product,product,row.ramanujan);
            add_scaled(r,product,4,factor,term);
        }
        weighted_remainder_rows_clear(&row);
        mpq_set(arithmetic,a);mpq_set(ramanujan,r);mpq_set(zero,z);mpq_set(one,o);
    }
    mpq_clears(a,r,z,o,xi,product,factor,term,NULL);
    return ok;
}

void weighted_remainder_increment_init(WeightedRemainderIncrement *s)
{
    s->cutoff=s->binary_exponent=0;
    mpz_inits(s->shift,s->cutoff_period,NULL);
    mpq_inits(s->mass,s->arithmetic,s->ramanujan,s->zero,s->one,
              s->potential_squared_error,s->increment_squared_error,s->cross_upper,
              s->covariance_error,s->full_lower,s->full_upper,
              s->potential_recurrence_squared_upper,s->covariance_recurrence_loss_upper,NULL);
}

void weighted_remainder_increment_clear(WeightedRemainderIncrement *s)
{
    mpz_clears(s->shift,s->cutoff_period,NULL);
    mpq_clears(s->mass,s->arithmetic,s->ramanujan,s->zero,s->one,
               s->potential_squared_error,s->increment_squared_error,s->cross_upper,
               s->covariance_error,s->full_lower,s->full_upper,
               s->potential_recurrence_squared_upper,s->covariance_recurrence_loss_upper,NULL);
}

static void sqrt_grid_upper(mpq_t out,const mpq_t value,unsigned grid)
{
    mpz_t scaled,integer,root,square;
    mpz_inits(scaled,integer,root,square,NULL);
    mpz_mul_ui(scaled,mpq_numref(value),grid);
    mpz_mul_ui(scaled,scaled,grid);
    mpz_fdiv_q(integer,scaled,mpq_denref(value));mpz_sqrt(root,integer);
    mpz_mul(square,root,root);mpz_mul(square,square,mpq_denref(value));
    if (mpz_cmp(square,scaled)<0) mpz_add_ui(root,root,1);
    mpz_set(mpq_numref(out),root);mpz_set_ui(mpq_denref(out),grid);
    mpq_canonicalize(out);
    mpz_clears(scaled,integer,root,square,NULL);
}

int weighted_remainder_increment_compute(WeightedRemainderIncrement *out,
                                          unsigned M,const mpz_t shift)
{
    if (!out || M<2 || M>MAX) return 0;
    WeightedRemainderIncrement s;
    weighted_remainder_increment_init(&s);
    mpz_set(s.shift,shift);mpz_set_ui(s.cutoff_period,1);
    mpq_t v[MAX+1],product;
    mpq_init(product);
    for (unsigned k=0;k<=M;++k) {
        mpq_init(v[k]);weighted_remainder_weight_q(v[k],k);
        mpq_add(s.mass,s.mass,v[k]);
        if (k>=1) mpz_lcm_ui(s.cutoff_period,s.cutoff_period,k);
    }
    int ok=weighted_remainder_increment_covariance_q(s.arithmetic,s.ramanujan,s.zero,s.one,v,M,s.shift);
    if (ok) {
        unsigned b=0,power=1;
        while (power<2*M) { power*=2;++b; }
        mpq_set_ui(s.potential_squared_error,256*(b+1)*(b+1),M);
        mpq_canonicalize(s.potential_squared_error);
        mpq_mul_2exp(s.increment_squared_error,s.potential_squared_error,2);
        mpq_mul(product,s.zero,s.increment_squared_error);
        sqrt_grid_upper(s.cross_upper,product,M*M);
        mpq_mul_2exp(s.covariance_error,s.cross_upper,1);
        mpq_add(s.covariance_error,s.covariance_error,s.increment_squared_error);
        mpq_sub(s.full_lower,s.arithmetic,s.covariance_error);
        mpq_add(s.full_upper,s.arithmetic,s.covariance_error);
        mpq_mul_2exp(s.potential_recurrence_squared_upper,s.potential_squared_error,2);
        mpq_mul_2exp(s.covariance_recurrence_loss_upper,s.potential_squared_error,3);
        out->cutoff=M;out->binary_exponent=b;
        mpz_set(out->shift,s.shift);mpz_set(out->cutoff_period,s.cutoff_period);
        mpq_set(out->mass,s.mass);mpq_set(out->arithmetic,s.arithmetic);
        mpq_set(out->ramanujan,s.ramanujan);mpq_set(out->zero,s.zero);mpq_set(out->one,s.one);
        mpq_set(out->potential_squared_error,s.potential_squared_error);
        mpq_set(out->increment_squared_error,s.increment_squared_error);
        mpq_set(out->cross_upper,s.cross_upper);mpq_set(out->covariance_error,s.covariance_error);
        mpq_set(out->full_lower,s.full_lower);mpq_set(out->full_upper,s.full_upper);
        mpq_set(out->potential_recurrence_squared_upper,s.potential_recurrence_squared_upper);
        mpq_set(out->covariance_recurrence_loss_upper,s.covariance_recurrence_loss_upper);
    }
    for (unsigned k=0;k<=M;++k) mpq_clear(v[k]);
    mpq_clear(product);weighted_remainder_increment_clear(&s);
    return ok;
}

static int parse_cutoff(const char *p,unsigned *M)
{
    if (!p || !*p) return 0;
    unsigned n=0;
    for (;*p;++p) {
        if (*p<'0' || *p>'9') return 0;
        n=10*n+(unsigned)(*p-'0');if (n>MAX) return 0;
    }
    if (n<2) return 0;
    *M=n;return 1;
}

static int parse_shift(mpz_t z,const char *p)
{
    if (!p || !*p) return 0;
    const char *digits=p;
    if (*digits=='-') ++digits;
    if (!*digits) return 0;
    for (const char *s=digits;*s;++s) if (*s<'0' || *s>'9') return 0;
    return mpz_set_str(z,p,10)==0;
}

int weighted_remainder_increment_command(int argc,char **argv)
{
    if (argc<3) return 1;
    int recurrence=!strcmp(argv[2],"increment-recurrence");
    unsigned M;
    if ((!recurrence && strcmp(argv[2],"increment-covariance")) ||
        argc!=(recurrence ? 4 : 5) || !parse_cutoff(argv[3],&M)) goto bad;
    mpz_t shift;
    mpz_init_set_ui(shift,recurrence ? 1 : 0);
    int ok=1;
    if (recurrence) for (unsigned k=1;k<=M;++k) mpz_lcm_ui(shift,shift,k);
    else ok=parse_shift(shift,argv[4]);
    WeightedRemainderIncrement s;
    weighted_remainder_increment_init(&s);
    if (ok) ok=weighted_remainder_increment_compute(&s,M,shift);
    if (ok) {
        printf("Increment covariance and recurrence\ncutoff=%u\nbinary_exponent=%u\n",M,s.binary_exponent);
        gmp_printf("shift=%Zd\ncutoff_period=%Zd\nretained_mass=%Qd\n"
                   "finite_arithmetic=%Qd\nfinite_ramanujan=%Qd\nfinite_zero=%Qd\nfinite_one=%Qd\n"
                   "potential_squared_error=%Qd\nincrement_squared_error=%Qd\ncross_upper=%Qd\n"
                   "covariance_error=%Qd\nfull_lower=%Qd\nfull_upper=%Qd\n"
                   "potential_recurrence_squared_upper=%Qd\ncovariance_recurrence_loss_upper=%Qd\n",
            s.shift,s.cutoff_period,s.mass,s.arithmetic,s.ramanujan,s.zero,s.one,
            s.potential_squared_error,s.increment_squared_error,s.cross_upper,s.covariance_error,
            s.full_lower,s.full_upper,s.potential_recurrence_squared_upper,s.covariance_recurrence_loss_upper);
        printf("finite_zero_positive=%d\nfinite_one_negative=%d\n",mpq_sgn(s.zero)>0,mpq_sgn(s.one)<0);
        if (recurrence) printf("finite_return_equals_zero=%d\n",mpq_equal(s.arithmetic,s.zero));
    }
    weighted_remainder_increment_clear(&s);mpz_clear(shift);
    if (ok) return 0;
bad:
    fputs("increment-covariance requires cutoff 2..240 and a signed integer shift; "
          "increment-recurrence requires cutoff 2..240.\n",stderr);
    return 1;
}
