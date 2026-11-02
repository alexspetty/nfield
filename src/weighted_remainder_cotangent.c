#include "weighted_remainder_cotangent.h"
#include "weighted_remainder_rect_internal.h"
#include "weighted_remainder_constants.h"

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };
#define FIELDS(X) X(residue_bound) X(unit_residue_bound) X(prefix_lower) X(prefix_upper) \
    X(unit_prefix_lower) X(unit_prefix_upper) X(tail_upper) X(unit_tail_upper) X(lower) X(upper) \
    X(unit_lower) X(unit_upper) X(gcd_prefix_lower) X(gcd_prefix_upper) X(mobius_prefix_lower) \
    X(mobius_prefix_upper) X(gcd_lower) X(gcd_upper) X(mobius_lower) X(mobius_upper) \
    X(zeta_lower) X(zeta_upper) X(delta) X(harmonic_seed_lower) X(harmonic_seed_upper) X(eta_lower) X(eta_upper)

static unsigned gcd_u(unsigned a,unsigned b) { while (b) { unsigned r=a%b;a=b;b=r; }return a; }
static int moebius(unsigned n)
{
    int sign=1;
    for (unsigned p=2;p<=n/p;++p) if (n%p==0) {
        n/=p;sign=-sign;if (n%p==0) return 0;
    }
    return n>1?-sign:sign;
}

void weighted_remainder_cotangent_init(WeightedRemainderCotangent *s)
{
    s->modulus=s->cutoff=s->zeta_cutoff=0;
#define INIT(f) mpq_init(s->f);
    FIELDS(INIT)
#undef INIT
}
void weighted_remainder_cotangent_clear(WeightedRemainderCotangent *s)
{
#define CLEAR(f) mpq_clear(s->f);
    FIELDS(CLEAR)
#undef CLEAR
}

/* All caller-owned outputs are initialized temporary structs. N=0 is
 * admitted here only for prefixes; full fields are zero in that case. */
static int base(WeightedRemainderCotangent *s,unsigned q,unsigned N)
{
    mpq_t lo[MAX],hi[MAX],c,t;mpq_inits(c,t,NULL);
    for (unsigned a=0;a<q;++a) mpq_inits(lo[a],hi[a],NULL);
    WeightedRemainderTrig trig;weighted_remainder_trig_init(&trig);
    mpz_t a;mpz_init(a);int ok=1;
    for (unsigned r=1;r<q && ok;++r) {
        mpz_set_ui(a,r);ok=weighted_remainder_trig_compute(&trig,q,a);
        if (!ok) break;
        mpq_set(lo[r],trig.cot_lower);mpq_set(hi[r],trig.cot_upper);
        mpq_abs(c,lo[r]);mpq_abs(t,hi[r]);if (mpq_cmp(t,c)>0) mpq_set(c,t);
        if (mpq_cmp(c,s->residue_bound)>0) mpq_set(s->residue_bound,c);
        if (gcd_u(r,q)==1 && mpq_cmp(c,s->unit_residue_bound)>0) mpq_set(s->unit_residue_bound,c);
    }
    if (ok) for (unsigned n=1;n<=N;++n) {
        unsigned r=n%q;if (!r) continue;
        mpq_set_ui(c,1,n*n);
        mpq_mul(t,lo[r],c);mpq_add(s->prefix_lower,s->prefix_lower,t);
        if (gcd_u(n,q)==1) mpq_add(s->unit_prefix_lower,s->unit_prefix_lower,t);
        mpq_mul(t,hi[r],c);mpq_add(s->prefix_upper,s->prefix_upper,t);
        if (gcd_u(n,q)==1) mpq_add(s->unit_prefix_upper,s->unit_prefix_upper,t);
    }
    if (ok && N) {
        mpq_set_ui(c,1,N);mpq_mul(s->tail_upper,s->residue_bound,c);
        mpq_mul(s->unit_tail_upper,s->unit_residue_bound,c);
        mpq_sub(s->lower,s->prefix_lower,s->tail_upper);mpq_add(s->upper,s->prefix_upper,s->tail_upper);
        mpq_sub(s->unit_lower,s->unit_prefix_lower,s->unit_tail_upper);
        mpq_add(s->unit_upper,s->unit_prefix_upper,s->unit_tail_upper);
    }
    for (unsigned r=0;r<q;++r) mpq_clears(lo[r],hi[r],NULL);
    mpz_clear(a);weighted_remainder_trig_clear(&trig);mpq_clears(c,t,NULL);return ok;
}

int weighted_remainder_cotangent_prefix_q(mpq_t lo,mpq_t hi,mpq_t ul,mpq_t uu,unsigned q,unsigned N)
{
    if (!lo || !hi || !ul || !uu || q<1 || q>MAX || N>MAX) return 0;
    mpq_ptr outs[]={lo,hi,ul,uu};
    for (unsigned i=0;i<4;++i) for (unsigned j=i+1;j<4;++j) if (outs[i]==outs[j]) return 0;
    WeightedRemainderCotangent s;weighted_remainder_cotangent_init(&s);int ok=base(&s,q,N);
    if (ok) {
        mpq_set(lo,s.prefix_lower);mpq_set(hi,s.prefix_upper);
        mpq_set(ul,s.unit_prefix_lower);mpq_set(uu,s.unit_prefix_upper);
    }
    weighted_remainder_cotangent_clear(&s);return ok;
}

static void add_scaled(mpq_t lo,mpq_t hi,const mpq_t a,const mpq_t b,const mpq_t coefficient)
{
    mpq_t l,u;mpq_inits(l,u,NULL);wr_product(l,u,a,b,coefficient,coefficient);
    mpq_add(lo,lo,l);mpq_add(hi,hi,u);mpq_clears(l,u,NULL);
}

int weighted_remainder_cotangent_compute(WeightedRemainderCotangent *out,unsigned q,unsigned N,unsigned K)
{
    if (!out || q<1 || q>MAX || N<1 || N>MAX || K<1 || K>MAX) return 0;
    WeightedRemainderCotangent s;weighted_remainder_cotangent_init(&s);
    s.modulus=q;s.cutoff=N;s.zeta_cutoff=K;int ok=base(&s,q,N);
    mpq_t c,l,u,dl,du,t,j;mpq_inits(c,l,u,dl,du,t,j,NULL);
    for (unsigned d=1;d<=q && ok;++d) if (q%d==0) {
        WeightedRemainderCotangent a,b,p,r;
        weighted_remainder_cotangent_init(&a);weighted_remainder_cotangent_init(&b);
        weighted_remainder_cotangent_init(&p);weighted_remainder_cotangent_init(&r);
        ok=base(&a,d,N) && base(&b,q/d,N) && base(&p,d,N*d/q) && base(&r,q/d,N/d);
        if (ok) {
            mpq_set_ui(c,d*d,q*q);mpq_canonicalize(c);
            add_scaled(s.gcd_prefix_lower,s.gcd_prefix_upper,p.unit_prefix_lower,p.unit_prefix_upper,c);
            add_scaled(s.gcd_lower,s.gcd_upper,a.unit_lower,a.unit_upper,c);
            mpq_set_si(c,moebius(d),d*d);mpq_canonicalize(c);
            add_scaled(s.mobius_prefix_lower,s.mobius_prefix_upper,r.prefix_lower,r.prefix_upper,c);
            add_scaled(s.mobius_lower,s.mobius_upper,b.lower,b.upper,c);
        }
        weighted_remainder_cotangent_clear(&a);weighted_remainder_cotangent_clear(&b);
        weighted_remainder_cotangent_clear(&p);weighted_remainder_cotangent_clear(&r);
    }
    WeightedRemainderConstants constants;weighted_remainder_constants_init(&constants);
    ok=ok && weighted_remainder_constants_compute(&constants,1);
    ok=ok && weighted_remainder_zeta_three_interval_q(s.zeta_lower,s.zeta_upper,K);
    ok=ok && weighted_remainder_amplitude_factors_q(s.delta,j,q);
    if (ok) {
        mpq_set_ui(c,q*q*q+1,2*q*q*q);mpq_canonicalize(c);
        mpq_mul(s.harmonic_seed_lower,s.zeta_lower,c);mpq_mul(s.harmonic_seed_upper,s.zeta_upper,c);
        mpq_set_ui(c,1,2*q);mpq_mul(l,constants.pi_lower,c);mpq_mul(u,constants.pi_upper,c);
        wr_product(dl,du,s.lower,s.upper,l,u);
        mpq_sub(s.harmonic_seed_lower,s.harmonic_seed_lower,du);
        mpq_sub(s.harmonic_seed_upper,s.harmonic_seed_upper,dl);
        if (q==1) { mpq_set_ui(s.eta_lower,1,1);mpq_set_ui(s.eta_upper,1,1); }
        else {
            mpq_mul(dl,s.zeta_lower,s.delta);mpq_mul(du,s.zeta_upper,s.delta);
            mpq_div(l,l,du);mpq_div(u,u,dl);
            wr_product(dl,du,s.unit_lower,s.unit_upper,l,u);
            mpq_set_ui(c,1,2);mpq_sub(s.eta_lower,c,du);mpq_sub(s.eta_upper,c,dl);
        }
        out->modulus=q;out->cutoff=N;out->zeta_cutoff=K;
#define COPY(f) mpq_set(out->f,s.f);
        FIELDS(COPY)
#undef COPY
    }
    weighted_remainder_constants_clear(&constants);mpq_clears(c,l,u,dl,du,t,j,NULL);
    weighted_remainder_cotangent_clear(&s);return ok;
}
