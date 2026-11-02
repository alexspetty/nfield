#include "weighted_remainder_character.h"
#include "weighted_remainder_rect_internal.h"
#include "weighted_remainder_constants.h"
#include "finite_character_core.h"
#include <stdlib.h>

enum { MAX=WEIGHTED_REMAINDER_EXACT_MAX };

#define CHARACTER_RECTS(X) X(cotangent_coefficient) X(l_one_conjugate) \
    X(l_two_prefix) X(l_two) X(mixed_product)
#define MIXED_FIELDS(X) X(delta) X(zeta_lower) X(zeta_upper) X(denominator_lower) \
    X(denominator_upper) X(eta_lower) X(eta_upper) X(positive_amplitude_lower) X(positive_amplitude_upper)

void weighted_remainder_character_init(WeightedRemainderCharacter *s)
{
    s->modulus=s->index=s->conductor=s->denominator=s->cutoff=0;
#define INIT(f) weighted_remainder_complex_init(&s->f);
    CHARACTER_RECTS(INIT)
#undef INIT
    mpq_init(s->l_two_tail);
}

void weighted_remainder_character_clear(WeightedRemainderCharacter *s)
{
#define CLEAR(f) weighted_remainder_complex_clear(&s->f);
    CHARACTER_RECTS(CLEAR)
#undef CLEAR
    mpq_clear(s->l_two_tail);
}

/* One reusable table of roots and cotangents for the whole character sum. */
typedef struct {
    FiniteCharacterTable table;
    WeightedRemainderComplex *phase;
    WeightedRemainderTrig *trig;
    mpq_t pi_lower,pi_upper;
} CharacterContext;

static void context_clear(CharacterContext *s)
{
    if (s->phase) for (int a=0;a<s->table.denominator;++a) weighted_remainder_complex_clear(&s->phase[a]);
    if (s->trig) for (int a=0;a<s->table.modulus;++a) weighted_remainder_trig_clear(&s->trig[a]);
    free(s->phase);free(s->trig);finite_character_table_free(&s->table);
    mpq_clears(s->pi_lower,s->pi_upper,NULL);
}

static int context_init(CharacterContext *s,unsigned q)
{
    *s=(CharacterContext){0};mpq_inits(s->pi_lower,s->pi_upper,NULL);
    if (!finite_character_table_build((int)q,&s->table)) return 0;
    if (s->table.denominator<1 || s->table.denominator>MAX) return 0;
    s->phase=calloc((size_t)s->table.denominator,sizeof(*s->phase));
    s->trig=calloc(q,sizeof(*s->trig));
    /* Initialize allocated entries before any later failure is possible. */
    if (s->phase) for (int a=0;a<s->table.denominator;++a) weighted_remainder_complex_init(&s->phase[a]);
    if (s->trig) for (unsigned a=0;a<q;++a) weighted_remainder_trig_init(&s->trig[a]);
    if (!s->phase || !s->trig) return 0;
    for (int a=0;a<s->table.denominator;++a)
        if (!wr_rect_phase(&s->phase[a],(unsigned)s->table.denominator,(unsigned)a)) return 0;
    mpz_t a;mpz_init(a);int ok=1;
    for (unsigned n=1;n<q && ok;++n) {
        mpz_set_ui(a,n);ok=weighted_remainder_trig_compute(&s->trig[n],q,a);
    }
    mpz_clear(a);
    WeightedRemainderConstants c;weighted_remainder_constants_init(&c);
    ok=ok && weighted_remainder_constants_compute(&c,1);
    if (ok) { mpq_set(s->pi_lower,c.pi_lower);mpq_set(s->pi_upper,c.pi_upper); }
    weighted_remainder_constants_clear(&c);return ok;
}

static void character_with_context(WeightedRemainderCharacter *s,
    const CharacterContext *ctx,unsigned index,unsigned N)
{
    const FiniteCharacterTable *table=&ctx->table;
    unsigned q=(unsigned)table->modulus;
    s->modulus=q;s->index=index;s->conductor=(unsigned)table->conductor[index];
    s->denominator=(unsigned)table->denominator;s->cutoff=N;
#define ZERO(f) wr_rect_zero(&s->f);
    CHARACTER_RECTS(ZERO)
#undef ZERO
    WeightedRemainderComplex t;weighted_remainder_complex_init(&t);
    mpq_t c,lo,hi;mpq_inits(c,lo,hi,NULL);
    for (unsigned a=1;a<q;++a) {
        int phase=table->phase[index*q+a];if (phase<0) continue;
        wr_rect_conjugate(&t,&ctx->phase[phase]);
        wr_rect_scale(&t,&t,ctx->trig[a].cot_lower,ctx->trig[a].cot_upper);
        wr_rect_add(&s->cotangent_coefficient,&s->cotangent_coefficient,&t);
    }
    mpq_set_ui(c,1,2*q);mpq_mul(lo,ctx->pi_lower,c);mpq_mul(hi,ctx->pi_upper,c);
    wr_rect_scale(&s->l_one_conjugate,&s->cotangent_coefficient,lo,hi);
    for (unsigned n=1;n<=N;++n) {
        int phase=table->phase[index*q+n%q];if (phase<0) continue;
        mpq_set_ui(c,1,n*n);wr_rect_scale(&t,&ctx->phase[phase],c,c);
        wr_rect_add(&s->l_two_prefix,&s->l_two_prefix,&t);
    }
    mpq_set_ui(s->l_two_tail,1,N);
    wr_rect_widen(&s->l_two,&s->l_two_prefix,s->l_two_tail);
    wr_rect_product(&s->mixed_product,&s->l_one_conjugate,&s->l_two);
    mpq_clears(c,lo,hi,NULL);weighted_remainder_complex_clear(&t);
}

int weighted_remainder_character_compute(WeightedRemainderCharacter *out,
    unsigned q,unsigned index,unsigned N)
{
    if (!out || q<2 || q>MAX || N<1 || N>MAX || index>=q) return 0;
    CharacterContext ctx;int ok=context_init(&ctx,q);
    if (ok) ok=index<(unsigned)ctx.table.count && ctx.table.odd[index];
    if (ok) character_with_context(out,&ctx,index,N);
    context_clear(&ctx);return ok;
}

void weighted_remainder_mixed_moment_init(WeightedRemainderMixedMoment *s)
{
    s->modulus=s->cutoff=s->zeta_cutoff=s->period_cutoff=0;
    s->character_count=s->odd_count=s->induced_odd_count=0;
    weighted_remainder_complex_init(&s->mixed_moment);
#define INIT(f) mpq_init(s->f);
    MIXED_FIELDS(INIT)
#undef INIT
}

void weighted_remainder_mixed_moment_clear(WeightedRemainderMixedMoment *s)
{
    weighted_remainder_complex_clear(&s->mixed_moment);
#define CLEAR(f) mpq_clear(s->f);
    MIXED_FIELDS(CLEAR)
#undef CLEAR
}

int weighted_remainder_mixed_moment_compute(WeightedRemainderMixedMoment *out,
    unsigned q,unsigned N,unsigned K,unsigned M)
{
    if (!out || q<2 || q>MAX || N<1 || N>MAX || K<1 || K>MAX || M<2 || M>MAX) return 0;
    CharacterContext ctx;int ok=context_init(&ctx,q);
    if (!ok) { context_clear(&ctx);return 0; }
    WeightedRemainderMixedMoment s;weighted_remainder_mixed_moment_init(&s);
    s.modulus=q;s.cutoff=N;s.zeta_cutoff=K;s.period_cutoff=M;s.character_count=(unsigned)ctx.table.count;
    WeightedRemainderCharacter ch;weighted_remainder_character_init(&ch);
    for (unsigned i=0;i<s.character_count;++i) if (ctx.table.odd[i]) {
        character_with_context(&ch,&ctx,i,N);++s.odd_count;
        if ((unsigned)ctx.table.conductor[i]<q) ++s.induced_odd_count;
        wr_rect_add(&s.mixed_moment,&s.mixed_moment,&ch.mixed_product);
    }
    mpq_t c,jordan,lo,hi,rl,ru;mpq_inits(c,jordan,lo,hi,rl,ru,NULL);
    weighted_remainder_amplitude_factors_q(s.delta,jordan,q);
    weighted_remainder_zeta_three_interval_q(s.zeta_lower,s.zeta_upper,K);
    mpq_set_ui(c,s.character_count,1);mpq_mul(c,c,s.delta);
    mpq_mul(s.denominator_lower,s.zeta_lower,c);mpq_mul(s.denominator_upper,s.zeta_upper,c);
    mpq_inv(lo,s.denominator_upper);mpq_inv(hi,s.denominator_lower);
    wr_product(rl,ru,s.mixed_moment.real_lower,s.mixed_moment.real_upper,lo,hi);
    mpq_set_ui(c,1,2);mpq_sub(s.eta_lower,c,ru);mpq_sub(s.eta_upper,c,rl);
    ok=weighted_remainder_amplitude_interval_q(s.positive_amplitude_lower,s.positive_amplitude_upper,q,M);
    if (mpq_cmp(s.positive_amplitude_lower,s.eta_lower)<0) mpq_set(s.positive_amplitude_lower,s.eta_lower);
    if (mpq_cmp(s.positive_amplitude_upper,s.eta_upper)>0) mpq_set(s.positive_amplitude_upper,s.eta_upper);
    if (ok) {
        out->modulus=q;out->cutoff=N;out->zeta_cutoff=K;out->period_cutoff=M;
        out->character_count=s.character_count;out->odd_count=s.odd_count;out->induced_odd_count=s.induced_odd_count;
        wr_rect_copy(&out->mixed_moment,&s.mixed_moment);
#define COPY(f) mpq_set(out->f,s.f);
        MIXED_FIELDS(COPY)
#undef COPY
    }
    mpq_clears(c,jordan,lo,hi,rl,ru,NULL);weighted_remainder_character_clear(&ch);
    weighted_remainder_mixed_moment_clear(&s);context_clear(&ctx);return ok;
}
