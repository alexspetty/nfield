#include "weighted_remainder_character.h"
#include "weighted_remainder_cotangent.h"
#include "weighted_remainder_harmonic_root.h"
#include "weighted_remainder_small_amplitude.h"
#include "finite_character_core.h"
#include <stdio.h>
#include <string.h>

static int index_arg(const char *p,unsigned lower,unsigned *out)
{
    if (!p || !*p) return 0;
    unsigned n=0;
    for (;*p;++p) {
        if (*p<'0' || *p>'9') return 0;
        n=10*n+(unsigned)(*p-'0');if (n>WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    }
    if (n<lower) return 0;
    *out=n;return 1;
}
static int rational_arg(mpq_t out,const char *p)
{
    if (!p || !*p || strlen(p)>160) return 0;
    const char *start=p;if (*p=='-') ++p;
    int slash=0,digits=0;
    for (;*p;++p) {
        if (*p=='/' && !slash && digits) { slash=1;digits=0; }
        else if (*p>='0' && *p<='9') ++digits;
        else return 0;
    }
    if (!digits || mpq_set_str(out,start,10) || mpz_sgn(mpq_denref(out))<=0) return 0;
    mpq_canonicalize(out);return 1;
}
static int frequency_arg(mpz_t out,const char *p)
{
    if (!p || !*p || strlen(p)>1000) return 0;
    const char *start=p;if (*p=='-') ++p;
    if (!*p) return 0;
    for (;*p;++p) if (*p<'0' || *p>'9') return 0;
    return !mpz_set_str(out,start,10);
}
static void print_complex(const char *name,const WeightedRemainderComplex *s)
{
    gmp_printf("%s_real_lower=%Qd\n%s_real_upper=%Qd\n%s_imag_lower=%Qd\n%s_imag_upper=%Qd\n",
        name,s->real_lower,name,s->real_upper,name,s->imag_lower,name,s->imag_upper);
}
static void print_character(const WeightedRemainderCharacter *s)
{
    printf("modulus=%u\ncharacter_index=%u\ncharacter_conductor=%u\nphase_denominator=%u\nseries_cutoff=%u\n",
        s->modulus,s->index,s->conductor,s->denominator,s->cutoff);
    print_complex("cotangent_coefficient",&s->cotangent_coefficient);
    print_complex("l_one_conjugate",&s->l_one_conjugate);print_complex("l_two_prefix",&s->l_two_prefix);
    print_complex("l_two",&s->l_two);print_complex("mixed_product",&s->mixed_product);
    gmp_printf("l_two_norm_tail_upper=%Qd\n",s->l_two_tail);
}
static void print_mixed(const WeightedRemainderMixedMoment *s)
{
    printf("modulus=%u\nseries_cutoff=%u\nzeta_cutoff=%u\nperiod_cutoff=%u\ncharacter_count=%u\nodd_count=%u\ninduced_odd_count=%u\n",
        s->modulus,s->cutoff,s->zeta_cutoff,s->period_cutoff,s->character_count,s->odd_count,s->induced_odd_count);
    print_complex("mixed_moment",&s->mixed_moment);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(delta) PRINT(zeta_lower) PRINT(zeta_upper) PRINT(denominator_lower) PRINT(denominator_upper)
    PRINT(eta_lower) PRINT(eta_upper) PRINT(positive_amplitude_lower) PRINT(positive_amplitude_upper)
#undef PRINT
}
static void print_cotangent(const WeightedRemainderCotangent *s)
{
    printf("modulus=%u\nseries_cutoff=%u\nzeta_cutoff=%u\n",s->modulus,s->cutoff,s->zeta_cutoff);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(residue_bound) PRINT(unit_residue_bound) PRINT(prefix_lower) PRINT(prefix_upper)
    PRINT(unit_prefix_lower) PRINT(unit_prefix_upper) PRINT(tail_upper) PRINT(unit_tail_upper)
    PRINT(lower) PRINT(upper) PRINT(unit_lower) PRINT(unit_upper) PRINT(gcd_prefix_lower) PRINT(gcd_prefix_upper)
    PRINT(mobius_prefix_lower) PRINT(mobius_prefix_upper) PRINT(gcd_lower) PRINT(gcd_upper) PRINT(mobius_lower) PRINT(mobius_upper)
    PRINT(zeta_lower) PRINT(zeta_upper) PRINT(delta) PRINT(harmonic_seed_lower) PRINT(harmonic_seed_upper)
    PRINT(eta_lower) PRINT(eta_upper)
#undef PRINT
}
static void print_root(const WeightedRemainderHarmonicRoot *s)
{
    printf("phase_denominator=%u\nphase_numerator=%u\nseries_cutoff=%u\nzeta_cutoff=%u\nbinary_exponent=%u\n",
        s->denominator,s->numerator,s->cutoff,s->zeta_cutoff,s->binary_exponent);
    print_complex("phase",&s->phase);print_complex("harmonic_prefix",&s->harmonic_prefix);print_complex("harmonic",&s->harmonic);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(harmonic_tail_upper) PRINT(cubic_prefix_lower) PRINT(cubic_prefix_upper) PRINT(cubic_tail_upper)
    PRINT(cubic_lower) PRINT(cubic_upper) PRINT(sine_prefix_lower) PRINT(sine_prefix_upper) PRINT(sine_tail_upper)
    PRINT(sine_lower) PRINT(sine_upper) PRINT(zeta_lower) PRINT(zeta_upper) PRINT(angle_weight_lower) PRINT(angle_weight_upper)
    PRINT(identity_lower) PRINT(identity_upper)
#undef PRINT
}
static void print_small(const WeightedRemainderSmallAmplitude *s)
{
    printf("series_cutoff=%u\nzeta_cutoff=%u\n",s->cutoff,s->zeta_cutoff);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(three_prefix) PRINT(three_lower) PRINT(three_upper) PRINT(catalan_prefix) PRINT(catalan_lower) PRINT(catalan_upper)
    PRINT(six_prefix) PRINT(six_lower) PRINT(six_upper) PRINT(induced_prefix_rhs) PRINT(induced_factor)
    PRINT(induced_lower) PRINT(induced_upper) PRINT(l_tail_upper) PRINT(zeta_lower) PRINT(zeta_upper)
    PRINT(sqrt_three_lower) PRINT(sqrt_three_upper) PRINT(eta_three_lower) PRINT(eta_three_upper)
    PRINT(eta_four_lower) PRINT(eta_four_upper) PRINT(eta_six_direct_lower) PRINT(eta_six_direct_upper)
    PRINT(eta_six_relation_lower) PRINT(eta_six_relation_upper)
#undef PRINT
}

int weighted_remainder_mixed_command(int argc,char **argv)
{
    if (argc<3) return 1;
    unsigned q,a,N,K,M;const char *action=argv[2];
    if (!strcmp(action,"character-phase")) {
        if (argc!=5 || !index_arg(argv[3],1,&q) || !index_arg(argv[4],0,&a)) goto bad;
        WeightedRemainderComplex s;weighted_remainder_complex_init(&s);
        int ok=weighted_remainder_complex_phase_q(s.real_lower,s.real_upper,s.imag_lower,s.imag_upper,q,a);
        if (ok) { printf("Complex root of unity\nphase_denominator=%u\nphase_numerator=%u\n",q,a);print_complex("phase",&s); }
        weighted_remainder_complex_clear(&s);if (!ok) goto bad;
    } else if (!strcmp(action,"character-table")) {
        if (argc!=4 || !index_arg(argv[3],2,&q)) goto bad;
        FiniteCharacterTable t={0};int ok=finite_character_table_build((int)q,&t);if (!ok) goto bad;
        printf("Full unit-group character table\nmodulus=%u\ncharacter_count=%d\nphase_denominator=%d\n",q,t.count,t.denominator);
        puts("Rows: index conductor odd phases-by-residue; phase -1 denotes a zero character value on a nonunit.");
        for (int i=0;i<t.count;++i) {
            printf("character %d %d %u",i,t.conductor[i],(unsigned)t.odd[i]);
            for (unsigned r=0;r<q;++r) printf(" %d",t.phase[i*q+r]);
            putchar('\n');
        }
        finite_character_table_free(&t);
    } else if (!strcmp(action,"character-l")) {
        if (argc!=6 || !index_arg(argv[3],2,&q) || !index_arg(argv[4],0,&a) || !index_arg(argv[5],1,&N)) goto bad;
        WeightedRemainderCharacter s;weighted_remainder_character_init(&s);
        int ok=weighted_remainder_character_compute(&s,q,a,N);
        if (ok) { puts("Odd-character L-values and mixed product");print_character(&s); }
        weighted_remainder_character_clear(&s);if (!ok) goto bad;
        puts("L(1) uses the conjugate character and its naturally ordered value. L(2) retains a finite prefix and a separate norm tail.");
    } else if (!strcmp(action,"mixed-moment")) {
        if (argc!=7 || !index_arg(argv[3],2,&q) || !index_arg(argv[4],1,&N) ||
            !index_arg(argv[5],1,&K) || !index_arg(argv[6],2,&M)) goto bad;
        WeightedRemainderMixedMoment s;weighted_remainder_mixed_moment_init(&s);
        int ok=weighted_remainder_mixed_moment_compute(&s,q,N,K,M);
        if (ok) { puts("Full odd-character mixed moment");print_mixed(&s); }
        weighted_remainder_mixed_moment_clear(&s);if (!ok) goto bad;
        puts("All odd characters, including induced characters, enter the sum. The raw imaginary interval is retained; reality is proved separately. Positive-amplitude fields intersect the raw eta formula with the positive period enclosure.");
    } else if (!strcmp(action,"cotangent-sums")) {
        if (argc!=6 || !index_arg(argv[3],1,&q) || !index_arg(argv[4],1,&N) || !index_arg(argv[5],1,&K)) goto bad;
        WeightedRemainderCotangent s;weighted_remainder_cotangent_init(&s);
        int ok=weighted_remainder_cotangent_compute(&s,q,N,K);
        if (ok) { puts("Cotangent series, divisor descent and amplitude");print_cotangent(&s); }
        weighted_remainder_cotangent_clear(&s);if (!ok) goto bad;
        puts("Finite gcd and Mobius prefixes use floor(N*d/q) and floor(N/d). Full divisor series use their own tails at cutoff N. Both cotangent sums vanish at q=1; its amplitude is one.");
    } else if (!strcmp(action,"harmonic-polylog")) {
        if (argc!=6 || !index_arg(argv[5],1,&N)) goto bad;
        mpq_t re,im;mpq_inits(re,im,NULL);WeightedRemainderHarmonicPolylog s;weighted_remainder_harmonic_polylog_init(&s);
        int ok=rational_arg(re,argv[3]) && rational_arg(im,argv[4]) && weighted_remainder_harmonic_polylog_compute(&s,re,im,N);
        if (ok) {
            printf("Harmonic polylogarithm on the closed unit disk\nseries_cutoff=%u\nbinary_exponent=%u\n",s.cutoff,s.binary_exponent);
            gmp_printf("z_real=%Qd\nz_imag=%Qd\ntail_upper=%Qd\n",s.z_real,s.z_imag,s.tail_upper);
            print_complex("prefix",&s.prefix);print_complex("value",&s.value);
        }
        weighted_remainder_harmonic_polylog_clear(&s);mpq_clears(re,im,NULL);if (!ok) goto bad;
    } else if (!strcmp(action,"harmonic-root")) {
        if (argc!=7 || !index_arg(argv[3],1,&q) || !index_arg(argv[4],0,&a) ||
            !index_arg(argv[5],1,&N) || !index_arg(argv[6],1,&K)) goto bad;
        WeightedRemainderHarmonicRoot s;weighted_remainder_harmonic_root_init(&s);
        int ok=weighted_remainder_harmonic_root_compute(&s,q,a,N,K);
        if (ok) { puts("Harmonic root, cubic cosine and quadratic sine series");print_root(&s); }
        weighted_remainder_harmonic_root_clear(&s);if (!ok) goto bad;
        puts("The identity interval evaluates the root formula separately. Angle zero retains the exact zeta and zero-sine endpoint identities.");
    } else if (!strcmp(action,"harmonic-root-average")) {
        if (argc!=5 || !index_arg(argv[3],1,&q) || !index_arg(argv[4],1,&N)) goto bad;
        WeightedRemainderHarmonicRootAverage s;weighted_remainder_harmonic_root_average_init(&s);
        int ok=weighted_remainder_harmonic_root_average_compute(&s,q,N);
        if (ok) {
            printf("Finite harmonic root average and full seed\nmodulus=%u\nseries_cutoff=%u\nbinary_exponent=%u\n",s.modulus,s.cutoff,s.binary_exponent);
            print_complex("root_average_prefix",&s.root_average_prefix);
            gmp_printf("selected_prefix=%Qd\ntail_upper=%Qd\nlower=%Qd\nupper=%Qd\n",s.selected_prefix,s.tail_upper,s.lower,s.upper);
        }
        weighted_remainder_harmonic_root_average_clear(&s);if (!ok) goto bad;
    } else if (!strcmp(action,"sine-transform")) {
        if (argc!=5 || !index_arg(argv[3],1,&q)) goto bad;
        mpz_t n;mpz_init(n);mpq_t l,u,rl,ru;mpq_inits(l,u,rl,ru,NULL);
        int ok=frequency_arg(n,argv[4]) && weighted_remainder_sine_transform_q(l,u,rl,ru,q,n);
        if (ok) {
            printf("Finite sine transform\nmodulus=%u\n",q);gmp_printf("frequency=%Zd\n",n);
            gmp_printf("lower=%Qd\nupper=%Qd\ncotangent_rhs_lower=%Qd\ncotangent_rhs_upper=%Qd\n",l,u,rl,ru);
        }
        mpz_clear(n);mpq_clears(l,u,rl,ru,NULL);if (!ok) goto bad;
    } else if (!strcmp(action,"small-amplitudes")) {
        if (argc!=5 || !index_arg(argv[3],1,&N) || !index_arg(argv[4],1,&K)) goto bad;
        WeightedRemainderSmallAmplitude s;weighted_remainder_small_amplitude_init(&s);
        int ok=weighted_remainder_small_amplitude_compute(&s,N,K);
        if (ok) { puts("Conductor-three, four and six amplitude examples");print_small(&s); }
        weighted_remainder_small_amplitude_clear(&s);if (!ok) goto bad;
        puts("Catalan is L(2,chi_-4). The finite induced prefix uses floor(N/2); the full induced L-value factor is 5/4. The direct and affine eta-six intervals are separate readouts.");
    } else return 1;
    puts("Exact rational endpoints; finite computations and infinite proofs are separate.");return 0;
bad:
    fputs("Use character-phase q a; character-table q; character-l q index N; mixed-moment q N K M; "
          "cotangent-sums q N K; harmonic-polylog real imag N; harmonic-root q a N K; "
          "harmonic-root-average q N; sine-transform q frequency; small-amplitudes N K. "
          "q,N,K=1..240, M=2..240; character-table, character-l and mixed-moment require q>=2. "
          "Require 0<=a<q and an odd character index from character-table. "
          "Polylog coordinates are signed digits or signed digits/digits, <=160 characters each, "
          "with <=63-bit reduced components and real^2+imag^2<=1. Frequency is signed decimal, <=1000 characters.\n",stderr);
    return 1;
}
