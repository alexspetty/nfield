#include "weighted_remainder_expansion.h"
#include "weighted_remainder_dirichlet.h"
#include <stdio.h>
#include <string.h>

static int bounded(const char *p,unsigned lower,unsigned *out)
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

static int rational(mpq_t out,const char *p)
{
    if (!p || !*p || strlen(p)>160) return 0;
    const char *start=p;int slash=0,digits=0;
    for (;*p;++p) {
        if (*p=='/' && !slash && digits) { slash=1;digits=0; }
        else if (*p>='0' && *p<='9') ++digits;
        else return 0;
    }
    if (!digits || mpq_set_str(out,start,10) || mpz_sgn(mpq_denref(out))<=0) return 0;
    mpq_canonicalize(out);return 1;
}

static void print_constants(WeightedRemainderConstants *s)
{
    printf("constant_cutoff=%u\nlog_tail_binary_exponent=%u\n",s->cutoff,s->log_tail_binary_exponent);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(pi_lower) PRINT(pi_upper) PRINT(zeta_two_lower) PRINT(zeta_two_upper)
    PRINT(zeta_three_lower) PRINT(zeta_three_upper) PRINT(zeta_four_lower) PRINT(zeta_four_upper)
    PRINT(gamma_harmonic_prefix) PRINT(log_n_lower) PRINT(log_n_upper) PRINT(gamma_lower) PRINT(gamma_upper)
    PRINT(log_moment_prefix_lower) PRINT(log_moment_prefix_upper) PRINT(log_moment_tail_upper)
    PRINT(log_moment_lower) PRINT(log_moment_upper) PRINT(kappa_lower) PRINT(kappa_upper)
    PRINT(leading_lower) PRINT(leading_upper)
#undef PRINT
}

static void print_expansion(WeightedRemainderExpansion *s)
{
    printf("conductor=%u\namplitude_expansion_available=%u\nprime_base=%u\nprime_exponent=%u\n",
           s->conductor,s->amplitude_expansion_available,s->prime_base,s->prime_exponent);
    print_constants(&s->constants);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(delta) PRINT(jordan_three) PRINT(totient_ratio) PRINT(rho) PRINT(prime_factor_plus_product)
    PRINT(log_lower) PRINT(log_upper) PRINT(nu_lower) PRINT(nu_upper)
    PRINT(mobius_inverse) PRINT(mobius_log_lower) PRINT(mobius_log_upper)
    PRINT(harmonic_prefix) PRINT(harmonic_error_raw_lower) PRINT(harmonic_error_raw_upper)
    PRINT(harmonic_error_lower) PRINT(harmonic_error_upper) PRINT(harmonic_error_bound)
    PRINT(seed_main_lower) PRINT(seed_main_upper) PRINT(seed_error_bound) PRINT(seed_lower) PRINT(seed_upper)
    if (s->amplitude_expansion_available) {
        PRINT(main_lower) PRINT(main_upper) PRINT(error_upper) PRINT(amplitude_lower) PRINT(amplitude_upper)
    }
    if (s->prime_base) { PRINT(prime_power_main_lower) PRINT(prime_power_main_upper) }
    if (s->prime_exponent==1) { PRINT(prime_leading_lower) PRINT(prime_leading_upper) }
#undef PRINT
}

static void print_series(WeightedRemainderDirichlet *s,const char *prefix)
{
    printf("%scutoff=%u\n%sspecialization=%u\n",prefix,s->cutoff,prefix,s->specialization);
#define PRINT(f) gmp_printf("%s" #f "=%Qd\n",prefix,s->f);
    PRINT(exponent) PRINT(zeta_prefix_lower) PRINT(zeta_prefix_upper) PRINT(zeta_tail_upper)
    PRINT(zeta_lower) PRINT(zeta_upper) PRINT(doubled_prefix_lower) PRINT(doubled_prefix_upper)
    PRINT(doubled_tail_upper) PRINT(doubled_lower) PRINT(doubled_upper)
    PRINT(prefix_lower) PRINT(prefix_upper) PRINT(formula_lower) PRINT(formula_upper)
    if (s->specialization) { PRINT(special_lower) PRINT(special_upper) }
    PRINT(lower) PRINT(upper) PRINT(tail_upper)
#undef PRINT
}

int weighted_remainder_expansion_command(int argc,char **argv)
{
    if (argc<3) return 1;
    const char *op=argv[2];unsigned N,q;
    if (!strcmp(op,"expansion-constants")) {
        if (argc!=4 || !bounded(argv[3],1,&N)) goto constants_bad;
        WeightedRemainderConstants s;weighted_remainder_constants_init(&s);
        int ok=weighted_remainder_constants_compute(&s,N);
        if (ok) { puts("Uniform amplitude constants");print_constants(&s); }
        weighted_remainder_constants_clear(&s);if (!ok) goto constants_bad;
    } else if (!strcmp(op,"harmonic-expansion") || !strcmp(op,"amplitude-expansion")) {
        unsigned minimum=!strcmp(op,"amplitude-expansion") ? 2 : 1;
        if (argc!=5 || !bounded(argv[3],minimum,&q) || !bounded(argv[4],1,&N)) goto expansion_bad;
        WeightedRemainderExpansion s;weighted_remainder_expansion_init(&s);
        int ok=weighted_remainder_expansion_compute(&s,q,N);
        if (ok) { puts("Harmonic seed and uniform amplitude expansion");print_expansion(&s); }
        weighted_remainder_expansion_clear(&s);if (!ok) goto expansion_bad;
    } else if (!strcmp(op,"deficit-series")) {
        if (argc!=5 || !bounded(argv[4],1,&N)) goto series_bad;
        mpq_t exponent;mpq_init(exponent);
        WeightedRemainderDirichlet s;weighted_remainder_dirichlet_init(&s);
        int ok=rational(exponent,argv[3]) && weighted_remainder_dirichlet_compute(&s,exponent,N);
        if (ok) { puts("Positive Dirichlet deficit series");print_series(&s,""); }
        weighted_remainder_dirichlet_clear(&s);mpq_clear(exponent);if (!ok) goto series_bad;
    } else if (!strcmp(op,"deficit-diagnostic")) {
        if (argc!=4 || !bounded(argv[3],1,&N)) goto diagnostic_bad;
        WeightedRemainderDeficitDiagnostic s;weighted_remainder_deficit_diagnostic_init(&s);
        int ok=weighted_remainder_deficit_diagnostic_compute(&s,N);
        if (ok) {
            puts("Dirichlet deficit positivity diagnostic");print_series(&s.two,"two_");print_series(&s.three_halves,"three_halves_");
#define PRINT(f) gmp_printf(#f "=%Qd\n",s.f);
            PRINT(two_weight) PRINT(three_halves_weight) PRINT(loss_lower) PRINT(loss_upper)
            PRINT(margin_lower) PRINT(margin_upper) PRINT(literal_loss_bound) PRINT(literal_margin)
#undef PRINT
            puts("The full weighted loss is strictly below 3979/8000; its margin is strictly above 4021/8000 and one half.");
        }
        weighted_remainder_deficit_diagnostic_clear(&s);if (!ok) goto diagnostic_bad;
    } else return 1;
    puts("Exact rational intervals enclose full values. Positive prefixes are finite; infinite identities and bounds are proved separately.");
    return 0;
constants_bad:
    fputs("expansion-constants requires cutoff 1..240.\n",stderr);return 1;
expansion_bad:
    fputs("harmonic-expansion requires conductor 1..240 and cutoff 1..240; amplitude-expansion requires conductor 2..240.\n",stderr);return 1;
series_bad:
    fputs("deficit-series requires rational exponent 1<s<=6 and cutoff 1..240; use digits or digits/digits, at most 160 characters and 255 bits per reduced component.\n",stderr);return 1;
diagnostic_bad:
    fputs("deficit-diagnostic requires cutoff 1..240.\n",stderr);return 1;
}
