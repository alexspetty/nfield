#include "weighted_remainder_spectral.h"
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
    const char *start=p;int slash=0,digits=0;
    for (;*p;++p) {
        if (*p=='/' && !slash && digits) { slash=1;digits=0; }
        else if (*p>='0' && *p<='9') ++digits;
        else return 0;
    }
    if (!digits || mpq_set_str(out,start,10) || mpz_sgn(mpq_denref(out))<=0) return 0;
    mpq_canonicalize(out);return 1;
}

static void print_mean(WeightedRemainderSpectralMean *s)
{
    printf("floor_x=%u\nprime_cutoff=%u\nprime_tail_binary_exponent=%u\n",s->floor_x,s->prime_cutoff,s->prime_tail_binary_exponent);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(x) PRINT(h_sum) PRINT(h_mean) PRINT(correction_floor_sum) PRINT(correction_floor_mean)
    PRINT(correction_series_prefix) PRINT(product_lower) PRINT(product_upper)
    PRINT(nu_sum_lower) PRINT(nu_sum_upper) PRINT(nu_square_sum_lower) PRINT(nu_square_sum_upper)
    PRINT(nu_mean_lower) PRINT(nu_mean_upper) PRINT(nu_square_mean_lower) PRINT(nu_square_mean_upper)
    PRINT(first_prefix_lower) PRINT(first_prefix_upper) PRINT(first_tail_upper) PRINT(first_lower) PRINT(first_upper)
    PRINT(second_prefix_lower) PRINT(second_prefix_upper) PRINT(second_tail_upper) PRINT(second_lower) PRINT(second_upper)
    PRINT(nu_first_mean_bound) PRINT(nu_second_mean_bound)
#undef PRINT
}

static void print_tail(WeightedRemainderSpectralTail *s)
{
    printf("cutoff=%u\nband_cutoff=%u\nperiod_cutoff=%u\nprime_cutoff=%u\nconstant_cutoff=%u\nperiod_binary_exponent=%u\n",
           s->cutoff,s->band_cutoff,s->period_cutoff,s->prime_cutoff,s->constant_cutoff,s->period_binary_exponent);
#define PRINT(f) gmp_printf(#f "=%Qd\n",s->f);
    PRINT(product_lower) PRINT(product_upper) PRINT(amplitude_leading_lower) PRINT(amplitude_leading_upper)
    PRINT(log_q_lower) PRINT(log_q_upper) PRINT(log_b_lower) PRINT(log_b_upper)
    PRINT(weighted_band_lower) PRINT(weighted_band_upper) PRINT(weighted_remainder_upper)
    PRINT(weighted_tail_lower) PRINT(weighted_tail_upper) PRINT(energy_band_lower) PRINT(energy_band_upper)
    PRINT(energy_remainder_upper) PRINT(projection_tail_lower) PRINT(projection_tail_upper)
    PRINT(weighted_leading_lower) PRINT(weighted_leading_upper) PRINT(energy_leading_lower) PRINT(energy_leading_upper)
#undef PRINT
}

int weighted_remainder_spectral_command(int argc,char **argv)
{
    if (argc<3) return 1;
    unsigned Q,B,M,P,N;
    if (!strcmp(argv[2],"spectral-product")) {
        if (argc!=4 || !index_arg(argv[3],1,&P)) goto bad;
        mpq_t l,u;mpq_inits(l,u,NULL);weighted_remainder_spectral_product_q(l,u,P);
        printf("Full spectral Euler-product constant\nprime_cutoff=%u\n",P);
        gmp_printf("product_lower=%Qd\nproduct_upper=%Qd\n",l,u);mpq_clears(l,u,NULL);
    } else if (!strcmp(argv[2],"spectral-mean")) {
        if (argc!=5 || !index_arg(argv[4],1,&P)) goto bad;
        mpq_t x;mpq_init(x);WeightedRemainderSpectralMean s;weighted_remainder_spectral_mean_init(&s);
        int ok=rational_arg(x,argv[3]) && weighted_remainder_spectral_mean_compute(&s,x,P);
        if (ok) { puts("Finite spectral means and full prime moments");print_mean(&s); }
        weighted_remainder_spectral_mean_clear(&s);mpq_clear(x);if (!ok) goto bad;
        puts("The h and signed correction means divide by x; their sums end at floor(x). The correction series prefix is signed finite data.");
    } else if (!strcmp(argv[2],"spectral-energy")) {
        if (argc!=5 || !index_arg(argv[3],2,&Q) || !index_arg(argv[4],2,&M)) goto bad;
        mpq_t al,au,el,eu;mpq_inits(al,au,el,eu,NULL);
        weighted_remainder_spectral_energy_q(al,au,el,eu,Q,M);
        printf("Full conductor energy\nconductor=%u\nperiod_cutoff=%u\n",Q,M);
        gmp_printf("amplitude_lower=%Qd\namplitude_upper=%Qd\nenergy_lower=%Qd\nenergy_upper=%Qd\n",al,au,el,eu);
        mpq_clears(al,au,el,eu,NULL);
        puts("The lower amplitude and energy endpoints equal their finite period-prefix values.");
    } else if (!strcmp(argv[2],"spectral-tail")) {
        if (argc!=8 || !index_arg(argv[3],1,&Q) || !index_arg(argv[4],4,&B) ||
            !index_arg(argv[5],2,&M) || !index_arg(argv[6],1,&P) || !index_arg(argv[7],1,&N)) goto bad;
        WeightedRemainderSpectralTail s;weighted_remainder_spectral_tail_init(&s);
        int ok=weighted_remainder_spectral_tail_compute(&s,Q,B,M,P,N);
        if (ok) { puts("Full conductor tails and sharp leading terms");print_tail(&s); }
        weighted_remainder_spectral_tail_clear(&s);if (!ok) goto bad;
        puts("The band is Q<q<=B, with periods through M. Projection-tail bounds enclose the full squared orthogonal projection error. Leading terms are asymptotic readouts, not tail error bounds.");
    } else return 1;
    puts("Exact rational endpoints; finite computations and infinite proofs are separate.");return 0;
bad:
    fputs("Use spectral-product P; spectral-mean x P; spectral-energy q M; spectral-tail Q B M P N. "
          "Require 1<=Q<=B<=240, B>=4, q,M=2..240, P,N=1..240. "
          "x is rational 1..240: digits or digits/digits, at most 160 characters and 255 bits per reduced component.\n",stderr);
    return 1;
}
