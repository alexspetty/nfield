#include "reset_forest.h"
#include "reset_source.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

static int rf_uint(const char *s, unsigned *out)
{
    if (!s || !*s) return 0;
    for (const char *p=s;*p;p++) if (*p<'0' || *p>'9') return 0;
    errno=0; char *end;
    unsigned long value=strtoul(s,&end,10);
    if (errno || *end || value>RESET_FOREST_MAX_PRIME) return 0;
    *out=(unsigned)value; return 1;
}

static int rf_decimal(const char *s)
{
    size_t length=strlen(s);
    if (!length || length>4096) return 0;
    for (size_t i=0;i<length;i++) if (s[i]<'0' || s[i]>'9') return 0;
    return 1;
}

void reset_forest_help(void)
{
    puts("Reset forests and their contributions to the sampling defect\n\n"
         "  nfield reset-forest <prime> [--returns L | --divisor D] [--json | --csv]\n"
         "  nfield reset-forest source <prime> [--returns L | --divisor D] [--json | --csv]\n\n"
         "  nfield reset-forest project N [--weights c1,...,cN] [--modulus M | --mask k,...]\n"
         "      [--grid Q] [--json | --csv]\n"
         "  Project your own signed rational source with project; use\n"
         "  nfield reset-forest project --help for arbitrary reset selections.\n\n"
         "For N=p-1 and Q=p^2, select k when rough_N(k) divides D.\n"
         "rough_N removes every prime factor supported on N. The default is\n"
         "--returns 3, using D=15(NQ+1)(N^2-N-1) product_{odd j<=L}(Q^j-N^j).\n"
         "Use --divisor 1 for the incoming clocks alone, or supply any positive\n"
         "decimal integer. GMP retains the exact divisor and rational readings.\n\n"
         "The main view returns every reset's signed and absolute work, forest\n"
         "and complementary totals, continuous/sample energies, origin contact\n"
         "and curvature. Each clock reads the full N-harmonic midpoint field.\n"
         "A values are unnormalized; 4*A/Q is their contribution to the defect.\n"
         "The signed_work_bound bounds both |forest_work| and |restoration_work|.\n\n"
         "source returns each harmonic's destination pi(j), collapsed coefficient\n"
         "b_j and complementary coefficient 1-b_j. This is a source projection,\n"
         "not deletion of harmonics or an orthogonal energy partition.\n\n"
         "--json returns exact rational strings, rows and totals. --csv returns\n"
         "reset rows or source rows for plotting and further computation.\n"
         "Limits: odd primes 3..251; return windows 3..31; D at most 4096 digits.\n"
         "These are finite calculations; uniform complementary decay remains open.\n"
         "Separate checks: nfield verify reset-forest");
}

static void rf_json(const ResetForest *r, unsigned window, int source)
{
    gmp_printf("{\"schema\":\"nfield.reset-forest.v1\",\"view\":\"%s\","
               "\"prime\":%u,\"cutoff\":%u,\"grid\":%u,\"divisor\":\"%Zd\","
               "\"return_window\":",source?"source":"work",r->prime,r->cutoff,r->grid,r->divisor);
    if (window) printf("%u",window); else fputs("null",stdout);
    printf(",\"forest_count\":%u,\"values\":{",r->count);
    for (unsigned i=0;i<RF_VALUE_COUNT;i++)
        gmp_printf("%s\"%s\":\"%Qd\"",i?",":"",reset_forest_names[i],r->value[i]);
    fputs("},\"rows\":[",stdout);
    for (unsigned k=source?1:2;k<=r->cutoff;k++) {
        if (k>(source?1u:2u)) putchar(',');
        if (source)
            printf("{\"harmonic\":%u,\"destination\":%u,\"original_coefficient\":1,"
                   "\"forest_coefficient\":%u,\"complement_coefficient\":%ld}",
                   k,r->projection[k],r->population[k],1L-(long)r->population[k]);
        else
            gmp_printf("{\"denominator\":%u,\"rough\":%u,\"selected\":%s,"
                       "\"multiplicity\":%u,\"source_coefficient\":%u,"
                       "\"signed_work\":\"%Qd\",\"absolute_work\":\"%Qd\",\"clock_work\":\"%Qd\"}",
                       k,r->rough[k],r->selected[k]?"true":"false",r->cutoff/k,
                       r->population[k],r->signed_work[k],r->absolute_work[k],r->clock_work[k]);
    }
    puts("]}");
}

static void rf_csv(const ResetForest *r, int source)
{
    if (source) {
        puts("harmonic,destination,original_coefficient,forest_coefficient,complement_coefficient");
        for (unsigned j=1;j<=r->cutoff;j++)
            printf("%u,%u,1,%u,%ld\n",j,r->projection[j],r->population[j],1L-(long)r->population[j]);
    } else {
        puts("denominator,rough,selected,multiplicity,source_coefficient,signed_work,absolute_work,clock_work");
        for (unsigned k=2;k<=r->cutoff;k++)
            gmp_printf("%u,%u,%u,%u,%u,%Qd,%Qd,%Qd\n",k,r->rough[k],r->selected[k],r->cutoff/k,
                       r->population[k],r->signed_work[k],r->absolute_work[k],r->clock_work[k]);
    }
}

static void rf_text(const ResetForest *r, int source)
{
    printf("Reset forest at p=%u, N=%u, Q=%u\n",r->prime,r->cutoff,r->grid);
    gmp_printf("divisor=%Zd\n",r->divisor);
    fputs("Selected resets:",stdout);
    for (unsigned k=2;k<=r->cutoff;k++) if (r->selected[k]) printf(" %u",k);
    fputs("\nComplementary resets:",stdout);
    unsigned count=0;
    for (unsigned k=2;k<=r->cutoff;k++) if (!r->selected[k]) { printf(" %u",k); count++; }
    if (!count) fputs(" none",stdout);
    puts("");
    if (source) {
        puts("\n harmonic  destination  forest coefficient  complement coefficient");
        for (unsigned j=1;j<=r->cutoff;j++)
            printf(" %8u  %11u  %18u  %22ld\n",j,r->projection[j],r->population[j],1L-(long)r->population[j]);
    } else {
        puts("\n k  rough  sector       signed A_k       absolute A_k");
        for (unsigned k=2;k<=r->cutoff;k++)
            gmp_printf("%3u %5u  %-10s  %Qd  %Qd\n",k,r->rough[k],
                       r->selected[k]?"forest":"complement",r->signed_work[k],r->absolute_work[k]);
    }
    puts("");
    for (unsigned i=0;i<RF_VALUE_COUNT;i++)
        gmp_printf("%s=%Qd\n",reset_forest_names[i],r->value[i]);
    printf("\ndefect = origin_contact + 4*(forest_work + complement_work)/%u + curvature\n",r->grid);
    puts("complement_work = complement_clock_work + restoration_work");
}

int reset_forest_command(int argc, char **argv)
{
    if (argc && !strcmp(argv[0], "project")) return reset_source_command(argc - 1, argv + 1);
    if (!argc || (argc==1 && (!strcmp(argv[0],"help") || !strcmp(argv[0],"--help")))) {
        reset_forest_help(); return 0;
    }
    int source=!strcmp(argv[0],"source"), position=source?1:0;
    unsigned prime=0,window=3;
    if (position>=argc || !rf_uint(argv[position++],&prime)) goto bad;
    const char *divisor_text=NULL;
    int selector=0,format=0;
    for (;position<argc;position++) {
        const char *arg=argv[position];
        if (!strcmp(arg,"--returns") || !strcmp(arg,"--divisor")) {
            if (selector || ++position>=argc) goto bad;
            selector=1;
            if (!strcmp(arg,"--returns")) {
                if (!rf_uint(argv[position],&window) || window<3 || window>31) goto bad;
            } else {
                divisor_text=argv[position]; window=0;
                if (!rf_decimal(divisor_text)) goto bad;
            }
        } else if (!strcmp(arg,"--json") || !strcmp(arg,"--csv")) {
            if (format) goto bad;
            format=!strcmp(arg,"--json")?1:2;
        } else goto bad;
    }
    mpz_t divisor; mpz_init(divisor);
    int ok=divisor_text ? mpz_set_str(divisor,divisor_text,10)==0 && mpz_sgn(divisor)>0
                        : reset_forest_return_divisor(divisor,prime,window);
    ResetForest result; reset_forest_init(&result);
    if (ok) ok=reset_forest_compute(&result,prime,divisor);
    if (ok) {
        if (format==1) rf_json(&result,window,source);
        else if (format==2) rf_csv(&result,source);
        else rf_text(&result,source);
    }
    reset_forest_clear(&result); mpz_clear(divisor);
    if (ok) return 0;
bad:
    fputs("Invalid reset-forest input. See nfield help reset-forest.\n",stderr);
    return 1;
}
