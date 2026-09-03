/* Finite odd-character pairing and higher-lag assignment ledgers. */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "finite_character_core.h"
#include "nfield.h"

enum {
    PAIRING_ROW_COUNT = 14,
    PAIRING_CUTOFF_COUNT = 5,
    PAIRING_MAX_MODULUS = 7000
};

static const int pairing_rows[PAIRING_ROW_COUNT][2] = {
    {3, 1}, {3, 2}, {3, 3}, {3, 4}, {3, 5}, {3, 6}, {3, 7},
    {5, 1}, {5, 2}, {5, 3}, {5, 4},
    {7, 1}, {7, 2}, {7, 3}
};

static const int pairing_cutoffs[PAIRING_CUTOFF_COUNT] = {
    250000, 500000, 1000000, 2000000, 5000000
};

typedef struct {
    int base;
    int lag;
    int primes;
    int active;
    int inactive;
    int positive;
    int negative;
    int correlation_defined;
    long double net;
    long double correlation;
} ExpectedPairingRow;

static const ExpectedPairingRow expected_primary[PAIRING_ROW_COUNT] = {
    {3,1,148929,2,1,2,0,0, 0.618769951754L, 0.0L},
    {3,2,148924,8,1,4,4,1, 1.182669778793L, 0.416358427L},
    {3,3,148911,26,1,14,12,1, 0.616980320805L,-0.419732209L},
    {3,4,148880,80,1,34,46,1, 4.825182591844L,-0.275489188L},
    {3,5,148804,242,1,142,100,1,12.770973729841L,-0.326538431L},
    {3,6,148606,728,1,358,370,1,29.145247625115L,-0.326717004L},
    {3,7,148086,2186,1,1162,1024,1,10.357829314248L,-0.201591931L},
    {5,1,148924,8,2,6,2,1, 1.034798487902L,-0.451095820L},
    {5,2,148903,48,2,32,16,1,4.009357238663L,-0.176705295L},
    {5,3,148819,248,2,132,116,1,2.482805603362L,-0.277620401L},
    {5,4,148488,1248,2,634,614,1,15.256874179581L,-0.190393649L},
    {7,1,148918,18,3,10,8,1,1.812202507634L,-0.276189709L},
    {7,2,148865,144,3,86,58,1,7.564420407590L,-0.216332478L},
    {7,3,148576,1026,3,506,520,1,4.583791325193L,-0.156944807L}
};

static const long double expected_trends[3][PAIRING_CUTOFF_COUNT] = {
    {-0.051507739L,-0.087531833L,-0.140712181L,-0.201591931L,-0.246756535L},
    {-0.078365713L,-0.101838048L,-0.144508771L,-0.190393649L,-0.232988487L},
    {-0.046648602L,-0.099049227L,-0.129961407L,-0.156944807L,-0.214195964L}
};

static int validate_pairing_input(int base, int lag, int cutoff, int report)
{
    int modulus = 0;
    if (!finite_character_is_prime(base) || base == 2) {
        if (report) fprintf(stderr, "base must be an odd prime\n");
        return 0;
    }
    if (lag < 1 || !collision_table_modulus(base, lag, &modulus) ||
        modulus > PAIRING_MAX_MODULUS) {
        if (report)
            fprintf(stderr,
                    "base^(lag+1) must be at most %d for a character audit\n",
                    PAIRING_MAX_MODULUS);
        return 0;
    }
    if (cutoff <= modulus || cutoff > FINITE_CHARACTER_MAX_CUTOFF) {
        if (report)
            fprintf(stderr, "cutoff must satisfy modulus < cutoff <= %d\n",
                    FINITE_CHARACTER_MAX_CUTOFF);
        return 0;
    }
    return 1;
}

static void print_header(void)
{
    printf("  b  ell      q    primes active/inactive    +/-      net          rho       error\n");
}

static void print_row(const CollisionCenteredTable *table,
                      const FiniteCharacterPairingAudit *audit,
                      int cutoff_index)
{
    const FiniteCharacterPairingStats *stats =
        &audit->stats[cutoff_index];
    printf(" %2d  %2d  %5d  %8d  %5d/%-5d %5d/%-5d %+.9Lf  ",
           table->base, table->lag, table->modulus,
           audit->prime_count[cutoff_index], audit->active, audit->inactive,
           stats->positive, stats->negative, stats->net);
    if (stats->correlation_defined) printf("%+.6Lf", stats->correlation);
    else printf("undefined");
    printf("  %+.2Le\n", stats->decomposition_error);
}

static int one_pairing(int base, int lag, int cutoff, int report,
                       FiniteCharacterPairingAudit *result)
{
    CollisionCenteredTable table = {0};
    FiniteCharacterPairingAudit audit;
    int *primes = NULL;
    int prime_count = 0;
    int failures = 0;

    if (!validate_pairing_input(base, lag, cutoff, report)) return 1;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    primes = finite_character_primes(cutoff, &prime_count);
    if (!primes) {
        collision_centered_table_free(&table);
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures += centered_collision_table_audit(&table, NULL, NULL);
    failures += finite_character_pairing_audit(
        &table, primes, prime_count, &cutoff, 1, &audit);
    if (report) {
        printf("Finite character pairing\n");
        printf("One odd-character assignment ledger\n\n");
        printf("  interval: %d < p < %d; exponent sigma=1/2\n",
               table.modulus, cutoff);
        printf("  retained coefficient threshold: 1e-10\n\n");
        print_header();
        print_row(&table, &audit, 0);
        printf("\n  direct prime sum = %+.12Lf\n", audit.stats[0].direct);
        printf("  character decomposition = %+.12Lf\n", audit.stats[0].net);
        printf("  decomposition error = %+.3Le  %s\n",
               audit.stats[0].decomposition_error,
               failures == 0 ? "PASS" : "FAIL");
        printf("\nClassification  finite numerical evidence with an exact finite\n");
        printf("collision table and a long-double character transform.\n");
        printf("It is not a limiting correlation or an infinite prime sum.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    if (result) *result = audit;
    free(primes);
    collision_centered_table_free(&table);
    return failures;
}

int finite_character_pairing_one(int base, int lag, int cutoff)
{
    return one_pairing(base, lag, cutoff, 1, NULL) == 0 ? 0 : 1;
}

static int published_rows_audit(const int *primes, int prime_count,
                                int cutoff, int report,
                                int compare_fixtures,
                                int *negative_correlations,
                                int *positive_correlations,
                                int *undefined_correlations,
                                long double *largest_error)
{
    int failures = 0;
    int negative = 0, positive = 0, undefined = 0;
    long double maximum_error = 0.0L;

    if (report) {
        printf("Higher-lag character assignment\n");
        printf("Fourteen declared finite rows\n\n");
        printf("Finite interval q < p < %d; sigma=1/2.\n", cutoff);
        printf("Exact table checks precede each numerical character row.\n\n");
        print_header();
    }
    for (int row = 0; row < PAIRING_ROW_COUNT; row++) {
        CollisionCenteredTable table = {0};
        FiniteCharacterPairingAudit audit;
        const FiniteCharacterPairingStats *stats;

        if (!collision_centered_table_build(
                pairing_rows[row][0], pairing_rows[row][1], &table)) {
            failures++;
            continue;
        }
        failures += centered_collision_table_audit(&table, NULL, NULL);
        failures += finite_character_pairing_audit(
            &table, primes, prime_count, &cutoff, 1, &audit);
        stats = &audit.stats[0];
        if (stats->correlation_defined) {
            if (stats->correlation < 0.0L) negative++;
            else positive++;
        } else undefined++;
        if (fabsl(stats->decomposition_error) > maximum_error)
            maximum_error = fabsl(stats->decomposition_error);
        if (compare_fixtures && cutoff == 2000000) {
            const ExpectedPairingRow *expected = &expected_primary[row];
            if (audit.prime_count[0] != expected->primes ||
                audit.active != expected->active ||
                audit.inactive != expected->inactive ||
                stats->positive != expected->positive ||
                stats->negative != expected->negative ||
                stats->correlation_defined != expected->correlation_defined ||
                fabsl(stats->net - expected->net) > 5.0e-9L ||
                (expected->correlation_defined &&
                 fabsl(stats->correlation - expected->correlation) > 5.0e-7L))
                failures++;
        }
        if (report) print_row(&table, &audit, 0);
        collision_centered_table_free(&table);
    }
    if (report) {
        printf("\nDefined Pearson correlations: %d negative, %d positive;",
               negative, positive);
        printf(" %d undefined from zero variance.\n", undefined);
        printf("Largest direct/decomposition error = %.3Le.\n",
               maximum_error);
        if (cutoff == 2000000)
            printf("Declared count, sign, net, and correlation fixtures  %s\n",
                   failures == 0 ? "PASS" : "FAIL");
        else
            printf("This cutoff explores the same finite definition; it is not a declared fixture.\n");
        printf("\nClassification  finite numerical evidence, not an asymptotic theorem.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    if (negative_correlations) *negative_correlations = negative;
    if (positive_correlations) *positive_correlations = positive;
    if (undefined_correlations) *undefined_correlations = undefined;
    if (largest_error) *largest_error = maximum_error;
    return failures;
}

int finite_character_pairing_declared_rows(int cutoff)
{
    int *primes;
    int prime_count = 0;
    int failures;

    if (cutoff <= 6561 || cutoff > FINITE_CHARACTER_MAX_CUTOFF) {
        fprintf(stderr, "cutoff must satisfy 6561 < cutoff <= %d\n",
                FINITE_CHARACTER_MAX_CUTOFF);
        return 1;
    }
    primes = finite_character_primes(cutoff, &prime_count);
    if (!primes) {
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures = published_rows_audit(
        primes, prime_count, cutoff, 1, cutoff == 2000000,
        NULL, NULL, NULL, NULL);
    free(primes);
    return failures == 0 ? 0 : 1;
}

static int cutoff_trend_audit(const int *primes, int prime_count, int report)
{
    static const int deepest_rows[3][2] = {{3, 7}, {5, 4}, {7, 3}};
    int failures = 0;

    if (report) {
        printf("Higher-lag character assignment\n");
        printf("Deepest-lag cutoff trend\n\n");
        printf("Finite Pearson correlations at sigma=1/2\n");
        printf("  b ell    250000     500000    1000000    2000000    5000000\n");
    }
    for (int row = 0; row < 3; row++) {
        CollisionCenteredTable table = {0};
        FiniteCharacterPairingAudit audit;
        if (!collision_centered_table_build(
                deepest_rows[row][0], deepest_rows[row][1], &table)) {
            failures++;
            continue;
        }
        failures += centered_collision_table_audit(&table, NULL, NULL);
        failures += finite_character_pairing_audit(
            &table, primes, prime_count,
            pairing_cutoffs, PAIRING_CUTOFF_COUNT, &audit);
        if (report)
            printf(" %2d  %2d", deepest_rows[row][0], deepest_rows[row][1]);
        for (int cutoff_index = 0; cutoff_index < PAIRING_CUTOFF_COUNT;
             cutoff_index++) {
            FiniteCharacterPairingStats *stats = &audit.stats[cutoff_index];
            if (!stats->correlation_defined ||
                fabsl(stats->correlation -
                      expected_trends[row][cutoff_index]) > 5.0e-7L)
                failures++;
            if (cutoff_index > 0 && stats->correlation >=
                                      audit.stats[cutoff_index - 1].correlation)
                failures++;
            if (report) printf("  %+.6Lf", stats->correlation);
        }
        if (report) printf("\n");
        collision_centered_table_free(&table);
    }
    if (report) {
        printf("\nAll fifteen displayed values and all three strict downward trends  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("The base-three lag-seven net changes sign twice in these windows;\n");
        printf("the correlation trend therefore supplies finite evidence only.\n");
        printf("Classification  finite numerical evidence; no limiting claim.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    return failures;
}

int finite_character_pairing_cutoff_trend(void)
{
    int *primes;
    int prime_count = 0;
    int failures;

    primes = finite_character_primes(
        FINITE_CHARACTER_MAX_CUTOFF, &prime_count);
    if (!primes) {
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures = cutoff_trend_audit(primes, prime_count, 1);
    free(primes);
    return failures == 0 ? 0 : 1;
}

int finite_character_pairing_verify(void)
{
    int *primes;
    int prime_count = 0;
    int negative = 0, positive = 0, undefined = 0;
    long double largest_error = 0.0L;
    int rows_ok, trends_ok;
    int passed = 0;

    printf("Finite character pairing verification\n\n");
    primes = finite_character_primes(
        FINITE_CHARACTER_MAX_CUTOFF, &prime_count);
    if (!primes) {
        printf("unable to allocate the prime sieve\n");
        return 0;
    }
    rows_ok = published_rows_audit(
        primes, prime_count, 2000000, 0, 1,
        &negative, &positive, &undefined, &largest_error) == 0;
    trends_ok = cutoff_trend_audit(primes, prime_count, 0) == 0;
    free(primes);

    printf("  fourteen declared row fixtures                         %s\n",
           rows_ok ? "PASS" : "FAIL");
    if (rows_ok) passed++;
    printf("  correlations: 12 negative, 1 positive, 1 undefined   %s\n",
           rows_ok && negative == 12 && positive == 1 && undefined == 1
               ? "PASS" : "FAIL");
    if (rows_ok && negative == 12 && positive == 1 && undefined == 1)
        passed++;
    printf("  direct/decomposed error below 2.4e-14                 %s\n",
           rows_ok && largest_error < 2.4e-14L ? "PASS" : "FAIL");
    if (rows_ok && largest_error < 2.4e-14L) passed++;
    printf("  fifteen finite cutoff correlations and trends         %s\n",
           trends_ok ? "PASS" : "FAIL");
    if (trends_ok) passed++;
    printf("\n%d/4 verification groups passed.\n", passed);
    printf("Classification  finite numerical evidence with exact table inputs.\n");
    printf("Boundary  cutoff-uniform assignment control and infinite convergence\n");
    printf("remain open.\n");
    return passed == 4;
}

void finite_character_pairing_help(void)
{
    printf(
        "Finite character pairing\n\n"
        "Commands\n"
        "  nfield finite-character-pairing one <base> <lag> [--cutoff <X>]\n"
        "      Compute one odd-character pairing at sigma=1/2.\n"
        "  nfield finite-character-pairing declared-rows [--cutoff <X>]\n"
        "      Recompute the fourteen declared base/lag rows. At X=2000000\n"
        "      the command also checks every recorded fixture.\n"
        "  nfield finite-character-pairing cutoff-trend\n"
        "      Reproduce five cutoffs for (3,7), (5,4), and (7,3).\n"
        "  nfield finite-character-pairing verify\n"
        "  nfield verify finite-character-pairing\n\n"
        "Scope\n"
        "  exact input       Centered collision tables are checked exactly.\n"
        "  finite evidence   Character transforms, correlations, signs, and\n"
        "                    trends use explicitly printed finite intervals.\n"
        "  numerical method Long-double transforms are checked against direct\n"
        "                    finite prime sums and declared fixtures.\n"
        "  open             Cutoff-uniform correlation and infinite convergence.\n"
    );
}
