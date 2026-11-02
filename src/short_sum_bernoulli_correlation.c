/* Exhaustive finite correlation between short sums and Bernoulli magnitudes. */

#include <math.h>
#include <stdio.h>

#include "collision_spectrum_core.h"
#include "collision_magnitude_moments.h"
#include "nfield.h"

enum { SHORT_SUM_BASE_COUNT = 18 };

static const int short_sum_bases[SHORT_SUM_BASE_COUNT] = {
    5, 7, 11, 13, 17, 19, 23, 29, 31,
    37, 41, 43, 47, 53, 59, 61, 67, 71
};

static const int short_sum_character_counts[SHORT_SUM_BASE_COUNT] = {
    8, 18, 50, 72, 128, 162, 242, 392, 450,
    648, 800, 882, 1058, 1352, 1682, 1800, 2178, 2450
};

static const long double expected_correlations[SHORT_SUM_BASE_COUNT] = {
    1.000000000000L, 0.844013736013L, 0.804214041995L,
    0.800442004939L, 0.792520345533L, 0.763013414761L,
    0.751734181510L, 0.720322754318L, 0.726701324255L,
    0.708003796298L, 0.711125809014L, 0.698702485740L,
    0.687537799051L, 0.685638389183L, 0.675935418585L,
    0.679046206131L, 0.669011597085L, 0.675316900552L
};

static int correlation_ledger_audit(int report,
                                    int *character_count_out,
                                    long double *maximum_error_out)
{
    int failures = 0;
    int character_count = 0;
    long double maximum_error = 0.0L;

    if (report) {
        printf("Short-sum and Bernoulli correlation\n");
        printf("Exhaustive finite character ledger\n\n");
        printf("  b   primitive odd characters   correlation\n");
    }
    for (int index = 0; index < SHORT_SUM_BASE_COUNT; index++) {
        CollisionMagnitudeMoments summary = collision_magnitude_moments(short_sum_bases[index]);
        long double error;
        if (summary.failures) {
            failures++;
            continue;
        }
        character_count += summary.count;
        error = fabsl(summary.correlation - expected_correlations[index]);
        if (error > maximum_error) maximum_error = error;
        if (summary.count != short_sum_character_counts[index] ||
            error > 5.0e-12L)
            failures++;
        if (report)
            printf(" %2d          %4d              %.12Lf\n",
                   summary.base, summary.count,
                   summary.correlation);
    }
    if (report) {
        printf("\nAll 18 declared finite correlations  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("Checked characters=%d; no prime cutoff or Euler product.\n",
               character_count);
        printf("Maximum fixture error = %.3Le.\n", maximum_error);
        printf("Classification  exhaustive finite numerical evidence.\n");
        printf("No limiting correlation or decay law is inferred.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    if (character_count_out) *character_count_out = character_count;
    if (maximum_error_out) *maximum_error_out = maximum_error;
    return failures;
}

int short_sum_bernoulli_correlation_ledger(void)
{
    return correlation_ledger_audit(1, NULL, NULL) == 0 ? 0 : 1;
}

int short_sum_bernoulli_correlation_moments(int base)
{
    CollisionMagnitudeMoments row = collision_magnitude_moments(base);
    if (row.count == 0) {
        fprintf(stderr, "Base must be an odd prime from 5 through 127.\n");
        return 1;
    }
    printf("Finite magnitude moments\n\n");
    printf("Base %d; primitive odd characters %d\n", base, row.count);
    printf("X = short-sum magnitude / sqrt(base); Y = L(1) magnitude.\n");
    printf("Both conjugates are counted. Y comes from the finite Bernoulli sum.\n\n");
    printf("mean X                 %.15Lf\n", row.mean_x);
    printf("mean Y                 %.15Lf\n", row.mean_y);
    printf("mean XY                %.15Lf\n", row.mean_xy);
    printf("mean X^2               %.15Lf\n", row.mean_x2);
    printf("mean Y^2               %.15Lf\n", row.mean_y2);
    printf("mean X^2 Y^2           %.15Lf\n", row.mean_x2y2);
    printf("mean X^(3/2)           %.15Lf\n", row.mean_x_three_halves);
    printf("mean Y^3               %.15Lf\n", row.mean_y3);
    printf("mean Y^4               %.15Lf\n", row.mean_y4);
    printf("mean chi(2)            %.15Lf %+.15Lfi\n",
           row.mean_chi2_real, row.mean_chi2_imag);
    printf("mean Y^2 chi(2)        %.15Lf %+.15Lfi\n",
           row.mean_y2_chi2_real, row.mean_y2_chi2_imag);
    printf("variance Y - nu/16     %.15Lf\n", row.variance_y_margin);
    printf("magnitude correlation %.15Lf\n", row.correlation);
    printf("mixed-square ratio    %.15Lf\n", row.enrichment);
    printf("maximum identity error %.3Le; tolerance 2.000e-12\n",
           row.max_identity_error);
    printf("8 real moment/twist targets, 2 integer doubling sums, 1 variance bound.\n");
    printf("Result  %s\n", row.failures ? "FAIL" : "PASS");
    printf("These finite checks do not establish an asymptotic limit.\n");
    return row.failures ? 1 : 0;
}

int short_sum_bernoulli_correlation_verify(void)
{
    int character_count = 0;
    long double maximum_error = 0.0L;
    int ok = correlation_ledger_audit(
        0, &character_count, &maximum_error) == 0;

    printf("Short-sum and Bernoulli correlation verification\n\n");
    printf("  all 18 declared base rows                       %s\n",
           ok ? "PASS" : "FAIL");
    printf("  checked characters=%d; expected=14372           %s\n",
           character_count,
           character_count == 14372 ? "PASS" : "FAIL");
    printf("  maximum twelve-decimal fixture error %.3Le     %s\n",
           maximum_error,
           maximum_error <= 5.0e-12L ? "PASS" : "FAIL");
    printf("\n3/3 verification groups %s.\n",
           ok && character_count == 14372 && maximum_error <= 5.0e-12L
               ? "passed" : "did not pass");
    printf("  144 moment and twist identity targets          %s\n", ok ? "PASS" : "FAIL");
    printf("  36 exact integer doubling-sum checks           %s\n", ok ? "PASS" : "FAIL");
    printf("  18 positive-variance lower bounds              %s\n", ok ? "PASS" : "FAIL");
    printf("Finite evidence  the ledger is exhaustive over the declared character\n");
    printf("families but proves no asymptotic correlation or decay law.\n");
    return ok && character_count == 14372 && maximum_error <= 5.0e-12L;
}

void short_sum_bernoulli_correlation_help(void)
{
    printf(
        "Short-sum and Bernoulli correlation\n\n"
        "Commands\n"
        "  nfield short-sum-bernoulli-correlation ledger\n"
        "      Reproduce all 18 correlations from finite Bernoulli sums.\n"
        "  nfield short-sum-bernoulli-correlation moments <base>\n"
        "      Inspect normalized moments, the twist at two and variance.\n"
        "      Any odd prime base from 5 through 127.\n"
        "  nfield short-sum-bernoulli-correlation verify\n"
        "  nfield verify short-sum-bernoulli-correlation\n\n"
        "Scope\n"
        "  finite exhaustive every primitive odd character for odd prime bases\n"
        "                    5 through 71, 14372 characters total.\n"
        "  L-value input     the finite Bernoulli sum; no Euler product, prime\n"
        "                    series, or approximation cutoff.\n"
        "  analytic scope    limiting correlation and decay require a proof;\n"
        "                    the finite checks do not establish those limits.\n"
    );
}
