/* Parseval moment identities for finite collision energy and L(1) values. */

#include <stdio.h>

#include "collision_spectrum_core.h"
#include "nfield.h"

enum { SPECIAL_VALUE_BASE_COUNT = 18 };

static const int special_value_bases[SPECIAL_VALUE_BASE_COUNT] = {
    5, 7, 11, 13, 17, 19, 23, 29, 31,
    37, 41, 43, 47, 53, 59, 61, 67, 71
};

static int special_value_moment_audit(int report,
                                      int *character_count_out,
                                      long double *maximum_error_out)
{
    int failures = 0;
    int character_count = 0;
    long double maximum_error = 0.0L;

    if (report) {
        printf("Exact special-value moment\n");
        printf("Finite Parseval ledger\n\n");
        printf("  b   chars    energy numerator/base^2   diagonal moment   error\n");
    }
    for (int index = 0; index < SPECIAL_VALUE_BASE_COUNT; index++) {
        CollisionSpectrumSummary summary;
        int base = special_value_bases[index];
        long long expected_diagonal =
            (long long)2 * base * (base - 1) * (base - 1);
        if (!collision_spectrum_base_audit(base, &summary)) {
            failures++;
            continue;
        }
        character_count += summary.primitive_odd_count;
        if (summary.special_value_moment_error > maximum_error)
            maximum_error = summary.special_value_moment_error;
        if (summary.diagonal_second_moment_error > 2.0e-12L ||
            summary.special_value_moment_error > 2.0e-12L)
            failures++;
        if (report)
            printf(" %2d  %6d   %lld/%d              %.0Lf/%lld      %.3Le\n",
                   base, summary.primitive_odd_count,
                   (long long)summary.energy_numerator, base * base,
                   summary.diagonal_second_moment, expected_diagonal,
                   summary.special_value_moment_error);
    }
    if (report) {
        printf("\nEvery diagonal second moment equals 2b(b-1)^2  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("Every weighted L(1) moment equals the collision-energy side  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("Maximum relative special-value moment error = %.3Le.\n",
               maximum_error);
        printf("Classification  finite complex evaluation of an exact Parseval identity.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    if (character_count_out) *character_count_out = character_count;
    if (maximum_error_out) *maximum_error_out = maximum_error;
    return failures;
}

int special_value_moment_ledger(void)
{
    return special_value_moment_audit(1, NULL, NULL) == 0 ? 0 : 1;
}

int special_value_moment_verify(void)
{
    int character_count = 0;
    long double maximum_error = 0.0L;
    int ok = special_value_moment_audit(
        0, &character_count, &maximum_error) == 0;

    printf("Exact special-value moment verification\n\n");
    printf("  all 18 diagonal second-moment identities        %s\n",
           ok ? "PASS" : "FAIL");
    printf("  all 18 weighted L(1) Parseval identities        %s\n",
           ok ? "PASS" : "FAIL");
    printf("  checked characters=%d; expected=14372            %s\n",
           character_count,
           character_count == 14372 ? "PASS" : "FAIL");
    printf("  maximum relative moment error %.3Le             %s\n",
           maximum_error,
           maximum_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("\n4/4 verification groups %s.\n",
           ok && character_count == 14372 &&
           maximum_error <= 2.0e-12L ? "passed" : "did not pass");
    printf("Identity  the weighted special-value moment follows exactly from\n");
    printf("Parseval and the Bernoulli-diagonal coefficient factorization.\n");
    printf("Finite boundary  the verifier checks all declared character families.\n");
    return ok && character_count == 14372 &&
           maximum_error <= 2.0e-12L;
}

void special_value_moment_help(void)
{
    printf(
        "Exact special-value moment\n\n"
        "Commands\n"
        "  nfield special-value-moment ledger\n"
        "      Show collision energy, the diagonal second moment, and the\n"
        "      weighted L(1) Parseval error for 18 prime bases.\n"
        "  nfield special-value-moment verify\n"
        "  nfield verify special-value-moment\n\n"
        "Scope\n"
        "  exact identity     Parseval relation between centered collision energy\n"
        "                     and the weighted L(1) second moment.\n"
        "  finite exhaustive 14372 primitive odd characters, bases 5 through 71.\n"
        "  numerical method  long-double roots of unity; exact table inputs and\n"
        "                     closed-form moment targets.\n"
        "  open               no asymptotic moment or zero-location claim.\n"
    );
}
