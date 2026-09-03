/* Finite natural-prime sums over centered lag-one collision tables. */

#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "finite_character_core.h"
#include "nfield.h"

enum {
    NATURAL_SUM_BASE_COUNT = 10,
    NATURAL_SUM_CUTOFF_COUNT = 5
};

static const int natural_sum_bases[NATURAL_SUM_BASE_COUNT] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31
};

static const int natural_sum_cutoffs[NATURAL_SUM_CUTOFF_COUNT] = {
    250000, 500000, 1000000, 2000000, 5000000
};

static void compensated_add(long double term, long double *sum,
                            long double *correction)
{
    long double adjusted = term - *correction;
    long double updated = *sum + adjusted;
    *correction = (updated - *sum) - adjusted;
    *sum = updated;
}

static int build_lag_one_tables(CollisionCenteredTable *tables)
{
    int built = 0;
    for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
         base_index++) {
        if (!collision_centered_table_build(
                natural_sum_bases[base_index], 1, &tables[base_index])) {
            for (int index = 0; index < built; index++)
                collision_centered_table_free(&tables[index]);
            return 0;
        }
        built++;
    }
    return 1;
}

static void free_lag_one_tables(CollisionCenteredTable *tables)
{
    for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
         base_index++)
        collision_centered_table_free(&tables[base_index]);
}

static int base_boundary_audit(const int *primes, int prime_count,
                               const int *cutoffs, int cutoff_count,
                               int report, int *positive_count)
{
    CollisionCenteredTable tables[NATURAL_SUM_BASE_COUNT] = {{0}};
    long double forward[NATURAL_SUM_CUTOFF_COUNT]
                       [NATURAL_SUM_BASE_COUNT] = {{0}};
    long double correction[NATURAL_SUM_CUTOFF_COUNT]
                          [NATURAL_SUM_BASE_COUNT] = {{0}};
    long double reverse[NATURAL_SUM_CUTOFF_COUNT]
                       [NATURAL_SUM_BASE_COUNT] = {{0}};
    long double reverse_correction[NATURAL_SUM_CUTOFF_COUNT]
                                   [NATURAL_SUM_BASE_COUNT] = {{0}};
    long double absolute_mass[NATURAL_SUM_CUTOFF_COUNT]
                             [NATURAL_SUM_BASE_COUNT] = {{0}};
    int counts[NATURAL_SUM_CUTOFF_COUNT][NATURAL_SUM_BASE_COUNT] = {{0}};
    int failures = 0;
    int positives = 0;

    if (!primes || !cutoffs || cutoff_count < 1 ||
        cutoff_count > NATURAL_SUM_CUTOFF_COUNT ||
        !build_lag_one_tables(tables))
        return 1;
    for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
         base_index++)
        failures += centered_collision_table_audit(
            &tables[base_index], NULL, NULL);

    for (int prime_index = 0; prime_index < prime_count; prime_index++) {
        int prime = primes[prime_index];
        for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
             base_index++) {
            long double term;
            if (prime <= tables[base_index].modulus) continue;
            term = centered_collision_value(
                       &tables[base_index],
                       prime % tables[base_index].modulus) /
                   sqrtl((long double)prime);
            for (int cutoff_index = 0; cutoff_index < cutoff_count;
                 cutoff_index++) {
                if (prime >= cutoffs[cutoff_index]) continue;
                compensated_add(term, &forward[cutoff_index][base_index],
                                &correction[cutoff_index][base_index]);
                absolute_mass[cutoff_index][base_index] += fabsl(term);
                counts[cutoff_index][base_index]++;
            }
        }
    }
    for (int prime_index = prime_count - 1; prime_index >= 0;
         prime_index--) {
        int prime = primes[prime_index];
        for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
             base_index++) {
            long double term;
            if (prime <= tables[base_index].modulus) continue;
            term = centered_collision_value(
                       &tables[base_index],
                       prime % tables[base_index].modulus) /
                   sqrtl((long double)prime);
            for (int cutoff_index = 0; cutoff_index < cutoff_count;
                 cutoff_index++) {
                if (prime >= cutoffs[cutoff_index]) continue;
                compensated_add(
                    term, &reverse[cutoff_index][base_index],
                    &reverse_correction[cutoff_index][base_index]);
            }
        }
    }

    if (report) {
        printf("Natural prime-sum window\n");
        printf("Base-specific lower boundaries\n\n");
        printf("Each base uses its own exact lower boundary b^2 < p < X.\n");
        printf("Exponent sigma=1/2; these are finite partial sums.\n\n");
    }
    for (int cutoff_index = 0; cutoff_index < cutoff_count;
         cutoff_index++) {
        long double weighted = 0.0L;
        long double weighted_l1 = 0.0L;
        if (report) printf("cutoff X=%d\n", cutoffs[cutoff_index]);
        for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
             base_index++) {
            long double difference = fabsl(
                forward[cutoff_index][base_index] -
                reverse[cutoff_index][base_index]);
            long double guard = 1024.0L * LDBL_EPSILON *
                (counts[cutoff_index][base_index] + 2.0L) *
                (1.0L + absolute_mass[cutoff_index][base_index]);
            int order_stable = difference <= guard;
            long double contribution =
                forward[cutoff_index][base_index] /
                ((long double)natural_sum_bases[base_index] *
                 natural_sum_bases[base_index]);
            if (!order_stable) failures++;
            if (forward[cutoff_index][base_index] > guard) positives++;
            weighted += contribution;
            weighted_l1 += fabsl(contribution);
            if (report)
                printf("  b=%-2d lower=%-3d primes=%-6d value=%+.12Lf"
                       "  order_error=%.2Le  %s\n",
                       natural_sum_bases[base_index],
                       tables[base_index].modulus,
                       counts[cutoff_index][base_index],
                       forward[cutoff_index][base_index], difference,
                       order_stable ? "STABLE" : "FAIL");
        }
        if (report) {
            printf("  weighted sum with 1/b^2 = %+.12Lf\n", weighted);
            printf("  cancellation ratio = %.9Lf\n\n",
                   weighted_l1 > 0.0L
                       ? fabsl(weighted) / weighted_l1 : 0.0L);
        }
    }
    if (cutoff_count == NATURAL_SUM_CUTOFF_COUNT &&
        memcmp(cutoffs, natural_sum_cutoffs,
               sizeof(natural_sum_cutoffs)) == 0 &&
        positives != 50)
        failures++;
    if (report) {
        printf("Positive values in this requested finite ledger: %d/%d.\n",
               positives, cutoff_count * NATURAL_SUM_BASE_COUNT);
        if (cutoff_count == NATURAL_SUM_CUTOFF_COUNT &&
            memcmp(cutoffs, natural_sum_cutoffs,
                   sizeof(natural_sum_cutoffs)) == 0)
            printf("All fifty declared natural-sum signs  %s\n",
                   positives == 50 && failures == 0 ? "PASS" : "FAIL");
        printf("Classification  finite numerical evidence, not positivity or convergence.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    if (positive_count) *positive_count = positives;
    free_lag_one_tables(tables);
    return failures;
}

int natural_prime_sum_window_base_boundaries(int cutoff)
{
    int custom_cutoff[1];
    const int *cutoffs = natural_sum_cutoffs;
    int cutoff_count = NATURAL_SUM_CUTOFF_COUNT;
    int maximum_cutoff = FINITE_CHARACTER_MAX_CUTOFF;
    int *primes;
    int prime_count = 0;
    int failures;

    if (cutoff != 0) {
        if (cutoff <= 961 || cutoff > FINITE_CHARACTER_MAX_CUTOFF) {
            fprintf(stderr, "cutoff must satisfy 961 < cutoff <= %d\n",
                    FINITE_CHARACTER_MAX_CUTOFF);
            return 1;
        }
        custom_cutoff[0] = cutoff;
        cutoffs = custom_cutoff;
        cutoff_count = 1;
        maximum_cutoff = cutoff;
    }
    primes = finite_character_primes(maximum_cutoff, &prime_count);
    if (!primes) {
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures = base_boundary_audit(
        primes, prime_count, cutoffs, cutoff_count, 1, NULL);
    free(primes);
    return failures == 0 ? 0 : 1;
}

static int common_tail_audit(const int *primes, int prime_count,
                             int lower, int cutoff, int report,
                             int *positive_count, int *negative_count)
{
    CollisionCenteredTable tables[NATURAL_SUM_BASE_COUNT] = {{0}};
    long double sum[NATURAL_SUM_BASE_COUNT] = {0};
    long double correction[NATURAL_SUM_BASE_COUNT] = {0};
    long double direct = 0.0L, direct_correction = 0.0L;
    int count = 0, positives = 0, negatives = 0;
    int failures = 0;

    if (!build_lag_one_tables(tables)) return 1;
    for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
         base_index++)
        failures += centered_collision_table_audit(
            &tables[base_index], NULL, NULL);
    for (int prime_index = 0; prime_index < prime_count; prime_index++) {
        int prime = primes[prime_index];
        long double combined = 0.0L;
        if (prime <= lower || prime >= cutoff) continue;
        count++;
        for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
             base_index++) {
            long double value = centered_collision_value(
                &tables[base_index],
                prime % tables[base_index].modulus) /
                sqrtl((long double)prime);
            compensated_add(value, &sum[base_index],
                            &correction[base_index]);
            combined += value /
                ((long double)natural_sum_bases[base_index] *
                 natural_sum_bases[base_index]);
        }
        compensated_add(combined, &direct, &direct_correction);
    }
    if (report) {
        printf("Natural prime-sum window\n");
        printf("Common tail across ten bases\n\n");
        printf("Finite interval %d < p < %d; sigma=1/2.\n", lower, cutoff);
        printf("The default lower boundary removes the initial segment through 997.\n\n");
    }
    {
        long double weighted = 0.0L;
        for (int base_index = 0; base_index < NATURAL_SUM_BASE_COUNT;
             base_index++) {
            if (sum[base_index] > 0.0L) positives++;
            else if (sum[base_index] < 0.0L) negatives++;
            weighted += sum[base_index] /
                ((long double)natural_sum_bases[base_index] *
                 natural_sum_bases[base_index]);
            if (report)
                printf("  b=%-2d value=%+.12Lf sign=%s\n",
                       natural_sum_bases[base_index], sum[base_index],
                       sum[base_index] > 0.0L ? "positive" :
                       sum[base_index] < 0.0L ? "negative" : "zero");
        }
        if (fabsl(weighted - direct) >
            1.0e-12L * (1.0L + fabsl(direct)))
            failures++;
        if (lower == 997 && cutoff == 2000000 &&
            (positives != 3 || negatives != 7))
            failures++;
        if (report) {
            printf("\n  primes=%d; positive bases=%d; negative bases=%d\n",
                   count, positives, negatives);
            printf("  weighted sum by separate bases = %+.12Lf\n", weighted);
            printf("  direct weighted readout = %+.12Lf\n", direct);
            printf("  weighted identity error = %.3Le  %s\n",
                   weighted - direct, failures == 0 ? "PASS" : "FAIL");
            printf("\nClassification  finite numerical evidence. Mixed signs in this\n");
            printf("tail do not assert cancellation of an infinite prime sum.\n");
            printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
        }
    }
    if (positive_count) *positive_count = positives;
    if (negative_count) *negative_count = negatives;
    free_lag_one_tables(tables);
    return failures;
}

int natural_prime_sum_window_common_tail(int lower, int cutoff)
{
    int *primes;
    int prime_count = 0;
    int failures;

    if (lower < 961 || cutoff <= lower ||
        cutoff > FINITE_CHARACTER_MAX_CUTOFF) {
        fprintf(stderr, "window must satisfy 961 <= lower < cutoff <= %d\n",
                FINITE_CHARACTER_MAX_CUTOFF);
        return 1;
    }
    primes = finite_character_primes(cutoff, &prime_count);
    if (!primes) {
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures = common_tail_audit(
        primes, prime_count, lower, cutoff, 1, NULL, NULL);
    free(primes);
    return failures == 0 ? 0 : 1;
}

int natural_prime_sum_window_verify(void)
{
    int *primes;
    int prime_count = 0;
    int natural_positive = 0;
    int tail_positive = 0, tail_negative = 0;
    int natural_ok, tail_ok;
    int passed = 0;

    printf("Natural prime-sum window verification\n\n");
    primes = finite_character_primes(
        FINITE_CHARACTER_MAX_CUTOFF, &prime_count);
    if (!primes) {
        printf("unable to allocate the prime sieve\n");
        return 0;
    }
    natural_ok = base_boundary_audit(
        primes, prime_count, natural_sum_cutoffs,
        NATURAL_SUM_CUTOFF_COUNT, 0, &natural_positive) == 0;
    tail_ok = common_tail_audit(
        primes, prime_count, 997, 2000000, 0,
        &tail_positive, &tail_negative) == 0;
    free(primes);

    printf("  all fifty declared base-boundary sums are positive  %s\n",
           natural_ok && natural_positive == 50 ? "PASS" : "FAIL");
    if (natural_ok && natural_positive == 50) passed++;
    printf("  common tail has three positive and seven negative   %s\n",
           tail_ok && tail_positive == 3 && tail_negative == 7
               ? "PASS" : "FAIL");
    if (tail_ok && tail_positive == 3 && tail_negative == 7) passed++;
    printf("  weighted direct/separate-base identity               %s\n",
           tail_ok ? "PASS" : "FAIL");
    if (tail_ok) passed++;
    printf("\n%d/3 verification groups passed.\n", passed);
    printf("Classification  finite numerical evidence only.\n");
    printf("Boundary  positivity and convergence of infinite prime sums remain open.\n");
    return passed == 3;
}

void natural_prime_sum_window_help(void)
{
    printf(
        "Natural prime-sum window\n\n"
        "Commands\n"
        "  nfield natural-prime-sum-window base-boundaries [--cutoff <X>]\n"
        "      Use each base's exact lower boundary b^2. Without an option,\n"
        "      reproduce all fifty values at five declared cutoffs.\n"
        "  nfield natural-prime-sum-window common-tail [--lower <L>] [--cutoff <X>]\n"
        "      Compare ten base contributions on one finite tail. Defaults are\n"
        "      L=997 and X=2000000.\n"
        "  nfield natural-prime-sum-window verify\n"
        "  nfield verify natural-prime-sum-window\n\n"
        "Scope\n"
        "  exact input       Centered lag-one collision tables.\n"
        "  finite evidence   Compensated long-double sums over printed windows.\n"
        "  stability check   Forward/reverse order and direct/decomposed sums.\n"
        "  open              Positivity and convergence at infinite cutoff.\n"
    );
}
