/*
 * three_tier.c: Exact verification of the synchronized three-tier gap.
 *
 * The rough part may be composite.  Every score is computed on one common
 * denominator-n long-division clock of length ord_t(base).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "nfield.h"

typedef struct {
    int n;
    int base;
    int rough;
    int supported;
    int minimum_depth;
    int depth;
    int order;
    int terminating_expected;
    int terminating_observed;
    long long score_numerator;
    long long score_denominator;
} ThreeTierData;

static int tt_gcd(int a, int b)
{
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a < 0 ? -a : a;
}

static long long tt_gcdll(long long a, long long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = b;
        b = a % b;
        a = t;
    }
    return a == 0 ? 1 : a;
}

static void tt_reduce(long long *numerator, long long *denominator)
{
    long long g = tt_gcdll(*numerator, *denominator);
    *numerator /= g;
    *denominator /= g;
}

static void tt_print_fraction(long long numerator, long long denominator)
{
    tt_reduce(&numerator, &denominator);
    printf("%lld/%lld", numerator, denominator);
}

static int tt_supported_part(int n, int base, int *rough, int *supported)
{
    if (n < 1 || base < 2) return 0;
    int t = n;
    for (;;) {
        int g = tt_gcd(t, base);
        if (g == 1) break;
        t /= g;
    }
    *rough = t;
    *supported = n / t;
    return 1;
}

static int tt_clearing_depth(int supported, int base)
{
    int depth = 0;
    while (supported > 1) {
        int g = tt_gcd(supported, base);
        if (g == 1) return -1;
        supported /= g;
        depth++;
    }
    return depth;
}

static int tt_order(int base, int modulus)
{
    if (modulus == 1) return 0;
    if (modulus < 2 || tt_gcd(base, modulus) != 1) return -1;
    int value = base % modulus;
    int order = 1;
    while (value != 1 && order <= modulus) {
        value = (int)(((long long)value * base) % modulus);
        order++;
    }
    return value == 1 ? order : -1;
}

static int tt_fraction_terminates(int k, int n, int base)
{
    int reduced_denominator = n / tt_gcd(k, n);
    return is_b_smooth(reduced_denominator, base);
}

static int tt_row_matches(int k, const ThreeTierData *data)
{
    if (data->rough == 1 || k % data->rough == 0)
        return data->order;

    int reference = 1;
    int row = k;
    for (int i = 0; i < data->depth; i++) {
        reference = (int)(((long long)data->base * reference) % data->n);
        row = (int)(((long long)data->base * row) % data->n);
    }

    int matches = 0;
    for (int i = 0; i < data->order; i++) {
        int reference_digit =
            (int)(((long long)data->base * reference) / data->n);
        int row_digit = (int)(((long long)data->base * row) / data->n);
        if (reference_digit == row_digit) matches++;
        reference = (int)(((long long)data->base * reference) % data->n);
        row = (int)(((long long)data->base * row) % data->n);
    }
    return matches;
}

static int tt_build(int n, int base, int requested_depth, ThreeTierData *data)
{
    memset(data, 0, sizeof(*data));
    if (n < 2 || base < 2) return 0;

    int rough, supported;
    if (!tt_supported_part(n, base, &rough, &supported)) return 0;
    int minimum_depth = tt_clearing_depth(supported, base);
    int depth = requested_depth < 0 ? minimum_depth : requested_depth;
    if (minimum_depth < 0 || depth < minimum_depth) return 0;

    int order = tt_order(base, rough);
    if (rough > 1 && order <= 0) return 0;

    data->n = n;
    data->base = base;
    data->rough = rough;
    data->supported = supported;
    data->minimum_depth = minimum_depth;
    data->depth = depth;
    data->order = order;
    data->terminating_expected = supported - 1;

    if (rough == 1) {
        data->terminating_observed = n - 1;
        data->score_numerator = 1;
        data->score_denominator = 1;
        return 1;
    }

    long long score = 0;
    int terminating = 0;
    for (int k = 1; k < n; k++) {
        if (tt_fraction_terminates(k, n, base)) terminating++;
        score += tt_row_matches(k, data);
    }
    data->terminating_observed = terminating;
    data->score_numerator = score;
    data->score_denominator = (long long)order * (n - 1);
    return 1;
}

static const char *tt_tier(const ThreeTierData *data)
{
    if (data->rough == 1) return "I";
    if (data->rough == 3 && data->supported >= 4) return "II";
    return "III";
}

static int tt_in_theorem_domain(int base)
{
    return base >= 2 && base % 2 == 0 && base % 3 != 0;
}

static int tt_equal(long long an, long long ad, long long bn, long long bd)
{
    return an * bd == bn * ad;
}

static int tt_less(long long an, long long ad, long long bn, long long bd)
{
    return an * bd < bn * ad;
}

static int tt_less_equal(long long an, long long ad,
                         long long bn, long long bd)
{
    return an * bd <= bn * ad;
}

static void tt_print_pairs(const ThreeTierData *data)
{
    if (data->rough == 1) return;
    printf("\nComplement pairs (nonterminating rows):\n");
    printf("  k       n-k     score(k)  score(n-k)  pair total  <= 1\n");
    int shown = 0, total_pairs = 0;
    for (int k = 1; k < data->n; k++) {
        if (k % data->rough == 0) continue;
        int mate = data->n - k;
        if (k > mate) continue;
        int left = tt_row_matches(k, data);
        int right = tt_row_matches(mate, data);
        if (shown < 40) {
            printf("  %-7d %-7d %d/%-7d %d/%-10d %d/%-9d %s\n",
                   k, mate, left, data->order, right, data->order,
                   left + right, data->order,
                   left + right <= data->order ? "yes" : "NO");
            shown++;
        }
        total_pairs++;
    }
    if (shown < total_pairs)
        printf("  ... %d additional pairs omitted\n", total_pairs - shown);
}

int three_tier_inspect(int n, int base, int depth)
{
    if (n < 2) {
        fprintf(stderr, "n must be at least 2; alignment at n=1 is undefined\n");
        return 1;
    }
    if (base < 2) {
        fprintf(stderr, "base must be at least 2\n");
        return 1;
    }

    int rough, supported;
    tt_supported_part(n, base, &rough, &supported);
    int minimum_depth = tt_clearing_depth(supported, base);
    if (depth >= 0 && depth < minimum_depth) {
        fprintf(stderr, "depth %d is too early; use --depth %d or greater\n",
                depth, minimum_depth);
        return 1;
    }

    ThreeTierData data;
    if (!tt_build(n, base, depth, &data)) {
        fprintf(stderr, "could not construct synchronized alignment data\n");
        return 1;
    }

    printf("Three-Tier synchronized alignment inspection\n\n");
    printf("  n = %d\n  base = %d\n", n, base);
    printf("  canonical decomposition n = t*m = %d*%d\n",
           data.rough, data.supported);
    printf("  rough part t_b(n) = %d%s\n", data.rough,
           data.rough > 1 && data.rough != 3
               && data.rough != 5 && data.rough != 7 ? " (composite allowed)" : "");
    printf("  supported part s_b(n) = %d\n", data.supported);
    printf("  minimal clearing depth = %d\n", data.minimum_depth);
    printf("  chosen clearing depth D = %d\n", data.depth);
    printf("  common period L = ord_t(b) = %d\n", data.order);
    printf("  terminating fractions: observed %d, predicted s_b(n)-1 = %d  %s\n",
           data.terminating_observed, data.terminating_expected,
           data.terminating_observed == data.terminating_expected
               ? "PASS" : "FAIL");

    printf("\nExact alignment:\n  alpha_%d(%d) = ", base, n);
    tt_print_fraction(data.score_numerator, data.score_denominator);
    printf(" = %.12g\n",
           (double)data.score_numerator / data.score_denominator);

    double field = alignment_exact(n, base);
    double exact = (double)data.score_numerator / data.score_denominator;
    printf("  synchronized field measurement = %.12g\n", field);
    printf("  direct-clock comparison = %s\n",
           fabs(field - exact) < 1e-12 ? "PASS" : "FAIL");

    if (base % 2 == 0) {
        long long bound_num = (long long)data.supported
                            * (data.rough + 1) / 2 - 1;
        long long bound_den = n - 1;
        printf("\nEven-base complement bound:\n  finite bound = ");
        tt_print_fraction(bound_num, bound_den);
        printf("\n  rough-part ceiling = ");
        tt_print_fraction(data.rough + 1, 2LL * data.rough);
        printf("\n  exact alignment <= finite bound: %s\n",
               tt_less_equal(data.score_numerator, data.score_denominator,
                             bound_num, bound_den) ? "yes" : "NO");
    } else {
        printf("\nOdd-base status:\n");
        printf("  exact alignment was computed, but the even-base complement bound\n");
        printf("  does not apply because the middle digit is self-complementary.\n");
    }

    if (tt_in_theorem_domain(base)) {
        const char *tier = tt_tier(&data);
        printf("\nThree-Tier theorem status:\n");
        printf("  tier = %s\n", tier);
        if (strcmp(tier, "I") == 0)
            printf("  reason: n is entirely base-supported; alignment is one.\n");
        else if (strcmp(tier, "II") == 0)
            printf("  reason: rough part 3 with supported part m >= 4.\n");
        else
            printf("  reason: neither supported nor a three-core with m >= 4.\n");
        printf("  at or above reciprocal-golden threshold: %s\n",
               strcmp(tier, "III") == 0 ? "no" : "yes");
        printf("  lies in forbidden open interval (3/5, 7/11): %s\n",
               tt_less(3, 5, data.score_numerator, data.score_denominator)
               && tt_less(data.score_numerator, data.score_denominator, 7, 11)
                   ? "YES - FAILURE" : "no");
        if (tt_equal(data.score_numerator, data.score_denominator, 3, 5))
            printf("  endpoint: 3/5, uniquely attained at n=6  %s\n",
                   n == 6 ? "PASS" : "FAIL");
        if (tt_equal(data.score_numerator, data.score_denominator, 7, 11))
            printf("  endpoint: 7/11, uniquely attained at n=12  %s\n",
                   n == 12 ? "PASS" : "FAIL");
        printf("  exact separator proof: 3/5 < 1/phi uses 45 < 49;\n");
        printf("                         1/phi < 7/11 uses 225 < 245.\n");
    } else {
        printf("\nThree-Tier theorem status: not applicable.\n");
        if (base % 2 != 0)
            printf("  hypothesis failure: base %d is odd.\n", base);
        if (base % 3 == 0)
            printf("  hypothesis failure: base %d is divisible by 3.\n", base);
    }

    tt_print_pairs(&data);
    return fabs(field - exact) < 1e-12
        && data.terminating_observed == data.terminating_expected ? 0 : 1;
}

static int tt_validate_range(int maximum, int base)
{
    if (!tt_in_theorem_domain(base)) {
        fprintf(stderr,
                "the Three-Tier classification requires an even base not divisible by 3\n");
        return 0;
    }
    if (maximum < 2 || maximum > 2000) {
        fprintf(stderr, "maximum must be between 2 and 2000\n");
        return 0;
    }
    return 1;
}

int three_tier_classify(int maximum, int base)
{
    if (!tt_validate_range(maximum, base)) return 1;

    printf("Three-Tier classification through n=%d in base %d\n", maximum, base);
    printf("The reciprocal-golden decision is exact because 1/phi lies in (3/5,7/11).\n\n");
    printf("  n      t      m      exact alpha       tier   >=1/phi\n");
    for (int n = 2; n <= maximum; n++) {
        ThreeTierData data;
        if (!tt_build(n, base, -1, &data)) return 1;
        const char *tier = tt_tier(&data);
        long long an = data.score_numerator, ad = data.score_denominator;
        tt_reduce(&an, &ad);
        printf("  %-6d %-6d %-6d %lld/%-15lld %-6s %s\n",
               n, data.rough, data.supported, an, ad, tier,
               strcmp(tier, "III") == 0 ? "no" : "yes");
    }
    return 0;
}

static int tt_data_satisfies_tier(const ThreeTierData *data)
{
    const char *tier = tt_tier(data);
    long long an = data->score_numerator, ad = data->score_denominator;
    if (strcmp(tier, "I") == 0)
        return tt_equal(an, ad, 1, 1);
    if (strcmp(tier, "II") == 0)
        return tt_less_equal(7, 11, an, ad)
            && tt_less(an, ad, 2, 3)
            && (tt_equal(an, ad, 7, 11) == (data->n == 12));
    return tt_less_equal(an, ad, 3, 5)
        && (tt_equal(an, ad, 3, 5) == (data->n == 6));
}

int three_tier_scan(int maximum, int base)
{
    if (!tt_validate_range(maximum, base)) return 1;

    int gap_violations = 0;
    int classification_failures = 0;
    int lower_hits = 0, upper_hits = 0;
    int lower_n = 0, upper_n = 0;
    int tier_counts[3] = {0, 0, 0};

    for (int n = 2; n <= maximum; n++) {
        ThreeTierData data;
        if (!tt_build(n, base, -1, &data)) return 1;
        const char *tier = tt_tier(&data);
        if (strcmp(tier, "I") == 0) tier_counts[0]++;
        else if (strcmp(tier, "II") == 0) tier_counts[1]++;
        else tier_counts[2]++;

        long long an = data.score_numerator, ad = data.score_denominator;
        if (tt_less(3, 5, an, ad) && tt_less(an, ad, 7, 11))
            gap_violations++;
        if (tt_equal(an, ad, 3, 5)) { lower_hits++; lower_n = n; }
        if (tt_equal(an, ad, 7, 11)) { upper_hits++; upper_n = n; }
        if (!tt_data_satisfies_tier(&data)) classification_failures++;
    }

    int endpoints_ok = (maximum < 6 || (lower_hits == 1 && lower_n == 6))
                    && (maximum < 12 || (upper_hits == 1 && upper_n == 12));
    int ok = gap_violations == 0 && classification_failures == 0
          && endpoints_ok;

    printf("Exact Three-Tier scan: base %d, n=2..%d\n\n", base, maximum);
    printf("  Tier I count:   %d\n", tier_counts[0]);
    printf("  Tier II count:  %d\n", tier_counts[1]);
    printf("  Tier III count: %d\n", tier_counts[2]);
    printf("  forbidden interval violations: %d\n", gap_violations);
    printf("  classification failures: %d\n", classification_failures);
    if (maximum >= 6)
        printf("  3/5 endpoint hits: %d; unique n = %d\n", lower_hits, lower_n);
    if (maximum >= 12)
        printf("  7/11 endpoint hits: %d; unique n = %d\n", upper_hits, upper_n);
    printf("\nscan result: %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int tt_check_decomposition_and_termination(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int n = 2; n <= 240; n++) {
            ThreeTierData data;
            if (!tt_build(n, base, -1, &data)) return 0;
            if (data.n != data.rough * data.supported
                || tt_gcd(data.rough, base) != 1
                || !is_b_smooth(data.supported, base)
                || data.terminating_observed != data.supported - 1)
                return 0;

            for (int divisor = 1; divisor <= n; divisor++) {
                if (n % divisor != 0 || !is_b_smooth(divisor, base))
                    continue;
                if (divisor > data.supported
                    || data.supported % divisor != 0)
                    return 0;
                int cofactor = n / divisor;
                if (tt_gcd(cofactor, base) == 1
                    && (divisor != data.supported
                        || cofactor != data.rough))
                    return 0;
            }

            for (int k = 1; k < n; k++)
                if (tt_fraction_terminates(k, n, base)
                    != (k % data.rough == 0))
                    return 0;

            if (data.rough == 1
                && !tt_equal(data.score_numerator,
                             data.score_denominator, 1, 1))
                return 0;
        }
    }

    int rough = 0, supported = 0;
    if (!tt_supported_part(60, 10, &rough, &supported)
        || rough != 3 || supported != 20)
        return 0;
    if (!tt_supported_part(28, 10, &rough, &supported)
        || rough != 7 || supported != 4)
        return 0;
    return 1;
}

static int tt_check_clock_and_field(void)
{
    for (int base = 2; base <= 16; base++) {
        for (int n = 2; n <= 180; n++) {
            ThreeTierData first, next, later;
            if (!tt_build(n, base, -1, &first)) return 0;
            if (!tt_build(n, base, first.minimum_depth + 1, &next)
                || !tt_build(n, base, first.minimum_depth + 2, &later))
                return 0;
            if (!tt_equal(first.score_numerator, first.score_denominator,
                          next.score_numerator, next.score_denominator))
                return 0;
            if (!tt_equal(first.score_numerator, first.score_denominator,
                          later.score_numerator, later.score_denominator))
                return 0;

            for (int divisor = 2; divisor <= first.rough; divisor++) {
                if (first.rough % divisor != 0) continue;
                int reduced_order = tt_order(base, divisor);
                if (reduced_order <= 0
                    || first.order % reduced_order != 0)
                    return 0;
            }
            double exact = (double)first.score_numerator
                         / first.score_denominator;
            if (fabs(alignment_exact(n, base) - exact) > 1e-12) return 0;
        }
    }
    return 1;
}

static int tt_check_complement(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int n = 2; n <= 180; n++) {
            ThreeTierData data;
            if (!tt_build(n, base, -1, &data)) return 0;
            if (data.rough == 1) continue;

            int pair_count = 0;
            for (int k = 1; k < n; k++) {
                if (k % data.rough == 0) continue;
                int mate = n - k;
                if (tt_fraction_terminates(mate, n, base)) return 0;
                if (base % 2 == 0 && k == mate) return 0;
                if (k < mate) pair_count++;

                int reference_remainder = 1;
                int left_remainder = k;
                int right_remainder = mate;
                for (int i = 0; i < data.depth; i++) {
                    reference_remainder =
                        (int)(((long long)base * reference_remainder) % n);
                    left_remainder =
                        (int)(((long long)base * left_remainder) % n);
                    right_remainder =
                        (int)(((long long)base * right_remainder) % n);
                }
                for (int i = 0; i < data.order; i++) {
                    int reference_digit =
                        (int)(((long long)base * reference_remainder) / n);
                    int left_digit =
                        (int)(((long long)base * left_remainder) / n);
                    int right_digit =
                        (int)(((long long)base * right_remainder) / n);
                    if (left_digit + right_digit != base - 1) return 0;
                    if (base % 2 == 0
                        && left_digit == reference_digit
                        && right_digit == reference_digit)
                        return 0;
                    reference_remainder =
                        (int)(((long long)base * reference_remainder) % n);
                    left_remainder =
                        (int)(((long long)base * left_remainder) % n);
                    right_remainder =
                        (int)(((long long)base * right_remainder) % n);
                }
                if (base % 2 == 0
                    && tt_row_matches(k, &data)
                       + tt_row_matches(mate, &data) > data.order)
                    return 0;
            }
            if (base % 2 == 0
                && pair_count != (data.rough - 1) * data.supported / 2)
                return 0;
        }
    }
    return 1;
}

static int tt_check_upper_bound(void)
{
    for (int base = 2; base <= 20; base += 2) {
        for (int n = 2; n <= 240; n++) {
            ThreeTierData data;
            if (!tt_build(n, base, -1, &data)) return 0;
            long long bound_num =
                (long long)data.supported * (data.rough + 1) / 2 - 1;
            long long bound_den = n - 1;
            if (!tt_less_equal(data.score_numerator, data.score_denominator,
                               bound_num, bound_den))
                return 0;
            if (!tt_less_equal(bound_num, bound_den,
                               data.rough + 1, 2LL * data.rough))
                return 0;
            long long strict_difference =
                (long long)(data.rough + 1) * bound_den
                - 2LL * data.rough * bound_num;
            if (strict_difference != data.rough - 1) return 0;
            if (data.rough > 1
                && !tt_less(bound_num, bound_den,
                            data.rough + 1, 2LL * data.rough))
                return 0;
            if (data.rough >= 5
                && !tt_less_equal(data.rough + 1, 2LL * data.rough,
                                  3, 5))
                return 0;
        }
    }
    return 1;
}

static int tt_check_three_tier(void)
{
    for (int base = 2; base <= 20; base += 2) {
        if (base % 3 == 0) continue;
        int lower_hits = 0, upper_hits = 0;
        for (int n = 2; n <= 300; n++) {
            ThreeTierData data;
            if (!tt_build(n, base, -1, &data)) return 0;
            if (!tt_data_satisfies_tier(&data)) return 0;
            long long an = data.score_numerator, ad = data.score_denominator;
            if (tt_less(3, 5, an, ad) && tt_less(an, ad, 7, 11))
                return 0;
            if (tt_equal(an, ad, 3, 5)) {
                if (n != 6) return 0;
                lower_hits++;
            }
            if (tt_equal(an, ad, 7, 11)) {
                if (n != 12) return 0;
                upper_hits++;
            }
        }
        if (lower_hits != 1 || upper_hits != 1) return 0;
    }
    return 1;
}

static int tt_check_composite_rough_fixtures(void)
{
    int fixtures[] = {9, 21, 27, 63, 81, 99};
    for (int i = 0; i < 6; i++) {
        int n = fixtures[i];
        ThreeTierData data;
        if (!tt_build(n, 10, -1, &data)) return 0;
        if (data.rough != n || strcmp(tt_tier(&data), "III") != 0
            || !tt_less_equal(data.score_numerator,
                              data.score_denominator, 3, 5))
            return 0;
    }

    for (int n = 2; n <= 600; n++) {
        ThreeTierData data;
        if (!tt_build(n, 10, -1, &data)) return 0;
        if (data.rough != 1 && data.rough != 3) {
            if (data.rough < 7
                || !tt_less(data.score_numerator,
                            data.score_denominator, 4, 7))
                return 0;
        }
        if (data.rough == 3 && data.supported < 4
            && n != 3 && n != 6)
            return 0;
    }

    for (int m = 1; m <= 256; m++) {
        if (!is_b_smooth(m, 10)) continue;
        ThreeTierData seven_core;
        if (!tt_build(7 * m, 10, -1, &seven_core)) return 0;
        if (!tt_equal(seven_core.score_numerator,
                      seven_core.score_denominator,
                      2LL * m - 1, 7LL * m - 1))
            return 0;
        if (2LL * (7LL * m - 1) - 7LL * (2LL * m - 1) != 5)
            return 0;
        if (4LL * (7LL * m - 1) - 7LL * (4LL * m - 1) != 3)
            return 0;
    }
    return 1;
}

static int tt_check_endpoints_and_thresholds(void)
{
    if (!(45 < 49) || !(225 < 245)) return 0;
    for (int base = 2; base <= 20; base += 2) {
        if (base % 3 == 0) continue;
        ThreeTierData six, twelve;
        if (!tt_build(6, base, -1, &six)
            || !tt_build(12, base, -1, &twelve))
            return 0;
        if (!tt_equal(six.score_numerator, six.score_denominator, 3, 5)
            || !tt_equal(twelve.score_numerator,
                         twelve.score_denominator, 7, 11))
            return 0;

        for (int m = 1; m <= 64; m++) {
            if (!is_b_smooth(m, base)) continue;
            ThreeTierData data;
            if (!tt_build(3 * m, base, -1, &data)) return 0;
            if (!tt_equal(data.score_numerator, data.score_denominator,
                          2LL * m - 1, 3LL * m - 1))
                return 0;
            if (tt_less_equal(7, 11,
                              data.score_numerator,
                              data.score_denominator) != (m >= 4))
                return 0;
            if (!tt_less(data.score_numerator,
                         data.score_denominator, 2, 3))
                return 0;
            if (tt_equal(data.score_numerator,
                         data.score_denominator, 3, 5) != (m == 2))
                return 0;
            if (tt_equal(data.score_numerator,
                         data.score_denominator, 7, 11) != (m == 4))
                return 0;
        }
    }
    return 1;
}

static int tt_check_odd_base_obstructions(void)
{
    for (int base = 3; base <= 19; base += 2) {
        int middle = (base - 1) / 2;
        if (base - 1 - middle != middle) return 0;

        ThreeTierData fixed_point;
        if (!tt_build(2, base, -1, &fixed_point)) return 0;
        if (fixed_point.rough != 2 || fixed_point.supported != 1
            || tt_fraction_terminates(1, 2, base)
            || 2 - 1 != 1)
            return 0;

        for (int m = 1; m <= 64; m++) {
            if (!is_b_smooth(m, base)) continue;
            ThreeTierData two_core;
            if (!tt_build(2 * m, base, -1, &two_core)) return 0;
            if (two_core.rough != 2 || two_core.supported != m
                || !tt_equal(two_core.score_numerator,
                             two_core.score_denominator, 1, 1))
                return 0;
        }
    }
    return 1;
}

int three_tier_verify(void)
{
    printf("Exact three-tier gap verification\n");
    printf("Composite rough parts are evaluated on a common synchronized clock.\n\n");

    int passed = 0;
    int ok = tt_check_decomposition_and_termination();
    printf("  canonical maximal decomposition and termination iff: b<=20, n<=240       %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_clock_and_field();
    printf("  depth invariance, divisor periods, direct clock vs field: b<=16, n<=180    %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_complement();
    printf("  complement digits in every base and even-base pair inventory: n<=180      %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_upper_bound();
    printf("  finite bound, exact ceiling difference, and rough-core cap: n<=240         %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_three_tier();
    printf("  forbidden interval, tiers, and unique endpoints: admissible b<=20, n<=300 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_composite_rough_fixtures();
    printf("  decimal composite cores, four-sevenths cap, and seven-core family          %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_endpoints_and_thresholds();
    printf("  exact separators, endpoints, and three-core formula through m=64          %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = tt_check_odd_base_obstructions();
    printf("  odd-base middle digit, fixed point, and exact two-core family              %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/8 finite checks passed.\n", passed);
    printf("Finite verification is evidence, not the universal proof.\n");
    return passed == 8;
}

void three_tier_help(void)
{
    printf("Three-tier gap tools\n\n");
    printf("Domain of the classification: n >= 2 and an even base not divisible by 3.\n");
    printf("Every n is decomposed canonically as n=t*m, where m is the complete\n");
    printf("base-supported part and gcd(t,b)=1. The rough part t may be composite.\n\n");
    printf("Commands:\n");
    printf("  nfield three-tier inspect <n> [--base <b>] [--depth <D>]\n");
    printf("      Show the decomposition, common period, terminating count, exact\n");
    printf("      alignment, complement bound, tier, endpoint, and pair scores.\n\n");
    printf("  nfield three-tier classify <max> [--base <b>]\n");
    printf("      List the exact alignment and tier of every n from 2 through max.\n\n");
    printf("  nfield three-tier scan <max> [--base <b>]\n");
    printf("      Search the forbidden interval and audit unique endpoint attainment.\n\n");
    printf("  nfield three-tier verify\n");
    printf("  nfield verify three-tier\n");
    printf("      Run independent exact finite sweeps and print every range.\n\n");
    printf("Examples:\n");
    printf("  nfield three-tier inspect 6 --base 10\n");
    printf("  nfield three-tier inspect 12 --base 10\n");
    printf("  nfield three-tier inspect 21 --base 10\n");
    printf("  nfield three-tier scan 500 --base 10\n\n");
    printf("Exact separator: 3/5 < 1/phi < 7/11. Every threshold inside this open\n");
    printf("gap gives the same denominator classification.\n\n");
    printf("Odd bases are outside this theorem because the middle digit is its own\n");
    printf("complement and the two-core family has alignment one.\n\n");
    printf("Finite verification is evidence, not the universal proof.\n");
}
