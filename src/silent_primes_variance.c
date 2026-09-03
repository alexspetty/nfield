/*
 * silent_primes_variance.c
 *
 * Finite silence and collision-variance arithmetic.
 *
 * The collision, recipe, mean, and variance arithmetic is exact. Printed
 * decimals are views of exact rational values. The variance limit remains
 * open.
 */

#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#define SPV_MAX_BASE 64
#define SPV_MAX_PRIME 20000
#define SPV_MAX_RECIPE_VALUE 2147483647ULL

typedef struct {
    uint64_t numerator;
    uint64_t denominator;
    long double value;
    uint64_t raw_numerator;
    uint64_t raw_denominator;
    uint64_t diagonal_numerator;
    int64_t off_diagonal_numerator;
    uint64_t sum_collisions;
    uint64_t sum_collision_squares;
    uint64_t sum_failures;
    uint64_t sum_failure_squares;
    int q;
    int remainder;
    int population;
} SPVVariance;

typedef struct {
    int p;
    int exponent;
    int residue;
    int next_residue;
    int common_digit;
} SPVOrbitWitness;

static const SPVOrbitWitness spv_decimal_witnesses[] = {
    {17, 2, 15, 14, 8}, {29, 2, 13, 14, 4},
    {31, 2, 7, 8, 2},   {43, 4, 24, 25, 5},
    {47, 10, 21, 22, 4}, {53, 2, 47, 46, 8},
    {59, 15, 52, 48, 8}, {61, 6, 27, 26, 4},
    {67, 22, 37, 35, 5}, {71, 11, 16, 18, 2},
    {79, 6, 18, 22, 2},  {83, 9, 64, 59, 7},
    {89, 1, 10, 11, 1},  {97, 24, 75, 71, 7}
};

static const int spv_decimal_silent[] = {11, 13, 19, 23, 37, 41, 73};

static int spv_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static uint64_t spv_gcd_u64(uint64_t a, uint64_t b)
{
    while (b != 0) {
        uint64_t next = a % b;
        a = b;
        b = next;
    }
    return a;
}

static int spv_mod_pow(int base, int exponent, int modulus)
{
    int64_t result = 1;
    int64_t power = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int spv_mod_inverse(int value, int p)
{
    return spv_mod_pow(value, p - 2, p);
}

static int spv_digit(int residue, int p, int base)
{
    return (int)((int64_t)base * residue / p);
}

static int spv_validate_base_prime(int p, int base, int constructive,
                                   int report)
{
    if (base < 2 || base > SPV_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n", SPV_MAX_BASE);
        return 0;
    }
    if (!spv_is_prime(p)) {
        if (report) fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (p <= base + constructive) {
        if (report) {
            if (constructive)
                fprintf(stderr, "variance requires p > base + 1\n");
            else
                fprintf(stderr, "silent-prime arithmetic requires p > base\n");
        }
        return 0;
    }
    if (p > SPV_MAX_PRIME) {
        if (report)
            fprintf(stderr, "p must not exceed %d in this finite implementation\n",
                    SPV_MAX_PRIME);
        return 0;
    }
    return 1;
}

static int spv_collision_direct_unchecked(int p, int base, int multiplier)
{
    int count = 0;
    for (int r = 1; r < p; r++) {
        int image = (int)((int64_t)multiplier * r % p);
        count += spv_digit(r, p, base) == spv_digit(image, p, base);
    }
    return count;
}

int silent_primes_collision_count(int p, int base, int multiplier, int *count)
{
    if (!count || !spv_validate_base_prime(p, base, 0, 0) ||
        multiplier <= 0 || multiplier >= p)
        return 0;
    *count = spv_collision_direct_unchecked(p, base, multiplier);
    return 1;
}

static int spv_collision_coordinate_count(int c, int p, int base)
{
    int q = (p - 1) / base;
    int count = 0;
    for (int m = 1; m <= q; m++)
        count += 2 * ((int)((int64_t)m * c % p) > m * base);
    return count;
}

static int spv_coordinate_multiplier(int c, int p, int base)
{
    int term = (int)((int64_t)base * spv_mod_inverse(c, p) % p);
    int multiplier = 1 - term;
    if (multiplier < 0) multiplier += p;
    return multiplier;
}

static int spv_multiplier_coordinate(int multiplier, int p, int base)
{
    int denominator = 1 - multiplier;
    denominator %= p;
    if (denominator < 0) denominator += p;
    return (int)((int64_t)base * spv_mod_inverse(denominator, p) % p);
}

static int spv_repetend_unchecked(int p, int base, int lag)
{
    int multiplier = spv_mod_pow(base, lag, p);
    int residue = 1;
    int matches = 0;
    do {
        int image = (int)((int64_t)multiplier * residue % p);
        matches += spv_digit(residue, p, base) ==
                   spv_digit(image, p, base);
        residue = (int)((int64_t)base * residue % p);
    } while (residue != 1);
    return matches;
}

int silent_primes_repetend_count(int p, int base, int lag, int *count)
{
    if (!count || !spv_validate_base_prime(p, base, 0, 0) || lag < 1)
        return 0;
    *count = spv_repetend_unchecked(p, base, lag);
    return 1;
}

static int spv_recipe_match_unchecked(int p, int base, int lag, int *u_out)
{
    int b_lag = spv_mod_pow(base, lag, p);
    int b_next = (int)((int64_t)b_lag * base % p);
    for (int u = 1; u < base; u++) {
        int value = b_next - (int)((int64_t)u * (b_lag - 1) % p);
        value %= p;
        if (value < 0) value += p;
        if (value == 0) {
            if (u_out) *u_out = u;
            return 1;
        }
    }
    if (u_out) *u_out = 0;
    return 0;
}

int silent_primes_global_recipe_match(int p, int base, int lag, int *match)
{
    if (!match || !spv_validate_base_prime(p, base, 0, 0) || lag < 1)
        return 0;
    *match = spv_recipe_match_unchecked(p, base, lag, NULL);
    return 1;
}

static int spv_power_for_recipe(int base, int lag, uint64_t *power)
{
    if (base < 2 || base > SPV_MAX_BASE || lag < 1) return 0;
    uint64_t value = 1;
    for (int i = 0; i < lag + 1; i++) {
        if (value > SPV_MAX_RECIPE_VALUE / (uint64_t)base) return 0;
        value *= (uint64_t)base;
    }
    *power = value;
    return 1;
}

static int spv_compare_int(const void *left, const void *right)
{
    int a = *(const int *)left;
    int b = *(const int *)right;
    return (a > b) - (a < b);
}

static void spv_add_unique(int *values, int *count, int capacity, int value)
{
    for (int i = 0; i < *count; i++)
        if (values[i] == value) return;
    if (*count < capacity) values[(*count)++] = value;
}

static void spv_collect_large_prime_factors(uint64_t value, int base,
                                            int *values, int *count,
                                            int capacity)
{
    uint64_t remaining = value;
    for (uint64_t factor = 2; factor <= remaining / factor; factor++) {
        if (remaining % factor != 0) continue;
        if (factor > (uint64_t)base)
            spv_add_unique(values, count, capacity, (int)factor);
        while (remaining % factor == 0) remaining /= factor;
    }
    if (remaining > 1 && remaining > (uint64_t)base)
        spv_add_unique(values, count, capacity, (int)remaining);
}

static void spv_print_factorization(uint64_t value)
{
    uint64_t remaining = value;
    int first = 1;
    for (uint64_t factor = 2; factor <= remaining / factor; factor++) {
        if (remaining % factor != 0) continue;
        int exponent = 0;
        while (remaining % factor == 0) {
            remaining /= factor;
            exponent++;
        }
        printf("%s%llu", first ? "" : " * ",
               (unsigned long long)factor);
        if (exponent > 1) printf("^%d", exponent);
        first = 0;
    }
    if (remaining > 1 || first)
        printf("%s%llu", first ? "" : " * ",
               (unsigned long long)remaining);
}

static int spv_compute_variance(int p, int base, SPVVariance *result,
                                int check_coordinate)
{
    if (!result || !spv_validate_base_prime(p, base, 1, 0)) return 0;
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    int population = p - base - 1;
    uint64_t sum_c = 0;
    uint64_t sum_c2 = 0;
    uint64_t sum_y = 0;
    uint64_t sum_y2 = 0;

    for (int c = base + 1; c < p; c++) {
        int collision = spv_collision_coordinate_count(c, p, base);
        if (check_coordinate) {
            int multiplier = spv_coordinate_multiplier(c, p, base);
            if (spv_collision_direct_unchecked(p, base, multiplier) != collision)
                return 0;
        }
        int failures = q - collision / 2;
        sum_c += (uint64_t)collision;
        sum_c2 += (uint64_t)collision * (uint64_t)collision;
        sum_y += (uint64_t)failures;
        sum_y2 += (uint64_t)failures * (uint64_t)failures;
    }

    uint64_t raw_numerator = (uint64_t)population * sum_c2 - sum_c * sum_c;
    uint64_t raw_denominator = (uint64_t)population * (uint64_t)population;
    uint64_t ledger_numerator =
        4ULL * ((uint64_t)population * sum_y2 - sum_y * sum_y);
    if (ledger_numerator != raw_numerator) return 0;

    uint64_t diagonal_first =
        (uint64_t)base * (uint64_t)q * (uint64_t)(q - 1) *
        (uint64_t)population / 2ULL;
    uint64_t diagonal_second =
        (uint64_t)base * (uint64_t)base * (uint64_t)q *
        (uint64_t)(q - 1) * (uint64_t)(2 * q - 1) / 6ULL;
    uint64_t diagonal_numerator = 4ULL * (diagonal_first - diagonal_second);
    int64_t off_diagonal_numerator =
        (int64_t)raw_numerator - (int64_t)diagonal_numerator;
    uint64_t divisor = spv_gcd_u64(raw_numerator, raw_denominator);

    result->numerator = raw_numerator / divisor;
    result->denominator = raw_denominator / divisor;
    result->value = (long double)raw_numerator / (long double)raw_denominator;
    result->raw_numerator = raw_numerator;
    result->raw_denominator = raw_denominator;
    result->diagonal_numerator = diagonal_numerator;
    result->off_diagonal_numerator = off_diagonal_numerator;
    result->sum_collisions = sum_c;
    result->sum_collision_squares = sum_c2;
    result->sum_failures = sum_y;
    result->sum_failure_squares = sum_y2;
    result->q = q;
    result->remainder = remainder;
    result->population = population;
    return 1;
}

int silent_primes_variance_fraction(int p, int base,
                                    unsigned long long *mean_numerator,
                                    unsigned long long *mean_denominator,
                                    unsigned long long *variance_numerator,
                                    unsigned long long *variance_denominator)
{
    if (!mean_numerator || !mean_denominator || !variance_numerator ||
        !variance_denominator)
        return 0;
    SPVVariance variance;
    if (!spv_compute_variance(p, base, &variance, 0)) return 0;
    uint64_t mean_num = (uint64_t)variance.q *
        (uint64_t)(base * (variance.q - 1) + 2 * variance.remainder);
    uint64_t mean_den = (uint64_t)variance.population;
    uint64_t divisor = spv_gcd_u64(mean_num, mean_den);
    *mean_numerator = mean_num / divisor;
    *mean_denominator = mean_den / divisor;
    *variance_numerator = variance.numerator;
    *variance_denominator = variance.denominator;
    return 1;
}

static int spv_signed_fraction(int64_t numerator, uint64_t denominator,
                               int64_t *reduced_numerator,
                               uint64_t *reduced_denominator)
{
    uint64_t magnitude = numerator < 0 ? (uint64_t)(-numerator) :
                                         (uint64_t)numerator;
    uint64_t divisor = spv_gcd_u64(magnitude, denominator);
    *reduced_numerator = numerator / (int64_t)divisor;
    *reduced_denominator = denominator / divisor;
    return 1;
}

int silent_primes_recipe(int base, int lag)
{
    uint64_t next_power = 0;
    if (!spv_power_for_recipe(base, lag, &next_power)) {
        fprintf(stderr,
                "recipe requires 2 <= base <= %d, lag >= 1, and "
                "base^(lag+1) <= %llu\n",
                SPV_MAX_BASE, (unsigned long long)SPV_MAX_RECIPE_VALUE);
        return 1;
    }
    uint64_t b_lag = next_power / (uint64_t)base;
    uint64_t step = b_lag - 1;
    int primes[SPV_MAX_BASE * 8];
    int prime_count = 0;

    printf("Finite silence and collision-variance arithmetic\n");
    printf("Exact global-silence recipe\n\n");
    printf("base b = %d; lag ell = %d\n", base, lag);
    printf("N_b,ell(u) = b^(ell+1) - u(b^ell-1)\n");
    printf("progression first term = %llu; common difference = -%llu\n\n",
           (unsigned long long)(b_lag * (uint64_t)(base - 1) + 1),
           (unsigned long long)step);
    printf("  u       N_b,ell(u)       factorization\n");
    for (int u = 1; u < base; u++) {
        uint64_t value = next_power - (uint64_t)u * step;
        printf("  %-7d %-16llu ", u, (unsigned long long)value);
        spv_print_factorization(value);
        printf("\n");
        spv_collect_large_prime_factors(value, base, primes, &prime_count,
                                        (int)(sizeof(primes) / sizeof(primes[0])));
    }
    qsort(primes, (size_t)prime_count, sizeof(primes[0]), spv_compare_int);
    printf("\nprime divisors p>b = {");
    for (int i = 0; i < prime_count; i++)
        printf("%s%d", i ? "," : "", primes[i]);
    printf("}\n");

    int pass = 1;
    for (int i = 0; i < prime_count; i++) {
        int multiplier = spv_mod_pow(base, lag, primes[i]);
        int collision = spv_collision_direct_unchecked(primes[i], base,
                                                       multiplier);
        if (collision != 0 ||
            !spv_recipe_match_unchecked(primes[i], base, lag, NULL))
            pass = 0;
    }
    printf("every listed prime is globally silent by direct collision count  %s\n",
           pass ? "PASS" : "FAIL");
    printf("This recipe classifies global silence. Shorter repetend orbits are\n"
           "checked separately by the prime command.\n");
    printf("Result  %s\n", pass ? "PASS" : "FAIL");
    return pass ? 0 : 1;
}

int silent_primes_prime(int p, int base, int lag)
{
    if (!spv_validate_base_prime(p, base, 0, 1)) return 1;
    if (lag < 1 || lag > 64) {
        fprintf(stderr, "lag must be between 1 and 64\n");
        return 1;
    }
    int multiplier = spv_mod_pow(base, lag, p);
    int collision = spv_collision_direct_unchecked(p, base, multiplier);
    int repetend = spv_repetend_unchecked(p, base, lag);
    int u = 0;
    int recipe = spv_recipe_match_unchecked(p, base, lag, &u);
    int global_silent = collision == 0;
    int repetend_silent = repetend == 0;
    int pass = recipe == global_silent && (!global_silent || repetend_silent);

    printf("Finite silence and collision-variance arithmetic\n");
    printf("Prime silence inspection\n\n");
    printf("p = %d; base b = %d; lag ell = %d\n", p, base, lag);
    printf("multiplier [b^ell]_p = %d%s\n", multiplier,
           multiplier == 1 ? " (identity)" : "");
    printf("global collision count C_p,b([b^ell]_p) = %d\n", collision);
    printf("repetend autocorrelation R_p,b(ell) = %d\n", repetend);
    printf("globally silent = %s\n", global_silent ? "yes" : "no");
    printf("repetend-silent = %s\n", repetend_silent ? "yes" : "no");
    printf("finite recipe divisor test = %s", recipe ? "yes" : "no");
    if (recipe) printf(" (u=%d)", u);
    printf("\n");
    if (multiplier != 1) {
        int coordinate = spv_multiplier_coordinate(multiplier, p, base);
        printf("collision coordinate c([b^ell]_p) = %d\n", coordinate);
        printf("zero gate c<b = %s\n", coordinate < base ? "yes" : "no");
    } else {
        printf("collision coordinate is undefined for the identity multiplier\n");
    }
    printf("recipe iff global silence  %s\n", recipe == global_silent ?
           "PASS" : "FAIL");
    printf("global silence implies repetend silence  %s\n",
           (!global_silent || repetend_silent) ? "PASS" : "FAIL");
    if (repetend_silent && !global_silent)
        printf("This prime is repetend-silent but not a globally silent prime.\n");
    printf("Result  %s\n", pass ? "PASS" : "FAIL");
    return pass ? 0 : 1;
}

int silent_primes_variance(int p, int base)
{
    if (!spv_validate_base_prime(p, base, 1, 1)) return 1;
    SPVVariance variance;
    if (!spv_compute_variance(p, base, &variance, 1)) {
        fprintf(stderr, "exact variance computation failed\n");
        return 1;
    }
    uint64_t mean_num = (uint64_t)variance.q *
        (uint64_t)(base * (variance.q - 1) + 2 * variance.remainder);
    uint64_t mean_den = (uint64_t)variance.population;
    uint64_t expected_failure_sum =
        (uint64_t)base * (uint64_t)variance.q *
        (uint64_t)(variance.q - 1) / 2ULL;
    int mean_ok = variance.sum_collisions == mean_num;
    int floor_ok = variance.sum_failures == expected_failure_sum;
    int64_t diag_num = (int64_t)variance.diagonal_numerator;
    int64_t diag_reduced = 0;
    int64_t off_reduced = 0;
    uint64_t diag_den = 0;
    uint64_t off_den = 0;
    spv_signed_fraction(diag_num, variance.raw_denominator,
                        &diag_reduced, &diag_den);
    spv_signed_fraction(variance.off_diagonal_numerator,
                        variance.raw_denominator, &off_reduced, &off_den);
    int decomposition_ok =
        (int64_t)variance.raw_numerator ==
        diag_num + variance.off_diagonal_numerator;
    int pass = mean_ok && floor_ok && decomposition_ok;

    printf("Finite silence and collision-variance arithmetic\n");
    printf("Exact constructive variance\n\n");
    printf("p = %d; base b = %d\n", p, base);
    printf("p-1 = bQ+R = %d*%d+%d\n", base, variance.q,
           variance.remainder);
    printf("constructive coordinates c=b+1,...,p-1: N = %d\n\n",
           variance.population);
    printf("sum C(c) = %llu; formula Q(b(Q-1)+2R) = %llu  %s\n",
           (unsigned long long)variance.sum_collisions,
           (unsigned long long)mean_num, mean_ok ? "PASS" : "FAIL");
    printf("mean E[C] = %llu/%llu = %.12Lf\n",
           (unsigned long long)mean_num, (unsigned long long)mean_den,
           (long double)mean_num / (long double)mean_den);
    printf("sum_m |I_m| = %llu; bQ(Q-1)/2 = %llu  %s\n",
           (unsigned long long)variance.sum_failures,
           (unsigned long long)expected_failure_sum,
           floor_ok ? "PASS" : "FAIL");
    printf("variance from direct population and interval ledger = %llu/%llu\n",
           (unsigned long long)variance.numerator,
           (unsigned long long)variance.denominator);
    printf("V_p,b = %.12Lf; V_p,b/Q = %.12Lf\n", variance.value,
           variance.value / (long double)variance.q);
    printf("diagonal contribution = %lld/%llu = %.12Lf\n",
           (long long)diag_reduced, (unsigned long long)diag_den,
           (long double)variance.diagonal_numerator /
               (long double)variance.raw_denominator);
    printf("off-diagonal contribution = %lld/%llu = %+.12Lf\n",
           (long long)off_reduced, (unsigned long long)off_den,
           (long double)variance.off_diagonal_numerator /
               (long double)variance.raw_denominator);
    printf("diagonal plus off-diagonal equals total exactly  %s\n",
           decomposition_ok ? "PASS" : "FAIL");
    printf("candidate limit 1-1/b = %.12Lf\n",
           1.0L - 1.0L / (long double)base);
    printf("The ratio is finite evidence. The full variance asymptotic is open.\n");
    printf("Result  %s\n", pass ? "PASS" : "FAIL");
    return pass ? 0 : 1;
}

static int spv_check_variance_row(int p, int base, uint64_t numerator,
                                  uint64_t denominator,
                                  long double displayed_ratio,
                                  long double tolerance,
                                  SPVVariance *out)
{
    SPVVariance variance;
    if (!spv_compute_variance(p, base, &variance, 0)) return 0;
    long double ratio = variance.value / (long double)variance.q;
    if (numerator != 0 && (variance.numerator != numerator ||
                           variance.denominator != denominator))
        return 0;
    if (fabsl(ratio - displayed_ratio) > tolerance) return 0;
    if (out) *out = variance;
    return 1;
}

int silent_primes_snapshot(void)
{
    struct VarianceRow {
        int p;
        uint64_t numerator;
        uint64_t denominator;
        long double printed_variance;
        long double printed_ratio;
    } rows[] = {
        {97, 11096, 1849, 6.00108L, 0.66679L},
        {193, 115664, 8281, 13.96740L, 0.73513L},
        {499, 150526, 3721, 40.45310L, 0.82557L},
        {997, 20501936, 243049, 84.35310L, 0.85205L},
        {1999, 42757049, 247009, 173.09915L, 0.86984L},
        {4999, 685057257, 1555009, 440.54874L, 0.88286L},
        {9973, 21952888016ULL, 24810361, 884.82743L, 0.88749L}
    };
    struct CrossRow { int base; long double printed_ratio; } cross[] = {
        {3, 0.666072L}, {6, 0.828314L}, {7, 0.847494L},
        {10, 0.887490L}, {12, 0.905998L}
    };
    int pass = 1;
    int row_passes = 0;
    int cross_passes = 0;

    printf("Finite collision-variance fixtures\n");
    printf("Exact rational table reproduction\n\n");
    printf("  p      Q       V_p,10       V_p,10/Q    check\n");
    for (size_t i = 0; i < sizeof(rows) / sizeof(rows[0]); i++) {
        SPVVariance variance;
        int ok = spv_check_variance_row(rows[i].p, 10, rows[i].numerator,
                                        rows[i].denominator,
                                        rows[i].printed_ratio, 5.1e-6L,
                                        &variance) &&
                 fabsl(variance.value - rows[i].printed_variance) < 5.1e-6L;
        printf("  %-6d %-7d %-12.5Lf %-12.5Lf %s\n", rows[i].p,
               (rows[i].p - 1) / 10, variance.value,
               variance.value / ((rows[i].p - 1) / 10),
               ok ? "PASS" : "FAIL");
        if (ok) row_passes++; else pass = 0;
    }
    printf("\n%d/%d base-ten rows reproduced from exact rational values.\n\n",
           row_passes, (int)(sizeof(rows) / sizeof(rows[0])));
    printf("  b      Q       V_9973,b/Q   1-1/b       check\n");
    for (size_t i = 0; i < sizeof(cross) / sizeof(cross[0]); i++) {
        SPVVariance variance;
        int ok = spv_check_variance_row(9973, cross[i].base, 0, 0,
                                        cross[i].printed_ratio, 5.1e-7L,
                                        &variance);
        printf("  %-6d %-7d %-13.6Lf %-11.6Lf %s\n", cross[i].base,
               variance.q, variance.value / variance.q,
               1.0L - 1.0L / cross[i].base, ok ? "PASS" : "FAIL");
        if (ok) cross_passes++; else pass = 0;
    }
    printf("\n%d/%d cross-base rows reproduced.\n", cross_passes,
           (int)(sizeof(cross) / sizeof(cross[0])));
    printf("The comparison with 1-1/b is finite evidence for an open conjecture.\n");
    printf("Result  %s\n", pass ? "PASS" : "FAIL");
    return pass ? 0 : 1;
}

static int spv_contains(const int *values, size_t count, int target)
{
    for (size_t i = 0; i < count; i++)
        if (values[i] == target) return 1;
    return 0;
}

static int spv_decimal_list_ok(void)
{
    for (int p = 11; p <= 100; p++) {
        if (!spv_is_prime(p)) continue;
        int observed = spv_repetend_unchecked(p, 10, 1) == 0;
        int expected = spv_contains(
            spv_decimal_silent,
            sizeof(spv_decimal_silent) / sizeof(spv_decimal_silent[0]), p);
        if (observed != expected) return 0;
    }
    return 1;
}

static int spv_witnesses_ok(void)
{
    for (size_t i = 0;
         i < sizeof(spv_decimal_witnesses) / sizeof(spv_decimal_witnesses[0]);
         i++) {
        const SPVOrbitWitness *witness = &spv_decimal_witnesses[i];
        int residue = spv_mod_pow(10, witness->exponent, witness->p);
        int next = (int)((int64_t)10 * residue % witness->p);
        if (residue != witness->residue || next != witness->next_residue ||
            spv_digit(residue, witness->p, 10) != witness->common_digit ||
            spv_digit(next, witness->p, 10) != witness->common_digit)
            return 0;
    }
    return 1;
}

int silent_primes_examples(void)
{
    int list_ok = spv_decimal_list_ok() && spv_witnesses_ok();
    int global_13 = spv_collision_direct_unchecked(13, 10, 10) == 0;
    int repetend_13 = spv_repetend_unchecked(13, 10, 1) == 0;
    int base8_global = spv_collision_direct_unchecked(13, 8, 8) == 0;
    int base8_repetend = spv_repetend_unchecked(13, 8, 1) == 0;
    SPVVariance variance;
    int variance_ok = spv_compute_variance(97, 10, &variance, 1) &&
                      variance.numerator == 11096 &&
                      variance.denominator == 1849;
    int pass = list_ok && global_13 && repetend_13 && !base8_global &&
               base8_repetend && variance_ok;

    printf("Finite silence and variance examples\n\n");
    printf("base-ten lag-one repetend-silent primes are exactly\n"
           "{11,13,19,23,37,41,73}, with all fourteen nonsilent witnesses  %s\n",
           list_ok ? "PASS" : "FAIL");
    printf("decimal p=13 is globally silent and repetend-silent  %s\n",
           global_13 && repetend_13 ? "PASS" : "FAIL");
    printf("base-eight p=13 is repetend-silent but not globally silent  %s\n",
           base8_repetend && !base8_global ? "PASS" : "FAIL");
    printf("base-ten p=97 variance is exactly 11096/1849  %s\n",
           variance_ok ? "PASS" : "FAIL");
    printf("Result  %s\n", pass ? "PASS" : "FAIL");
    return pass ? 0 : 1;
}

static int spv_interval_ledger_model(int p, int base)
{
    int q = (p - 1) / base;
    int population = p - base - 1;
    unsigned char *membership = calloc(
        (size_t)(q + 1) * (size_t)p, sizeof(*membership));
    if (!membership) return 0;
    int ok = 1;
    uint64_t h_sum = 0;
    uint64_t y_square_sum = 0;

    for (int m = 1; m <= q && ok; m++) {
        for (int k = 1; k < m; k++) {
            int start = (k * p + m - 1) / m;
            for (int offset = 0; offset < base; offset++) {
                int c = start + offset;
                if (c <= base || c >= p || membership[m * p + c]) {
                    ok = 0;
                    break;
                }
                membership[m * p + c] = 1;
            }
        }
        for (int c = base + 1; c < p && ok; c++) {
            int residue = (int)((int64_t)m * c % p);
            int y = residue < m * base;
            int floor_crossing = m * c / p - m * (c - base) / p;
            if (membership[m * p + c] != y || floor_crossing != y) ok = 0;
        }
    }
    for (int m = 1; m <= q && ok; m++) {
        for (int n = 1; n <= q; n++) {
            int h = 0;
            int displayed_h = 0;
            for (int c = base + 1; c < p; c++)
                h += membership[m * p + c] && membership[n * p + c];
            for (int k = 1; k < m; k++) {
                int left = (k * p + m - 1) / m;
                for (int ell = 1; ell < n; ell++) {
                    int right = (ell * p + n - 1) / n;
                    int distance = left > right ? left - right : right - left;
                    if (distance < base) displayed_h += base - distance;
                }
            }
            if (h != displayed_h) ok = 0;
            h_sum += (uint64_t)h;
        }
    }
    for (int c = base + 1; c < p; c++) {
        int y = 0;
        for (int m = 1; m <= q; m++) y += membership[m * p + c];
        y_square_sum += (uint64_t)y * (uint64_t)y;
    }
    if (h_sum != y_square_sum || population <= 0) ok = 0;
    free(membership);
    return ok;
}

static void spv_report_group(const char *label, int ok, int *passed)
{
    printf("  %-66s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int silent_primes_verify(void)
{
    const int bases[] = {2, 3, 6, 7, 10, 12};
    int conjugation_ok = 1;
    int coordinate_bijection_ok = 1;
    int coordinate_formula_ok = 1;
    int zero_gate_ok = 1;
    int recipe_ok = 1;
    int repetend_bound_ok = 1;
    int decimal_list_ok = spv_decimal_list_ok() && spv_witnesses_ok();
    int silence_distinction_ok =
        spv_repetend_unchecked(13, 8, 1) == 0 &&
        spv_collision_direct_unchecked(13, 8, 8) > 0;
    int sawtooth_ok = 1;
    int mean_ok = 1;
    int interval_ok = 1;
    int variance_ok = 1;
    int tables_ok = 1;
    int repetend_count_bound_ok = 1;
    int models = 0;

    for (size_t ib = 0; ib < sizeof(bases) / sizeof(bases[0]); ib++) {
        int base = bases[ib];
        for (int p = base + 1; p <= 199; p++) {
            if (!spv_is_prime(p)) continue;
            models++;
            int *seen = calloc((size_t)p, sizeof(*seen));
            if (!seen) return 0;

            for (int r = 1; r < p && conjugation_ok; r++) {
                int br = (int)((int64_t)base * r % p);
                for (int s = 1; s < p; s++) {
                    int bs = (int)((int64_t)base * s % p);
                    if ((spv_digit(r, p, base) == spv_digit(s, p, base)) !=
                        (br % base == bs % base)) {
                        conjugation_ok = 0;
                        break;
                    }
                }
            }

            for (int c = 1; c < p; c++) {
                if (c == base) continue;
                int multiplier = spv_coordinate_multiplier(c, p, base);
                if (multiplier <= 0 || multiplier >= p || seen[multiplier]++)
                    coordinate_bijection_ok = 0;
                if (spv_multiplier_coordinate(multiplier, p, base) != c)
                    coordinate_bijection_ok = 0;
                int direct = spv_collision_direct_unchecked(p, base, multiplier);
                int coordinate = spv_collision_coordinate_count(c, p, base);
                if (direct != coordinate) coordinate_formula_ok = 0;
                if ((direct == 0) != (c < base) || direct % 2 != 0)
                    zero_gate_ok = 0;
                if (c > base) {
                    int signed_count = 0;
                    int q = (p - 1) / base;
                    for (int m = 1; m <= q; m++) {
                        int residue = (int)((int64_t)m * c % p);
                        signed_count += residue > m * base ? 1 : -1;
                    }
                    if (coordinate != q + signed_count) sawtooth_ok = 0;
                }
            }
            for (int multiplier = 1; multiplier < p; multiplier++) {
                if (multiplier == 1) continue;
                int direct = spv_collision_direct_unchecked(p, base, multiplier);
                int conjugated = 0;
                for (int x = 1; x < p; x++) {
                    int image = (int)((int64_t)multiplier * x % p);
                    conjugated += x % base == image % base;
                }
                if (direct != conjugated) conjugation_ok = 0;
            }
            free(seen);

            for (int lag = 1; lag <= 4; lag++) {
                int multiplier = spv_mod_pow(base, lag, p);
                int global = spv_collision_direct_unchecked(p, base,
                                                            multiplier) == 0;
                if (global != spv_recipe_match_unchecked(p, base, lag, NULL))
                    recipe_ok = 0;
                int repetend = spv_repetend_unchecked(p, base, lag);
                uint64_t bound_power = 1;
                for (int i = 0; i < lag + 1; i++)
                    bound_power *= (uint64_t)base;
                if (repetend == 0 && (uint64_t)p > bound_power)
                    repetend_bound_ok = 0;
                if (repetend < 0 || repetend > p - 1)
                    repetend_count_bound_ok = 0;
            }

            if (p > base + 1) {
                SPVVariance variance;
                if (!spv_compute_variance(p, base, &variance, 1)) {
                    variance_ok = 0;
                    mean_ok = 0;
                } else {
                    uint64_t expected_sum = (uint64_t)variance.q *
                        (uint64_t)(base * (variance.q - 1) +
                                   2 * variance.remainder);
                    if (variance.sum_collisions != expected_sum) mean_ok = 0;
                    if ((int64_t)variance.raw_numerator !=
                        (int64_t)variance.diagonal_numerator +
                        variance.off_diagonal_numerator)
                        variance_ok = 0;
                }
            }
        }
    }

    const int interval_primes[] = {13, 17, 29, 43, 97, 193};
    for (size_t i = 0;
         i < sizeof(interval_primes) / sizeof(interval_primes[0]); i++)
        if (!spv_interval_ledger_model(interval_primes[i], 10)) interval_ok = 0;

    struct ExactRow { int p; uint64_t n; uint64_t d; } exact_rows[] = {
        {97, 11096, 1849}, {193, 115664, 8281},
        {499, 150526, 3721}, {997, 20501936, 243049},
        {1999, 42757049, 247009}, {4999, 685057257, 1555009},
        {9973, 21952888016ULL, 24810361}
    };
    for (size_t i = 0; i < sizeof(exact_rows) / sizeof(exact_rows[0]); i++) {
        SPVVariance variance;
        if (!spv_compute_variance(exact_rows[i].p, 10, &variance, 0) ||
            variance.numerator != exact_rows[i].n ||
            variance.denominator != exact_rows[i].d)
            tables_ok = 0;
    }
    const int cross_bases[] = {3, 6, 7, 10, 12};
    const long double cross_values[] = {
        0.666072L, 0.828314L, 0.847494L, 0.887490L, 0.905998L
    };
    for (size_t i = 0; i < sizeof(cross_bases) / sizeof(cross_bases[0]); i++) {
        SPVVariance variance;
        if (!spv_compute_variance(9973, cross_bases[i], &variance, 0) ||
            fabsl(variance.value / variance.q - cross_values[i]) > 5.1e-7L)
            tables_ok = 0;
    }

    int passed = 0;
    const int total = 14;
    printf("Finite C verification of silence and collision variance\n");
    printf("Exact integer arithmetic over %d finite (base, prime) models.\n\n",
           models);
    spv_report_group("digit-bin conjugation and collision congruence",
                     conjugation_ok, &passed);
    spv_report_group("collision-coordinate bijection and inverse",
                     coordinate_bijection_ok, &passed);
    spv_report_group("positive-comparison collision formula",
                     coordinate_formula_ok, &passed);
    spv_report_group("zero gate, gate width, and even collision counts",
                     zero_gate_ok, &passed);
    spv_report_group("fixed-lag global silent-prime divisor recipe",
                     recipe_ok, &passed);
    spv_report_group("finite repetend-silence bound p <= b^(ell+1)",
                     repetend_bound_ok, &passed);
    spv_report_group("seven base-ten lag-one primes and all orbit witnesses",
                     decimal_list_ok, &passed);
    spv_report_group("global versus shorter-orbit repetend silence",
                     silence_distinction_ok, &passed);
    spv_report_group("signed sawtooth comparison identity",
                     sawtooth_ok, &passed);
    spv_report_group("exact constructive population mean", mean_ok, &passed);
    spv_report_group("floor crossing and explicit double-sum overlap ledger",
                     interval_ok, &passed);
    spv_report_group("exact variance and diagonal/off-diagonal decomposition",
                     variance_ok, &passed);
    spv_report_group("all reference finite variance table rows", tables_ok,
                     &passed);
    spv_report_group("repetend autocorrelation stays within orbit length",
                     repetend_count_bound_ok, &passed);
    printf("\n%d/%d verification groups passed.\n", passed, total);
    printf("The full variance limit is conjectural. Every check above is exact\n"
           "finite arithmetic or a bounded finite sweep.\n");
    return passed == total;
}

void silent_primes_help(void)
{
    printf(
        "Finite silence and collision-variance arithmetic\n\n"
        "Inspect global and orbit silence, factor the finite fixed-lag recipe,\n"
        "and compare direct collision variance with its interval ledger.\n\n"
        "Usage:\n"
        "  nfield silent-primes recipe [--base <b>] [--lag <ell>]\n"
        "  nfield silent-primes prime <p> [--base <b>] [--lag <ell>]\n"
        "  nfield silent-primes variance <p> [--base <b>]\n"
        "  nfield silent-primes snapshot\n"
        "  nfield silent-primes examples\n"
        "  nfield silent-primes verify\n"
        "  nfield verify silent-primes\n\n"
        "recipe factors the finite arithmetic progression whose prime divisors\n"
        "are exactly the globally silent primes at the chosen base and lag.\n"
        "prime computes both the complete-field collision count C and the\n"
        "single-orbit repetend count R. Global silence implies repetend silence,\n"
        "but a shorter orbit can be repetend-silent without being globally silent.\n\n"
        "variance computes the exact constructive mean and population variance.\n"
        "It checks the collision-coordinate count against direct digit bins, then\n"
        "separates the exact diagonal and off-diagonal contributions. The\n"
        "snapshot action reproduces the reference tables from exact rational\n"
        "arithmetic.\n\n"
        "The verifier checks exact identities, bounded model sweeps, and the\n"
        "reference fixtures. Finite sweeps are evidence, not symbolic proofs.\n"
        "The proposed limit V_p,b/Q -> 1-1/b remains a conjecture.\n\n"
        "The legacy underscore command silent_primes is preserved separately for\n"
        "older posts and scripts.\n"
    );
}
