/*
 * compatible_residue_channels.c
 *
 * Exact finite arithmetic for compatible residue channels.
 * Shared collision-table construction and fiber centering come from
 * collision_table_core.c.  This module adds arbitrary prime channels,
 * simultaneous squarefree channels, and finite character ledgers.
 */

#include <complex.h>
#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#define GN_MAX_BASE 64
#define GN_MAX_MODULUS 50000
#define GN_MAX_JOINT_MODULUS 2000000
#define GN_MAX_CHANNEL_MODULUS 2100
#define GN_MAX_CUTOFF 5000000
#define GN_ACTIVE_TOLERANCE 1.0e-12L

enum {
    GN_BASE10_EXPONENT_COUNT = 4,
    GN_PRIME_BASE_COUNT = 10
};

static const long double gn_base10_exponents[GN_BASE10_EXPONENT_COUNT] = {
    1.0L, 0.8L, 0.6L, 0.5L
};

static const int gn_prime_bases[GN_PRIME_BASE_COUNT] = {
    5, 7, 11, 13, 17, 19, 23, 29, 31, 37
};

typedef struct {
    int modulus;
    int count;
    long double complex *value;
} GNCharacterSystem;

typedef struct {
    int positive;
    int negative;
    int exact_zero;
    int active;
    int prime_count;
    long double net;
    long double direct;
    long double decomposition_error;
    long double correlation;
} GNBaseTenRow;

typedef struct {
    int base;
    int prime_count;
    int odd_characters;
    int active;
    int inactive;
    int positive;
    int negative;
    long double correlation;
    long double actual;
    long double direct;
    long double decomposition_error;
    long double expected;
    long double standard_deviation;
    long double z;
} GNPrimeBaseRow;

typedef struct {
    long double mean;
    long double standard_deviation;
} GNPermutationMoments;

typedef struct {
    int reflection_cases;
    int fiber_cases;
    int internal_pairs;
    int internal_nondividing_pairs;
    int internal_nonempty;
    int internal_empty;
    int internal_nondividing_empty;
    int internal_dividing_empty;
    int external_pairs;
    int external_channels;
    int simultaneous_pairs;
    int simultaneous_channels;
    int failures;
} GNExactAudit;

static int gn_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int gn_phi(int n)
{
    int result = n;
    int remaining = n;
    for (int p = 2; p <= remaining / p; p++) {
        if (remaining % p != 0) continue;
        result -= result / p;
        while (remaining % p == 0) remaining /= p;
    }
    if (remaining > 1) result -= result / remaining;
    return result;
}

static int gn_lcm(int a, int b, int *result)
{
    if (!result || a < 1 || b < 1) return 0;
    int divisor = collision_table_gcd(a, b);
    int64_t value = (int64_t)(a / divisor) * b;
    if (value > GN_MAX_JOINT_MODULUS) return 0;
    *result = (int)value;
    return 1;
}

static int gn_is_squarefree(int n)
{
    if (n < 2) return 0;
    int remaining = n;
    for (int p = 2; p <= remaining / p; p++) {
        if (remaining % p != 0) continue;
        remaining /= p;
        if (remaining % p == 0) return 0;
        while (remaining % p == 0) remaining /= p;
    }
    return 1;
}

static int gn_validate_table(int base, int lag, int report, int *modulus)
{
    int m = 0;
    if (base < 2 || base > GN_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n", GN_MAX_BASE);
        return 0;
    }
    if (lag < 1 || lag > 16) {
        if (report) fprintf(stderr, "lag must be between 1 and 16\n");
        return 0;
    }
    if (!collision_table_modulus(base, lag, &m) || m > GN_MAX_MODULUS) {
        if (report)
            fprintf(stderr,
                    "base^(lag+1) exceeds the compatible-channel table limit of %d\n",
                    GN_MAX_MODULUS);
        return 0;
    }
    if (modulus) *modulus = m;
    return 1;
}

static int gn_mod_pow(int base, int exponent, int modulus)
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

static int gn_primitive_root_prime_square(int prime)
{
    int modulus = prime * prime;
    int order = prime * (prime - 1);
    int factors[16];
    int factor_count = 0;
    int remaining = order;
    for (int p = 2; p <= remaining / p; p++) {
        if (remaining % p != 0) continue;
        factors[factor_count++] = p;
        while (remaining % p == 0) remaining /= p;
    }
    if (remaining > 1) factors[factor_count++] = remaining;
    for (int candidate = 2; candidate < modulus; candidate++) {
        int primitive = collision_table_gcd(candidate, modulus) == 1;
        for (int i = 0; primitive && i < factor_count; i++)
            if (gn_mod_pow(candidate, order / factors[i], modulus) == 1)
                primitive = 0;
        if (primitive) return candidate;
    }
    return 0;
}

static void gn_character_system_free(GNCharacterSystem *system)
{
    if (!system) return;
    free(system->value);
    memset(system, 0, sizeof(*system));
}

static int gn_prime_base_characters(int base, GNCharacterSystem *system)
{
    int modulus = base * base;
    int phi = base * (base - 1);
    int generator = gn_primitive_root_prime_square(base);
    int *discrete_log = NULL;
    int value = 1;
    long double two_pi = 2.0L * acosl(-1.0L);
    memset(system, 0, sizeof(*system));
    if (!gn_is_prime(base) || generator == 0) return 0;
    discrete_log = malloc((size_t)modulus * sizeof(*discrete_log));
    if (!discrete_log) return 0;
    for (int a = 0; a < modulus; a++) discrete_log[a] = -1;
    for (int index = 0; index < phi; index++) {
        discrete_log[value] = index;
        value = (int)((int64_t)value * generator % modulus);
    }
    system->modulus = modulus;
    system->count = phi / 2;
    system->value = calloc((size_t)system->count * modulus,
                           sizeof(*system->value));
    if (!system->value) {
        free(discrete_log);
        return 0;
    }
    int character = 0;
    for (int exponent = 1; exponent < phi; exponent += 2) {
        for (int a = 1; a < modulus; a++) {
            if (discrete_log[a] < 0) continue;
            long double angle = two_pi * exponent * discrete_log[a] / phi;
            system->value[(size_t)character * modulus + a] =
                cosl(angle) + I * sinl(angle);
        }
        character++;
    }
    free(discrete_log);
    return character == system->count;
}

static int gn_base10_characters(GNCharacterSystem *system)
{
    int discrete_log25[25];
    int value = 1;
    int character = 0;
    long double two_pi = 2.0L * acosl(-1.0L);
    memset(system, 0, sizeof(*system));
    for (int a = 0; a < 25; a++) discrete_log25[a] = -1;
    for (int index = 0; index < 20; index++) {
        discrete_log25[value] = index;
        value = value * 2 % 25;
    }
    system->modulus = 100;
    system->count = 20;
    system->value = calloc((size_t)system->count * 100,
                           sizeof(*system->value));
    if (!system->value) return 0;
    for (int parity = 0; parity <= 1; parity++) {
        for (int exponent = 0; exponent < 20; exponent++) {
            if (((parity + exponent) & 1) == 0) continue;
            for (int a = 1; a < 100; a++) {
                if (collision_table_gcd(a, 100) != 1) continue;
                long double sign =
                    parity == 0 || a % 4 == 1 ? 1.0L : -1.0L;
                long double angle =
                    two_pi * exponent * discrete_log25[a % 25] / 20.0L;
                system->value[(size_t)character * 100 + a] =
                    sign * (cosl(angle) + I * sinl(angle));
            }
            character++;
        }
    }
    return character == system->count;
}

static int *gn_prime_list(int limit, int *prime_count)
{
    unsigned char *composite = calloc((size_t)limit + 1, 1);
    int *primes = NULL;
    int count = 0;
    if (!composite || limit < 2 || !prime_count) {
        free(composite);
        return NULL;
    }
    composite[0] = composite[1] = 1;
    for (int p = 2; p <= limit / p; p++) {
        if (composite[p]) continue;
        for (int64_t multiple = (int64_t)p * p;
             multiple <= limit; multiple += p)
            composite[multiple] = 1;
    }
    for (int p = 2; p <= limit; p++) count += !composite[p];
    primes = malloc((size_t)count * sizeof(*primes));
    if (!primes) {
        free(composite);
        return NULL;
    }
    count = 0;
    for (int p = 2; p <= limit; p++)
        if (!composite[p]) primes[count++] = p;
    free(composite);
    *prime_count = count;
    return primes;
}

static int gn_spectral_data(
    const CollisionCenteredTable *table,
    const GNCharacterSystem *system,
    const int *primes, int prime_count,
    const long double *exponents, int exponent_count,
    long double complex *coefficients,
    long double complex *prime_sums,
    long double *direct_sums,
    int *used_prime_count)
{
    int modulus = table->modulus;
    long double *weights =
        calloc((size_t)exponent_count * modulus, sizeof(*weights));
    if (!weights || system->modulus != modulus) {
        free(weights);
        return 0;
    }
    for (int e = 0; e < exponent_count; e++) direct_sums[e] = 0.0L;
    int used = 0;
    for (int pi = 0; pi < prime_count; pi++) {
        int p = primes[pi];
        if (p <= modulus) continue;
        int a = p % modulus;
        int fiber = a % table->base;
        long double centered =
            (long double)table->centered_numerator[a] /
            table->fiber_count[fiber];
        used++;
        for (int e = 0; e < exponent_count; e++) {
            long double weight = powl((long double)p, -exponents[e]);
            weights[(size_t)e * modulus + a] += weight;
            direct_sums[e] += centered * weight;
        }
    }
    for (int character = 0; character < system->count; character++) {
        long double complex coefficient = 0.0L;
        for (int a = 1; a < modulus; a++) {
            if (collision_table_gcd(a, modulus) != 1) continue;
            int fiber = a % table->base;
            long double centered =
                (long double)table->centered_numerator[a] /
                table->fiber_count[fiber];
            coefficient += centered *
                conjl(system->value[(size_t)character * modulus + a]);
        }
        coefficients[character] = coefficient / table->phi;
        for (int e = 0; e < exponent_count; e++) {
            long double complex sum = 0.0L;
            for (int a = 1; a < modulus; a++) {
                long double weight = weights[(size_t)e * modulus + a];
                if (weight == 0.0L) continue;
                sum += system->value[(size_t)character * modulus + a] *
                    weight;
            }
            prime_sums[(size_t)e * system->count + character] = sum;
        }
    }
    free(weights);
    *used_prime_count = used;
    return 1;
}

static int gn_active(long double complex coefficient)
{
    return cabsl(coefficient) > GN_ACTIVE_TOLERANCE;
}

static long double gn_active_correlation(
    const long double complex *coefficients,
    const long double complex *prime_sums, int count)
{
    long double sx = 0.0L, sy = 0.0L;
    long double sxx = 0.0L, syy = 0.0L, sxy = 0.0L;
    int active = 0;
    for (int i = 0; i < count; i++) {
        if (!gn_active(coefficients[i])) continue;
        long double x = cabsl(coefficients[i]);
        long double y = cabsl(prime_sums[i]);
        sx += x;
        sy += y;
        sxx += x * x;
        syy += y * y;
        sxy += x * y;
        active++;
    }
    if (active < 2) return 0.0L;
    long double mx = sx / active;
    long double my = sy / active;
    long double vx = sxx / active - mx * mx;
    long double vy = syy / active - my * my;
    long double covariance = sxy / active - mx * my;
    if (vx <= 0.0L || vy <= 0.0L) return 0.0L;
    return covariance / sqrtl(vx * vy);
}

static GNPermutationMoments gn_permutation_moments(
    const long double complex *coefficients,
    const long double complex *prime_sums, int count)
{
    GNPermutationMoments result = {0.0L, 0.0L};
    if (count <= 1) return result;
    long double max = 0.0L, may = 0.0L, mcx = 0.0L, mcy = 0.0L;
    for (int i = 0; i < count; i++) {
        max += creall(coefficients[i]);
        may += cimagl(coefficients[i]);
        mcx += creall(prime_sums[i]);
        mcy -= cimagl(prime_sums[i]);
    }
    max /= count;
    may /= count;
    mcx /= count;
    mcy /= count;
    result.mean = count * (max * mcx + may * mcy);

    long double axx = 0.0L, axy = 0.0L, ayy = 0.0L;
    long double cxx = 0.0L, cxy = 0.0L, cyy = 0.0L;
    for (int i = 0; i < count; i++) {
        long double ax = creall(coefficients[i]) - max;
        long double ay = cimagl(coefficients[i]) - may;
        long double cx = creall(prime_sums[i]) - mcx;
        long double cy = -cimagl(prime_sums[i]) - mcy;
        axx += ax * ax;
        axy += ax * ay;
        ayy += ay * ay;
        cxx += cx * cx;
        cxy += cx * cy;
        cyy += cy * cy;
    }
    axx /= count;
    axy /= count;
    ayy /= count;
    long double variance = (long double)count / (count - 1) *
        (axx * cxx + 2.0L * axy * cxy + ayy * cyy);
    if (variance < 0.0L && fabsl(variance) < 1.0e-24L) variance = 0.0L;
    result.standard_deviation = variance > 0.0L ? sqrtl(variance) : 0.0L;
    return result;
}

static int gn_zero_base10_coefficients(long double complex *coefficients,
                                        int count,
                                        long double *largest_residual)
{
    int zero_count = 0;
    *largest_residual = 0.0L;
    for (int character = 0; character < count; character++) {
        int parity;
        int exponent;
        if (character < count / 2) {
            parity = 0;
            exponent = 2 * character + 1;
        } else {
            parity = 1;
            exponent = 2 * (character - count / 2);
        }
        int proved_zero =
            (parity == 0 && (exponent == 5 || exponent == 15)) ||
            (parity == 1 && exponent == 0);
        if (!proved_zero) continue;
        long double residual = cabsl(coefficients[character]);
        if (residual > *largest_residual) *largest_residual = residual;
        if (residual > GN_ACTIVE_TOLERANCE) return 0;
        coefficients[character] = 0.0L;
        zero_count++;
    }
    return zero_count == 3;
}

static int gn_base10_rows(const int *primes, int prime_count,
                          GNBaseTenRow rows[GN_BASE10_EXPONENT_COUNT],
                          long double *largest_zero_residual)
{
    CollisionCenteredTable table = {0};
    GNCharacterSystem system = {0};
    long double complex *coefficients = NULL;
    long double complex *prime_sums = NULL;
    long double direct[GN_BASE10_EXPONENT_COUNT];
    int used = 0;
    int ok = 0;
    if (!collision_centered_table_build(10, 1, &table) ||
        !gn_base10_characters(&system)) goto cleanup;
    coefficients = calloc((size_t)system.count, sizeof(*coefficients));
    prime_sums = calloc((size_t)system.count * GN_BASE10_EXPONENT_COUNT,
                        sizeof(*prime_sums));
    if (!coefficients || !prime_sums) goto cleanup;
    if (!gn_spectral_data(&table, &system, primes, prime_count,
                          gn_base10_exponents, GN_BASE10_EXPONENT_COUNT,
                          coefficients, prime_sums, direct, &used))
        goto cleanup;
    if (!gn_zero_base10_coefficients(coefficients, system.count,
                                     largest_zero_residual))
        goto cleanup;
    for (int e = 0; e < GN_BASE10_EXPONENT_COUNT; e++) {
        GNBaseTenRow row = {0};
        row.exact_zero = 3;
        row.prime_count = used;
        long double complex decomposition = 0.0L;
        for (int character = 0; character < system.count; character++) {
            if (!gn_active(coefficients[character])) continue;
            row.active++;
            long double complex product = coefficients[character] *
                prime_sums[(size_t)e * system.count + character];
            long double real_product = creall(product);
            decomposition += product;
            if (real_product > GN_ACTIVE_TOLERANCE) row.positive++;
            else if (real_product < -GN_ACTIVE_TOLERANCE) row.negative++;
        }
        row.net = creall(decomposition);
        row.direct = direct[e];
        row.decomposition_error = cabsl(decomposition - direct[e]);
        row.correlation = gn_active_correlation(
            coefficients, &prime_sums[(size_t)e * system.count],
            system.count);
        rows[e] = row;
    }
    ok = 1;
cleanup:
    free(coefficients);
    free(prime_sums);
    gn_character_system_free(&system);
    collision_centered_table_free(&table);
    return ok;
}

static int gn_prime_base_rows(const int *primes, int prime_count,
                              GNPrimeBaseRow rows[GN_PRIME_BASE_COUNT])
{
    const long double exponent = 0.5L;
    for (int bi = 0; bi < GN_PRIME_BASE_COUNT; bi++) {
        int base = gn_prime_bases[bi];
        CollisionCenteredTable table = {0};
        GNCharacterSystem system = {0};
        long double complex *coefficients = NULL;
        long double complex *prime_sums = NULL;
        long double direct = 0.0L;
        int used = 0;
        int ok = 0;
        if (!collision_centered_table_build(base, 1, &table) ||
            !gn_prime_base_characters(base, &system))
            goto row_cleanup;
        coefficients = calloc((size_t)system.count, sizeof(*coefficients));
        prime_sums = calloc((size_t)system.count, sizeof(*prime_sums));
        if (!coefficients || !prime_sums) goto row_cleanup;
        if (!gn_spectral_data(&table, &system, primes, prime_count,
                              &exponent, 1, coefficients, prime_sums,
                              &direct, &used))
            goto row_cleanup;
        for (int character = 0; character < system.count; character++) {
            int character_exponent = 2 * character + 1;
            if (character_exponent % base != 0) continue;
            if (cabsl(coefficients[character]) > GN_ACTIVE_TOLERANCE)
                goto row_cleanup;
            coefficients[character] = 0.0L;
        }
        GNPrimeBaseRow row = {0};
        row.base = base;
        row.prime_count = used;
        row.odd_characters = system.count;
        row.direct = direct;
        long double complex decomposition = 0.0L;
        for (int character = 0; character < system.count; character++) {
            if (!gn_active(coefficients[character])) {
                row.inactive++;
                continue;
            }
            row.active++;
            long double complex product =
                coefficients[character] * prime_sums[character];
            long double real_product = creall(product);
            decomposition += product;
            if (real_product > GN_ACTIVE_TOLERANCE) row.positive++;
            else if (real_product < -GN_ACTIVE_TOLERANCE) row.negative++;
        }
        row.actual = creall(decomposition);
        row.decomposition_error = cabsl(decomposition - direct);
        row.correlation = gn_active_correlation(
            coefficients, prime_sums, system.count);
        GNPermutationMoments moments = gn_permutation_moments(
            coefficients, prime_sums, system.count);
        row.expected = moments.mean;
        row.standard_deviation = moments.standard_deviation;
        if (moments.standard_deviation > 0.0L)
            row.z = (row.actual - moments.mean) / moments.standard_deviation;
        rows[bi] = row;
        ok = 1;
row_cleanup:
        free(coefficients);
        free(prime_sums);
        gn_character_system_free(&system);
        collision_centered_table_free(&table);
        if (!ok) return 0;
    }
    return 1;
}

static int gn_channel_sums(const CollisionCenteredTable *table,
                           int channel_modulus,
                           int **count, long long **raw,
                           long long **centered, int *joint_modulus)
{
    int joint = 0;
    if (!gn_lcm(table->modulus, channel_modulus, &joint)) return 0;
    int *counts = calloc((size_t)channel_modulus, sizeof(*counts));
    long long *raw_sums = calloc((size_t)channel_modulus,
                                 sizeof(*raw_sums));
    long long *centered_sums = calloc((size_t)channel_modulus,
                                      sizeof(*centered_sums));
    if (!counts || !raw_sums || !centered_sums) {
        free(counts);
        free(raw_sums);
        free(centered_sums);
        return 0;
    }
    for (int A = 1; A < joint; A++) {
        if (collision_table_gcd(A, joint) != 1) continue;
        int residue = A % channel_modulus;
        int a = A % table->modulus;
        counts[residue]++;
        raw_sums[residue] += table->value[a];
        centered_sums[residue] += table->centered_numerator[a];
    }
    *count = counts;
    *raw = raw_sums;
    *centered = centered_sums;
    *joint_modulus = joint;
    return 1;
}

int compatible_residue_channels_inspect(int integer, int prime,
                                        int base, int lag)
{
    int modulus = 0;
    if (!gn_validate_table(base, lag, 1, &modulus)) return 1;
    if (integer < 0) {
        fprintf(stderr, "integer must be nonnegative\n");
        return 1;
    }
    if (!gn_is_prime(prime) || prime > GN_MAX_CHANNEL_MODULUS) {
        fprintf(stderr, "channel modulus must be a prime not exceeding %d\n",
                GN_MAX_CHANNEL_MODULUS);
        return 1;
    }
    int quotient = integer / modulus;
    int representative = integer % modulus;
    int internal_residue = representative % prime;
    int quotient_shift = (int)((int64_t)(modulus % prime) *
                               (quotient % prime) % prime);
    int reconstructed = (internal_residue + quotient_shift) % prime;
    int true_residue = integer % prime;
    int is_unit = collision_table_gcd(representative, modulus) == 1;
    int ok = reconstructed == true_residue;

    printf("Compatible residue coordinate\n\n");
    printf("integer=%d; base=%d; lag=%d; table modulus=%d; prime=%d\n",
           integer, base, lag, modulus, prime);
    printf("n = m*t + a: t=%d; a=%d\n", quotient, representative);
    printf("internal representative class a mod q = %d\n", internal_residue);
    printf("quotient shift m*t mod q = %d\n", quotient_shift);
    printf("true integer class n mod q = %d\n", true_residue);
    printf("a + m*t mod q = %d  %s\n", reconstructed,
           ok ? "PASS" : "FAIL");
    printf("representative a is %sa unit modulo m\n", is_unit ? "" : "not ");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int compatible_residue_channels_internal(int prime, int base, int lag)
{
    int modulus = 0;
    if (!gn_validate_table(base, lag, 1, &modulus)) return 1;
    if (!gn_is_prime(prime) || prime == 2 ||
        prime > GN_MAX_CHANNEL_MODULUS) {
        fprintf(stderr,
                "internal fixed slices require an odd prime not exceeding %d\n",
                GN_MAX_CHANNEL_MODULUS);
        return 1;
    }
    if (base % prime == 0) {
        fprintf(stderr, "internal fixed slices require the prime not to divide the base\n");
        return 1;
    }
    CollisionCenteredTable table = {0};
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    int fixed = (modulus % prime) * ((prime + 1) / 2) % prime;
    int count = 0;
    long long raw = 0;
    long long centered = 0;
    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1 || a % prime != fixed)
            continue;
        count++;
        raw += table.value[a];
        centered += table.centered_numerator[a];
    }
    int ok = centered == 0 && (count == 0 || 2 * raw == -count);
    printf("Internal residue slice\n\n");
    printf("base=%d; lag=%d; table modulus=%d; internal prime=%d\n",
           base, lag, modulus, prime);
    printf("fixed label solves 2k = m mod q: k=%d\n", fixed);
    printf("slice count=%d; raw sum=%+lld; centered numerator sum=%+lld\n",
           count, raw, centered);
    if (count == 0)
        printf("the formal fixed slice is empty; the identities are vacuous\n");
    else
        printf("raw mean is exactly -1/2 and centered sum is zero\n");
    printf("This is an internal representative slice, not a true integer channel.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

int compatible_residue_channels_prime(int prime, int base, int lag)
{
    int modulus = 0;
    if (!gn_validate_table(base, lag, 1, &modulus)) return 1;
    if (!gn_is_prime(prime) || prime > GN_MAX_CHANNEL_MODULUS) {
        fprintf(stderr, "channel modulus must be a prime not exceeding %d\n",
                GN_MAX_CHANNEL_MODULUS);
        return 1;
    }
    CollisionCenteredTable table = {0};
    int *count = NULL;
    long long *raw = NULL;
    long long *centered = NULL;
    int joint = 0;
    if (!collision_centered_table_build(base, lag, &table) ||
        !gn_channel_sums(&table, prime, &count, &raw, &centered, &joint)) {
        collision_centered_table_free(&table);
        return 1;
    }
    int expected_count = base % prime == 0
        ? table.phi / (prime - 1) : table.phi;
    int ok = 1;
    printf("Compatible prime residue channels\n\n");
    printf("base=%d; lag=%d; table modulus=%d; prime=%d; joint modulus=%d\n",
           base, lag, modulus, prime, joint);
    printf("  residue   count   raw sum   centered numerator sum   status\n");
    for (int residue = 1; residue < prime; residue++) {
        int row_ok = count[residue] == expected_count &&
                     centered[residue] == 0;
        if (base % prime != 0)
            row_ok &= 2 * raw[residue] == -count[residue];
        printf("  %7d %7d %+9lld %+24lld   %s\n",
               residue, count[residue], raw[residue], centered[residue],
               row_ok ? "PASS" : "FAIL");
        ok &= row_ok;
    }
    if (base % prime == 0)
        printf("Each channel is a union of complete zero-sum reduction fibers.\n");
    else
        printf("Each channel is one complete table copy with raw mean -1/2.\n");
    printf("Every true nonzero channel has centered sum zero.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    free(count);
    free(raw);
    free(centered);
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

int compatible_residue_channels_squarefree(int squarefree, int base, int lag)
{
    int modulus = 0;
    if (!gn_validate_table(base, lag, 1, &modulus)) return 1;
    if (!gn_is_squarefree(squarefree) ||
        squarefree > GN_MAX_CHANNEL_MODULUS) {
        fprintf(stderr, "simultaneous modulus must be squarefree and at most %d\n",
                GN_MAX_CHANNEL_MODULUS);
        return 1;
    }
    CollisionCenteredTable table = {0};
    int *count = NULL;
    long long *raw = NULL;
    long long *centered = NULL;
    int joint = 0;
    if (!collision_centered_table_build(base, lag, &table) ||
        !gn_channel_sums(&table, squarefree, &count, &raw,
                         &centered, &joint)) {
        collision_centered_table_free(&table);
        return 1;
    }
    int shared = collision_table_gcd(squarefree, base);
    int expected_count = table.phi / gn_phi(shared);
    int ok = 1;
    int channels = 0;
    printf("Simultaneous squarefree neutrality\n\n");
    printf("base=%d; lag=%d; table modulus=%d; squarefree modulus=%d\n",
           base, lag, modulus, squarefree);
    printf("joint modulus=%d; gcd(Q,b)=%d; expected channel size=%d\n\n",
           joint, shared, expected_count);
    printf("  residue   count   raw sum   centered numerator sum   status\n");
    for (int residue = 1; residue < squarefree; residue++) {
        if (collision_table_gcd(residue, squarefree) != 1) continue;
        int row_ok = count[residue] == expected_count &&
                     centered[residue] == 0;
        if (shared == 1)
            row_ok &= 2 * raw[residue] == -count[residue];
        printf("  %7d %7d %+9lld %+24lld   %s\n",
               residue, count[residue], raw[residue], centered[residue],
               row_ok ? "PASS" : "FAIL");
        ok &= row_ok;
        channels++;
    }
    printf("\n%d unit channels checked; every centered sum is zero.\n",
           channels);
    if (shared == 1)
        printf("Every raw channel mean is exactly -1/2.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    free(count);
    free(raw);
    free(centered);
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

static int gn_valid_cutoff(int cutoff)
{
    if (cutoff <= 100 || cutoff > GN_MAX_CUTOFF) {
        fprintf(stderr, "cutoff must satisfy 100 < cutoff <= %d\n",
                GN_MAX_CUTOFF);
        return 0;
    }
    return 1;
}

int compatible_residue_channels_character_signs(int cutoff)
{
    if (!gn_valid_cutoff(cutoff)) return 1;
    int prime_count = 0;
    int *primes = gn_prime_list(cutoff, &prime_count);
    GNBaseTenRow rows[GN_BASE10_EXPONENT_COUNT];
    long double zero_residual = 0.0L;
    if (!primes || !gn_base10_rows(primes, prime_count, rows,
                                   &zero_residual)) {
        free(primes);
        return 1;
    }
    int ok = 1;
    printf("Finite active-character signs\n\n");
    printf("base=10; lag=1; 100 < p <= %d; odd characters=20\n", cutoff);
    printf("largest residual among three proved zeros = %.3Le\n\n",
           zero_residual);
    printf(" sigma  positive negative exact-zero       net      correlation  check\n");
    for (int e = 0; e < GN_BASE10_EXPONENT_COUNT; e++) {
        int row_ok = rows[e].active == 17 && rows[e].exact_zero == 3 &&
            rows[e].decomposition_error < 2.0e-12L;
        ok &= row_ok;
        printf("  %.1Lf %9d %8d %10d %+11.6Lf %+12.4Lf  %s\n",
               gn_base10_exponents[e], rows[e].positive, rows[e].negative,
               rows[e].exact_zero, rows[e].net, rows[e].correlation,
               row_ok ? "PASS" : "FAIL");
    }
    printf("\nEach row checks the finite character decomposition against the direct sum.\n");
    printf("Mixed signs are finite evidence and give no convergence claim below one.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    free(primes);
    return ok ? 0 : 1;
}

static int gn_print_prime_rows(int cutoff, int assignment_null)
{
    if (!gn_valid_cutoff(cutoff)) return 1;
    int prime_count = 0;
    int *primes = gn_prime_list(cutoff, &prime_count);
    GNPrimeBaseRow rows[GN_PRIME_BASE_COUNT];
    if (!primes || !gn_prime_base_rows(primes, prime_count, rows)) {
        free(primes);
        return 1;
    }
    int ok = 1;
    if (assignment_null) {
        printf("Finite assignment null\n\n");
        printf("cutoff=%d; exponent=1/2; all odd coefficient values retained\n",
               cutoff);
        printf("The null does not preserve conjugate pairs.\n\n");
        printf(" base      actual    expected      stddev       z   check\n");
        for (int i = 0; i < GN_PRIME_BASE_COUNT; i++) {
            int row_ok = rows[i].decomposition_error < 2.0e-11L &&
                         rows[i].standard_deviation > 0.0L;
            ok &= row_ok;
            printf(" %4d  %+10.4Lf %+10.4Lf %10.4Lf %+7.2Lf  %s\n",
                   rows[i].base, rows[i].actual, rows[i].expected,
                   rows[i].standard_deviation, rows[i].z,
                   row_ok ? "PASS" : "FAIL");
        }
        printf("\nThis is a finite comparison, not a probability model for the arithmetic.\n");
    } else {
        printf("Finite collision-to-prime magnitude correlations\n\n");
        printf("cutoff=%d; lag=1; exponent=1/2\n\n", cutoff);
        printf(" base   primes retained   correlation  decomposition\n");
        for (int i = 0; i < GN_PRIME_BASE_COUNT; i++) {
            int row_ok = rows[i].decomposition_error < 2.0e-11L;
            ok &= row_ok;
            printf(" %4d %8d %8d %+13.4Lf  %s\n",
                   rows[i].base, rows[i].prime_count, rows[i].active,
                   rows[i].correlation, row_ok ? "PASS" : "FAIL");
        }
        printf("\nCorrelation records finite magnitudes, not phase, sign, or convergence.\n");
    }
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    free(primes);
    return ok ? 0 : 1;
}

int compatible_residue_channels_magnitude_correlations(int cutoff)
{
    return gn_print_prime_rows(cutoff, 0);
}

int compatible_residue_channels_assignment_null(int cutoff)
{
    return gn_print_prime_rows(cutoff, 1);
}

static int gn_snapshot_ok(int print)
{
    static const int expected_pos[GN_BASE10_EXPONENT_COUNT] = {10, 12, 10, 10};
    static const int expected_neg[GN_BASE10_EXPONENT_COUNT] = {7, 5, 7, 7};
    static const long double expected_net[GN_BASE10_EXPONENT_COUNT] = {
        0.077446L, 0.185838L, 0.444176L, 0.725464L
    };
    static const long double expected_corr10[GN_BASE10_EXPONENT_COUNT] = {
        -0.4081L, -0.5169L, -0.4925L, -0.4192L
    };
    static const int expected_primes[GN_PRIME_BASE_COUNT] = {
        348504, 348498, 348483, 348474, 348452,
        348441, 348414, 348367, 348351, 348294
    };
    static const int expected_active[GN_PRIME_BASE_COUNT] = {
        8, 18, 50, 72, 128, 162, 242, 392, 450, 648
    };
    static const long double expected_corr[GN_PRIME_BASE_COUNT] = {
        -0.4747L, -0.2227L, -0.2689L, -0.3185L, -0.3568L,
        -0.1858L, -0.2498L, -0.2119L, -0.2534L, -0.2408L
    };
    static const long double expected_actual[GN_PRIME_BASE_COUNT] = {
        0.9252L, 1.9324L, 1.8263L, 3.4569L, 2.4026L,
        3.9673L, 2.2264L, 6.8818L, 6.5765L, 7.9385L
    };
    static const long double expected_mean[GN_PRIME_BASE_COUNT] = {
        0.1118L, -0.1316L, -0.0707L, -0.0250L, -0.0312L,
        -0.0530L, 0.0082L, 0.0207L, -0.0129L, 0.0072L
    };
    static const long double expected_sd[GN_PRIME_BASE_COUNT] = {
        0.4248L, 0.9646L, 1.2893L, 1.4779L, 1.6801L,
        1.7144L, 1.8986L, 2.1879L, 2.2742L, 2.5009L
    };
    static const long double expected_z[GN_PRIME_BASE_COUNT] = {
        1.91L, 2.14L, 1.47L, 2.36L, 1.45L,
        2.34L, 1.17L, 3.14L, 2.90L, 3.17L
    };
    int prime_count = 0;
    int *primes = gn_prime_list(GN_MAX_CUTOFF, &prime_count);
    GNBaseTenRow base10[GN_BASE10_EXPONENT_COUNT];
    GNPrimeBaseRow prime_rows[GN_PRIME_BASE_COUNT];
    long double zero_residual = 0.0L;
    if (!primes || !gn_base10_rows(primes, prime_count, base10,
                                   &zero_residual) ||
        !gn_prime_base_rows(primes, prime_count, prime_rows)) {
        free(primes);
        return 0;
    }
    int ok = zero_residual < GN_ACTIVE_TOLERANCE;
    if (print) {
        printf("Reference finite character data\n\n");
        printf("Base-ten active-character signs, cutoff 5000000\n");
        printf(" sigma  positive negative zero       net  correlation  check\n");
    }
    for (int e = 0; e < GN_BASE10_EXPONENT_COUNT; e++) {
        int row_ok = base10[e].prime_count == 348488 &&
            base10[e].positive == expected_pos[e] &&
            base10[e].negative == expected_neg[e] &&
            base10[e].exact_zero == 3 &&
            fabsl(base10[e].net - expected_net[e]) < 5.1e-7L &&
            fabsl(base10[e].correlation - expected_corr10[e]) < 5.1e-5L &&
            base10[e].decomposition_error < 2.0e-12L;
        ok &= row_ok;
        if (print)
            printf("  %.1Lf %9d %8d %4d %+9.6Lf %+11.4Lf  %s\n",
                   gn_base10_exponents[e], base10[e].positive,
                   base10[e].negative, base10[e].exact_zero,
                   base10[e].net, base10[e].correlation,
                   row_ok ? "PASS" : "FAIL");
    }
    if (print) {
        printf("\nPrime-base magnitude correlations at exponent 1/2\n");
        printf(" base   primes retained correlation  check\n");
    }
    for (int i = 0; i < GN_PRIME_BASE_COUNT; i++) {
        int row_ok = prime_rows[i].prime_count == expected_primes[i] &&
            prime_rows[i].active == expected_active[i] &&
            fabsl(prime_rows[i].correlation - expected_corr[i]) < 5.1e-5L &&
            prime_rows[i].decomposition_error < 2.0e-11L;
        ok &= row_ok;
        if (print)
            printf(" %4d %8d %8d %+11.4Lf  %s\n",
                   prime_rows[i].base, prime_rows[i].prime_count,
                   prime_rows[i].active, prime_rows[i].correlation,
                   row_ok ? "PASS" : "FAIL");
    }
    if (print) {
        printf("\nAssignment-null moments at exponent 1/2\n");
        printf(" base   actual expected  stddev     z  check\n");
    }
    for (int i = 0; i < GN_PRIME_BASE_COUNT; i++) {
        int row_ok = fabsl(prime_rows[i].actual - expected_actual[i]) < 5.1e-5L &&
            fabsl(prime_rows[i].expected - expected_mean[i]) < 5.1e-5L &&
            fabsl(prime_rows[i].standard_deviation - expected_sd[i]) < 5.1e-5L &&
            fabsl(prime_rows[i].z - expected_z[i]) < 5.1e-3L;
        ok &= row_ok;
        if (print)
            printf(" %4d %+8.4Lf %+8.4Lf %7.4Lf %+5.2Lf  %s\n",
                   prime_rows[i].base, prime_rows[i].actual,
                   prime_rows[i].expected,
                   prime_rows[i].standard_deviation, prime_rows[i].z,
                   row_ok ? "PASS" : "FAIL");
    }
    if (print) {
        printf("\nAll three reference finite tables reproduced to displayed precision.\n");
        printf("These are finite numerical fixtures, not convergence evidence.\n");
        printf("Result  %s\n", ok ? "PASS" : "FAIL");
    }
    free(primes);
    return ok;
}

int compatible_residue_channels_snapshot(void)
{
    return gn_snapshot_ok(1) ? 0 : 1;
}

static void gn_audit_failure(GNExactAudit *audit)
{
    audit->failures++;
}

static void gn_audit_table(const CollisionCenteredTable *table,
                           GNExactAudit *audit)
{
    long long raw_total = 0;
    long long centered_total = 0;
    for (int fiber = 0; fiber < table->base; fiber++) {
        long long sum = 0;
        int expected = collision_table_gcd(fiber, table->base) == 1
            ? table->fiber_size : 0;
        for (int a = 1; a < table->modulus; a++)
            if (collision_table_gcd(a, table->modulus) == 1 &&
                a % table->base == fiber)
                sum += table->centered_numerator[a];
        audit->fiber_cases++;
        if (table->fiber_count[fiber] != expected || sum != 0)
            gn_audit_failure(audit);
    }
    for (int a = 1; a < table->modulus; a++) {
        if (collision_table_gcd(a, table->modulus) != 1) continue;
        int reflected = table->modulus - a;
        audit->reflection_cases++;
        raw_total += table->value[a];
        centered_total += table->centered_numerator[a];
        if (table->value[a] + table->value[reflected] != -1 ||
            table->centered_numerator[a] +
                table->centered_numerator[reflected] != 0)
            gn_audit_failure(audit);
    }
    if (2 * raw_total != -table->phi || centered_total != 0)
        gn_audit_failure(audit);
}

static void gn_audit_internal(const CollisionCenteredTable *table,
                              GNExactAudit *audit)
{
    static const int primes[] = {3, 5, 7, 11, 13, 17, 19};
    for (size_t qi = 0; qi < sizeof(primes) / sizeof(primes[0]); qi++) {
        int q = primes[qi];
        int fixed = (table->modulus % q) * ((q + 1) / 2) % q;
        int count = 0;
        long long raw = 0, centered = 0;
        for (int a = 1; a < table->modulus; a++) {
            if (collision_table_gcd(a, table->modulus) != 1 ||
                a % q != fixed) continue;
            count++;
            raw += table->value[a];
            centered += table->centered_numerator[a];
        }
        audit->internal_pairs++;
        if (table->base % q != 0) audit->internal_nondividing_pairs++;
        if (count == 0) {
            audit->internal_empty++;
            if (table->base % q == 0) audit->internal_dividing_empty++;
            else audit->internal_nondividing_empty++;
        } else {
            audit->internal_nonempty++;
            if (2 * raw != -count || centered != 0)
                gn_audit_failure(audit);
        }
    }
}

static void gn_audit_channels(const CollisionCenteredTable *table,
                              int channel_modulus, int simultaneous,
                              GNExactAudit *audit)
{
    int *count = NULL;
    long long *raw = NULL, *centered = NULL;
    int joint = 0;
    if (!gn_channel_sums(table, channel_modulus, &count, &raw,
                         &centered, &joint)) {
        gn_audit_failure(audit);
        return;
    }
    int shared = collision_table_gcd(table->base, channel_modulus);
    int expected = simultaneous
        ? table->phi / gn_phi(shared)
        : (table->base % channel_modulus == 0
            ? table->phi / (channel_modulus - 1) : table->phi);
    if (simultaneous) audit->simultaneous_pairs++;
    else audit->external_pairs++;
    for (int residue = 1; residue < channel_modulus; residue++) {
        if (collision_table_gcd(residue, channel_modulus) != 1) continue;
        if (simultaneous) audit->simultaneous_channels++;
        else audit->external_channels++;
        int ok = count[residue] == expected && centered[residue] == 0;
        if (shared == 1) ok &= 2 * raw[residue] == -count[residue];
        if (!ok) gn_audit_failure(audit);
    }
    free(count);
    free(raw);
    free(centered);
}

static void gn_report(const char *label, int ok, int *passed)
{
    printf("  %-68s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int compatible_residue_channels_verify(void)
{
    static const int external_primes[] = {2, 3, 5, 7, 11, 13, 17, 19};
    static const int squarefree[] = {6, 30, 105, 210};
    GNExactAudit audit = {0};
    for (int base = 2; base <= 20; base++) {
        CollisionCenteredTable table;
        if (!collision_centered_table_build(base, 1, &table)) {
            gn_audit_failure(&audit);
            continue;
        }
        gn_audit_table(&table, &audit);
        gn_audit_internal(&table, &audit);
        for (size_t i = 0;
             i < sizeof(external_primes) / sizeof(external_primes[0]); i++)
            gn_audit_channels(&table, external_primes[i], 0, &audit);
        for (size_t i = 0;
             i < sizeof(squarefree) / sizeof(squarefree[0]); i++)
            gn_audit_channels(&table, squarefree[i], 1, &audit);
        collision_centered_table_free(&table);
    }
    int exact_counts = audit.reflection_cases == 1744 &&
        audit.fiber_cases == 209 && audit.internal_pairs == 133 &&
        audit.internal_nondividing_pairs == 117 &&
        audit.internal_nonempty == 101 && audit.internal_empty == 32 &&
        audit.internal_nondividing_empty == 16 &&
        audit.internal_dividing_empty == 16 &&
        audit.external_pairs == 152 && audit.external_channels == 1311 &&
        audit.simultaneous_pairs == 76 &&
        audit.simultaneous_channels == 2014;
    int snapshot = gn_snapshot_ok(0);
    int passed = 0;
    printf("Compatible residue channel verification\n\n");
    printf("Exact lag-one scope: bases 2 through 20.\n");
    printf("reflection=%d; fibers=%d; internal=%d; true channels=%d; simultaneous=%d\n\n",
           audit.reflection_cases, audit.fiber_cases, audit.internal_pairs,
           audit.external_channels, audit.simultaneous_channels);
    gn_report("raw reflection and centered fiber identities",
              audit.failures == 0, &passed);
    gn_report("internal fixed slices, including empty slices",
              audit.failures == 0 && audit.internal_nonempty == 101,
              &passed);
    gn_report("all prime channels, including q=2 and primes dividing the base",
              audit.failures == 0 && audit.external_channels == 1311,
              &passed);
    gn_report("all channels for squarefree moduli 6, 30, 105, and 210",
              audit.failures == 0 && audit.simultaneous_channels == 2014,
              &passed);
    gn_report("reference exact audit counts", exact_counts, &passed);
    gn_report("three reference finite character and assignment tables",
              snapshot, &passed);
    printf("\n%d/6 verification groups passed.\n", passed);
    printf("Channel neutrality is exact finite arithmetic. Mertens' theorem in\n");
    printf("arithmetic progressions is the external analytic input for convergence\n");
    printf("at one. Character signs, correlations, and assignment moments are finite\n");
    printf("numerical data. Convergence below one remains open.\n");
    return passed == 6;
}

void compatible_residue_channels_help(void)
{
    printf(
        "Compatible residue channels\n\n"
        "Inspect internal residue slices, true prime channels, simultaneous\n"
        "squarefree channels, and their finite character coordinates.\n\n"
        "Exact finite arithmetic\n"
        "  nfield compatible-residue-channels inspect <integer> <prime>\n"
        "                                      [--base <b>] [--lag <ell>]\n"
        "      Show n=m*t+a, its internal representative class, the quotient\n"
        "      shift, and the reconstructed true residue modulo the prime.\n\n"
        "  nfield compatible-residue-channels internal <prime>\n"
        "                                      [--base <b>] [--lag <ell>]\n"
        "      Check the reflection-fixed canonical slice. The prime must be odd\n"
        "      and must not divide the base. Empty fixed slices are reported.\n\n"
        "  nfield compatible-residue-channels channels <prime>\n"
        "                                      [--base <b>] [--lag <ell>]\n"
        "      Lift the table to lcm(b^(ell+1),prime) and check every true nonzero\n"
        "      residue channel, including prime two and primes dividing the base.\n\n"
        "  nfield compatible-residue-channels simultaneous <squarefree>\n"
        "                                      [--base <b>] [--lag <ell>]\n"
        "      Check all unit channels modulo one squarefree modulus at once.\n\n"
        "Finite numerical ledgers\n"
        "  nfield compatible-residue-channels character-signs [--cutoff <X>]\n"
        "  nfield compatible-residue-channels magnitude-correlations [--cutoff <X>]\n"
        "  nfield compatible-residue-channels assignment-null [--cutoff <X>]\n"
        "      Recompute declared finite character data. The default cutoff is\n"
        "      5000000, matching the reference fixtures. Smaller cutoffs explore\n"
        "      the same definitions away from those fixtures.\n\n"
        "Reference fixtures and focused verification\n"
        "  nfield compatible-residue-channels snapshot\n"
        "  nfield compatible-residue-channels verify\n"
        "  nfield verify compatible-residue-channels\n\n"
        "The channel sums and finite decompositions are exact identities. Complex\n"
        "character transforms and prime weights use long-double arithmetic with\n"
        "a direct-sum cross-check. Character signs and correlations are bounded\n"
        "numerical data. Mertens' theorem in arithmetic progressions is the external\n"
        "analytic input for convergence at one. Convergence below one remains open.\n"
    );
}
