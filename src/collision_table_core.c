/*
 * collision_table_core.c
 *
 * Exact finite-table arithmetic shared by the collision fluctuation,
 * centered collision, and collision periodic-table companions.
 */

#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#define COLLISION_TABLE_MAX_MODULUS 2000000

int collision_table_gcd(int a, int b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int next = a % b;
        a = b;
        b = next;
    }
    return a;
}

int collision_table_modulus(int base, int lag, int *modulus)
{
    if (!modulus || base < 2 || base > 128 || lag < 1 || lag > 16)
        return 0;
    int64_t q = 1;
    for (int i = 0; i <= lag; i++) {
        q *= base;
        if (q > COLLISION_TABLE_MAX_MODULUS) return 0;
    }
    *modulus = (int)q;
    return 1;
}

int collision_table_value(int base, int lag, int residue, int *value)
{
    int modulus = 0;
    if (!value || !collision_table_modulus(base, lag, &modulus) ||
        residue <= 0 || residue >= modulus ||
        collision_table_gcd(residue, modulus) != 1)
        return 0;

    int leading_place = modulus / base;
    int middle_count = leading_place / base;
    int64_t total = -1 - residue / base;
    for (int digit = 0; digit < base; digit++) {
        for (int middle = 0; middle < middle_count; middle++) {
            int n = digit * leading_place + middle * base + digit;
            total += ((int64_t)(n + 1) * residue) / modulus;
            total -= ((int64_t)n * residue) / modulus;
        }
    }
    if (total < INT_MIN || total > INT_MAX) return 0;
    *value = (int)total;
    return 1;
}

static int collision_table_mod_pow(int base, int exponent, int modulus)
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

int collision_table_direct_deviation(int n, int base, int lag,
                                     int *collision, int *deviation,
                                     int *multiplier)
{
    int table_modulus = 0;
    if (!collision || !deviation || !multiplier || n < 2 ||
        !collision_table_modulus(base, lag, &table_modulus) ||
        collision_table_gcd(n, base) != 1)
        return 0;

    int mult = collision_table_mod_pow(base, lag, n);
    int count = 0;
    for (int r = 1; r < n; r++) {
        int image = (int)((int64_t)mult * r % n);
        int digit = (int)((int64_t)base * r / n);
        int image_digit = (int)((int64_t)base * image / n);
        count += digit == image_digit;
    }
    *collision = count;
    *deviation = count - (n - 1) / base;
    *multiplier = mult;
    return 1;
}

static long long collision_table_gcd_ll(long long a, long long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        long long next = a % b;
        a = b;
        b = next;
    }
    return a;
}

int collision_centered_table_build(int base, int lag,
                                   CollisionCenteredTable *table)
{
    int modulus = 0;
    if (!table || !collision_table_modulus(base, lag, &modulus)) return 0;

    memset(table, 0, sizeof(*table));
    table->base = base;
    table->lag = lag;
    table->modulus = modulus;
    table->fiber_size = modulus / base;
    table->value = calloc((size_t)modulus, sizeof(*table->value));
    table->fiber_sum = calloc((size_t)base, sizeof(*table->fiber_sum));
    table->fiber_count = calloc((size_t)base, sizeof(*table->fiber_count));
    table->centered_numerator =
        calloc((size_t)modulus, sizeof(*table->centered_numerator));
    if (!table->value || !table->fiber_sum || !table->fiber_count ||
        !table->centered_numerator) {
        collision_centered_table_free(table);
        return 0;
    }

    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1) continue;
        if (!collision_table_value(base, lag, a, &table->value[a])) {
            collision_centered_table_free(table);
            return 0;
        }
        int fiber = a % base;
        table->fiber_sum[fiber] += table->value[a];
        table->fiber_count[fiber]++;
        table->phi++;
    }

    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1) continue;
        int fiber = a % base;
        table->centered_numerator[a] =
            (long long)table->fiber_count[fiber] * table->value[a] -
            table->fiber_sum[fiber];
    }
    return 1;
}

void collision_centered_table_free(CollisionCenteredTable *table)
{
    if (!table) return;
    free(table->value);
    free(table->fiber_sum);
    free(table->fiber_count);
    free(table->centered_numerator);
    memset(table, 0, sizeof(*table));
}

int collision_centered_table_fraction(const CollisionCenteredTable *table,
                                      int residue,
                                      long long *numerator,
                                      long long *denominator)
{
    if (!table || !numerator || !denominator || residue <= 0 ||
        residue >= table->modulus ||
        collision_table_gcd(residue, table->modulus) != 1)
        return 0;
    int fiber = residue % table->base;
    long long num = table->centered_numerator[residue];
    long long den = table->fiber_count[fiber];
    long long divisor = collision_table_gcd_ll(num, den);
    if (divisor > 1) {
        num /= divisor;
        den /= divisor;
    }
    *numerator = num;
    *denominator = den;
    return 1;
}
