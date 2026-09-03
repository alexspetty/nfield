/* Exact collision labels for primes inside and outside the base support. */

#include <stdint.h>
#include <stdio.h>

#include "nfield.h"

#define ALL_PRIME_LABEL_MAX_PRIME 100000

static int apcl_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0) return 0;
    return 1;
}

static int apcl_power_mod(int base, int exponent, int modulus)
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

static int apcl_direct_deviation(int prime, int base, int lag,
                                 int *deviation)
{
    if (!deviation || !apcl_is_prime(prime) || prime > ALL_PRIME_LABEL_MAX_PRIME ||
        base < 2 || lag < 1)
        return 0;
    int multiplier = apcl_power_mod(base, lag, prime);
    int collision = 0;
    for (int residue = 1; residue < prime; residue++) {
        int image = (int)((int64_t)multiplier * residue % prime);
        int digit = (int)((int64_t)base * residue / prime);
        int image_digit = (int)((int64_t)base * image / prime);
        collision += digit == image_digit;
    }
    *deviation = collision - (prime - 1) / base;
    return 1;
}

int all_prime_collision_label_value(int prime, int base, int lag,
                                    int *direct_label, int *table_label,
                                    int *uses_unit_table)
{
    int modulus = 0;
    if (!direct_label || !table_label || !uses_unit_table ||
        !apcl_is_prime(prime) || prime > ALL_PRIME_LABEL_MAX_PRIME ||
        !collision_table_modulus(base, lag, &modulus) ||
        !apcl_direct_deviation(prime, base, lag, direct_label))
        return 0;
    if (base % prime == 0) {
        *uses_unit_table = 0;
        *table_label = 0;
        return 1;
    }
    *uses_unit_table = 1;
    return collision_table_value(
        base, lag, prime % modulus, table_label);
}

int all_prime_collision_label_inspect(int prime, int base, int lag)
{
    int modulus = 0;
    int direct = 0;
    int table = 0;
    int uses_table = 0;
    if (!apcl_is_prime(prime)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (!collision_table_modulus(base, lag, &modulus)) {
        fprintf(stderr, "base and lag must give a modulus not exceeding 2000000\n");
        return 1;
    }
    if (!all_prime_collision_label_value(
            prime, base, lag, &direct, &table, &uses_table))
        return 1;
    int ok = uses_table ? direct == table : direct == 0;
    printf("All-prime collision label\n\n");
    printf("  prime=%d base=%d lag=%d modulus=%d\n",
           prime, base, lag, modulus);
    printf("  direct collision label=%d\n", direct);
    if (uses_table) {
        printf("  prime is a unit modulo b^(lag+1)\n");
        printf("  finite-table residue=%d label=%d  %s\n",
               prime % modulus, table, direct == table ? "PASS" : "FAIL");
    } else {
        printf("  prime divides the base\n");
        printf("  exact exceptional label=0          %s\n",
               direct == 0 ? "PASS" : "FAIL");
    }
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int all_prime_collision_label_verify(void)
{
    int models = 0;
    int unit_models = 0;
    int base_prime_models = 0;
    int unit_failures = 0;
    int base_prime_failures = 0;
    for (int base = 2; base <= 40; base++) {
        for (int lag = 1; lag <= 4; lag++) {
            int modulus = 0;
            if (!collision_table_modulus(base, lag, &modulus)) continue;
            for (int prime = 2; prime <= 257; prime++) {
                int direct = 0;
                int table = 0;
                int uses_table = 0;
                if (!apcl_is_prime(prime)) continue;
                models++;
                if (!all_prime_collision_label_value(
                        prime, base, lag, &direct, &table, &uses_table)) {
                    unit_failures++;
                    continue;
                }
                if (uses_table) {
                    unit_models++;
                    if (direct != table) unit_failures++;
                } else {
                    base_prime_models++;
                    if (direct != 0) base_prime_failures++;
                }
            }
        }
    }
    int coverage = models > 0 && unit_models > 0 && base_prime_models > 0;
    int units = unit_failures == 0;
    int supported = base_prime_failures == 0;
    int passed = coverage + units + supported;
    printf("All-prime collision-label verification\n\n");
    printf("  models=%d; unit-table=%d; base-prime=%d        %s\n",
           models, unit_models, base_prime_models,
           coverage ? "PASS" : "FAIL");
    printf("  every prime outside the base support uses its finite table  %s\n",
           units ? "PASS" : "FAIL");
    printf("  every tested prime dividing the base has exact label zero   %s\n",
           supported ? "PASS" : "FAIL");
    printf("\n%d/3 verification groups passed.\n", passed);
    printf("Computed  direct long-division labels and table values use exact integers.\n");
    printf("Theorem boundary  the universal two-case identity is proved separately.\n");
    return passed == 3;
}

void all_prime_collision_label_help(void)
{
    printf(
        "All-prime collision label\n\n"
        "Commands\n"
        "  nfield all-prime-collision-label inspect <p> [--base <b>] [--lag <ell>]\n"
        "      Compare one direct prime label with the unit table, or check the\n"
        "      exact zero label when the prime divides the base.\n"
        "  nfield all-prime-collision-label verify\n"
        "  nfield verify all-prime-collision-label\n\n"
        "Scope\n"
        "  proved             every prime has a collision label; non-base primes\n"
        "                     use the finite unit table and base primes equal zero.\n"
        "  exact computation primes through 257, bases 2 through 40, and all\n"
        "                     supported lags one through four.\n"
        "  boundary           the bounded sweep checks exact instances; it does\n"
        "                     not replace the universal two-case proof.\n"
    );
}
