/* Exact all-lag finite-determination and optimal-base-power checks. */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "nfield.h"

static int fd_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0) return 0;
    return 1;
}

static int fd_totient(int modulus)
{
    int count = 0;
    for (int residue = 1; residue < modulus; residue++)
        count += collision_table_gcd(residue, modulus) == 1;
    return count;
}

int finite_determination_compare(int integer, int base, int lag,
                                 int *table_value, int *direct_value)
{
    int modulus = 0;
    int collision = 0;
    int multiplier = 0;
    if (!table_value || !direct_value ||
        !collision_table_modulus(base, lag, &modulus) ||
        integer < 2 || collision_table_gcd(integer, base) != 1 ||
        !collision_table_value(base, lag, integer % modulus, table_value) ||
        !collision_table_direct_deviation(
            integer, base, lag, &collision, direct_value, &multiplier))
        return 0;
    return 1;
}

static int fd_slice_bridge_model(
    int integer, int base, int lag,
    int *transport_ok, int *diagonal_ok, int *endpoint_ok,
    int *direct_collision, int *slice_collision, int *diagonal_count)
{
    int modulus = 0;
    if (!transport_ok || !diagonal_ok || !endpoint_ok ||
        !direct_collision || !slice_collision || !diagonal_count ||
        integer < 2 ||
        !collision_table_modulus(base, lag, &modulus) ||
        collision_table_gcd(integer, base) != 1)
        return 0;

    int base_power = modulus / base;
    int middle_count = base_power / base;
    unsigned char *diagonal = calloc((size_t)modulus, 1);
    if (!diagonal) return 0;

    *transport_ok = 1;
    *diagonal_ok = 1;
    *endpoint_ok = 1;
    *direct_collision = 0;
    *slice_collision = -1;
    *diagonal_count = 0;

    for (int digit = 0; digit < base; digit++) {
        for (int middle = 0; middle < middle_count; middle++) {
            int index = digit * (base_power + 1) + base * middle;
            if (index < 0 || index >= modulus || diagonal[index]) {
                *diagonal_ok = 0;
                continue;
            }
            diagonal[index] = 1;
            (*diagonal_count)++;
        }
    }
    if (*diagonal_count != base_power) *diagonal_ok = 0;
    for (int index = 0; index < modulus; index++) {
        int intrinsic = index / base_power == index % base;
        if ((diagonal[index] != 0) != intrinsic) *diagonal_ok = 0;
    }
    if (!diagonal[0] || !diagonal[modulus - 1]) *endpoint_ok = 0;

    for (int residue = 1; residue < integer; residue++) {
        int64_t slice_numerator = (int64_t)modulus * residue;
        int slice = (int)(slice_numerator / integer);
        int original_digit =
            (int)((int64_t)base * residue / integer);
        int64_t product = (int64_t)base_power * residue;
        int quotient = (int)(product / integer);
        int transported = (int)(product % integer);
        int transported_digit =
            (int)((int64_t)base * transported / integer);
        if (transported == 0 ||
            original_digit != slice / base_power ||
            (int64_t)modulus * residue !=
                (int64_t)base * quotient * integer +
                    (int64_t)base * transported ||
            slice != base * quotient + transported_digit ||
            transported_digit != slice % base ||
            (original_digit == transported_digit) != (diagonal[slice] != 0))
            *transport_ok = 0;
        *direct_collision += original_digit == transported_digit;
    }

    for (int index = 0; index < modulus; index++) {
        if (!diagonal[index]) continue;
        *slice_collision +=
            (int)((int64_t)(index + 1) * integer / modulus) -
            (int)((int64_t)index * integer / modulus);
    }

    free(diagonal);
    return 1;
}

int finite_determination_slice_values(
    int integer, int base, int lag,
    int *direct_collision, int *slice_collision,
    int *diagonal_count, int *structure_ok)
{
    int transport = 0;
    int diagonal = 0;
    int endpoints = 0;
    if (!structure_ok ||
        !fd_slice_bridge_model(
            integer, base, lag, &transport, &diagonal, &endpoints,
            direct_collision, slice_collision, diagonal_count))
        return 0;
    *structure_ok = transport && diagonal && endpoints &&
                    *direct_collision == *slice_collision;
    return 1;
}

int finite_determination_inspect(int integer, int base, int lag)
{
    int modulus = 0;
    int table_value = 0;
    int direct_value = 0;
    int transport = 0;
    int diagonal = 0;
    int endpoints = 0;
    int direct_collision = 0;
    int slice_collision = 0;
    int diagonal_count = 0;
    if (!collision_table_modulus(base, lag, &modulus)) {
        fprintf(stderr, "base and lag must give a modulus not exceeding 2000000\n");
        return 1;
    }
    if (integer < 2) {
        fprintf(stderr, "finite determination requires N >= 2\n");
        return 1;
    }
    if (collision_table_gcd(integer, base) != 1) {
        fprintf(stderr, "N must be coprime to the base\n");
        return 1;
    }
    if (!finite_determination_compare(
            integer, base, lag, &table_value, &direct_value))
        return 1;
    if (!fd_slice_bridge_model(
            integer, base, lag, &transport, &diagonal, &endpoints,
            &direct_collision, &slice_collision, &diagonal_count))
        return 1;
    int residue = integer % modulus;
    int ok = transport && diagonal && endpoints &&
             direct_collision == slice_collision &&
             table_value == direct_value;
    printf("Finite-determination theorem\n\n");
    printf("  N=%d base=%d lag=%d\n", integer, base, lag);
    printf("  determining modulus b^(lag+1)=%d\n", modulus);
    printf("  diagonal slices=%d; expected b^lag=%d         %s\n",
           diagonal_count, modulus / base,
           diagonal ? "PASS" : "FAIL");
    printf("  diagonal endpoints 0 and m-1                 %s\n",
           endpoints ? "PASS" : "FAIL");
    printf("  pointwise digit and slice transport           %s\n",
           transport ? "PASS" : "FAIL");
    printf("  direct collision count=%d; slice score=%d     %s\n",
           direct_collision, slice_collision,
           direct_collision == slice_collision ? "PASS" : "FAIL");
    printf("  unit residue [N]_m=%d\n", residue);
    printf("  direct collision deviation S_l(N)=%d\n", direct_value);
    printf("  exact finite-table value S_l([N]_m)=%d  %s\n",
           table_value, ok ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int finite_determination_optimal(int base, int lag)
{
    int modulus = 0;
    if (!collision_table_modulus(base, lag, &modulus)) {
        fprintf(stderr, "base and lag must give a modulus not exceeding 2000000\n");
        return 1;
    }
    int base_power = modulus / base;
    int first = 1;
    int second = modulus - base_power + 1;
    int first_value = 0;
    int second_value = 0;
    int expected_second = -(base - 1) * (base_power / base);
    int ok = collision_table_value(base, lag, first, &first_value) &&
             collision_table_value(base, lag, second, &second_value) &&
             first % base_power == second % base_power &&
             first_value == 0 && second_value == expected_second;
    printf("Optimal base power\n\n");
    printf("  base=%d lag=%d B=b^lag=%d m=b^(lag+1)=%d\n",
           base, lag, base_power, modulus);
    printf("  classes a=1 and a'=m-B+1=%d\n", second);
    printf("  same residue modulo B=%d                      %s\n",
           first % base_power,
           first % base_power == second % base_power ? "PASS" : "FAIL");
    printf("  S_l(1)=%d; expected 0                         %s\n",
           first_value, first_value == 0 ? "PASS" : "FAIL");
    printf("  S_l(a')=%d; expected %d                       %s\n",
           second_value, expected_second,
           second_value == expected_second ? "PASS" : "FAIL");
    printf("\nNo smaller power b^k with k<=lag determines the table.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int fd_declared_lag_one(int *instances, int *classes)
{
    static const int bases[] = {3, 5, 7, 10};
    int failures = 0;
    *instances = 0;
    *classes = 0;
    for (size_t base_index = 0;
         base_index < sizeof(bases) / sizeof(bases[0]); base_index++) {
        int base = bases[base_index];
        int modulus = base * base;
        unsigned char *seen = calloc((size_t)modulus, 1);
        if (!seen) return 1;
        for (int prime = modulus + 1; prime <= 5000; prime++) {
            int table_value = 0;
            int direct_value = 0;
            if (!fd_is_prime(prime) || prime % base == 0) continue;
            (*instances)++;
            if (!finite_determination_compare(
                    prime, base, 1, &table_value, &direct_value) ||
                table_value != direct_value)
                failures++;
            seen[prime % modulus] = 1;
        }
        for (int residue = 1; residue < modulus; residue++) {
            if (collision_table_gcd(residue, modulus) != 1) continue;
            if (seen[residue]) (*classes)++;
            else failures++;
        }
        free(seen);
    }
    return failures;
}

static int fd_declared_base_three(int *instances)
{
    int failures = 0;
    *instances = 0;
    for (int lag = 1; lag <= 3; lag++) {
        int modulus = 0;
        collision_table_modulus(3, lag, &modulus);
        for (int prime = modulus + 1; prime <= 8000; prime++) {
            int table_value = 0;
            int direct_value = 0;
            if (!fd_is_prime(prime) || prime % 3 == 0) continue;
            (*instances)++;
            if (!finite_determination_compare(
                    prime, 3, lag, &table_value, &direct_value) ||
                table_value != direct_value)
                failures++;
        }
    }
    return failures;
}

static int fd_all_size_sweep(int *instances)
{
    int failures = 0;
    *instances = 0;
    for (int base = 2; base <= 16; base++) {
        for (int lag = 1; lag <= 4; lag++) {
            int modulus = 0;
            if (!collision_table_modulus(base, lag, &modulus)) continue;
            int maximum = modulus + 50;
            if (maximum > 500) maximum = 500;
            for (int integer = 2; integer <= maximum; integer++) {
                int table_value = 0;
                int direct_value = 0;
                if (collision_table_gcd(integer, base) != 1) continue;
                (*instances)++;
                if (!finite_determination_compare(
                        integer, base, lag, &table_value, &direct_value) ||
                    table_value != direct_value)
                    failures++;
            }
        }
    }
    return failures;
}

static int fd_slice_bridge_sweep(int *instances)
{
    int failures = 0;
    *instances = 0;
    for (int base = 2; base <= 16; base++) {
        for (int lag = 1; lag <= 4; lag++) {
            int modulus = 0;
            if (!collision_table_modulus(base, lag, &modulus)) continue;
            int maximum = modulus + 50;
            if (maximum > 500) maximum = 500;
            for (int integer = 2; integer <= maximum; integer++) {
                if (collision_table_gcd(integer, base) != 1) continue;
                int transport = 0;
                int diagonal = 0;
                int endpoints = 0;
                int direct_collision = 0;
                int slice_collision = 0;
                int diagonal_count = 0;
                (*instances)++;
                if (!fd_slice_bridge_model(
                        integer, base, lag, &transport, &diagonal,
                        &endpoints, &direct_collision, &slice_collision,
                        &diagonal_count) ||
                    !transport || !diagonal || !endpoints ||
                    direct_collision != slice_collision)
                    failures++;
            }
        }
    }
    return failures;
}

int finite_determination_verify(void)
{
    int lag_one_instances = 0;
    int represented_classes = 0;
    int base_three_instances = 0;
    int all_size_instances = 0;
    int slice_bridge_instances = 0;
    int lag_one_failures =
        fd_declared_lag_one(&lag_one_instances, &represented_classes);
    int base_three_failures = fd_declared_base_three(&base_three_instances);
    int all_size_failures = fd_all_size_sweep(&all_size_instances);
    int slice_bridge_failures =
        fd_slice_bridge_sweep(&slice_bridge_instances);
    int expected_classes = fd_totient(9) + fd_totient(25) +
                           fd_totient(49) + fd_totient(100);
    int optimal_failures = 0;
    int optimal_models = 0;
    for (int base = 2; base <= 16; base++) {
        for (int lag = 1; lag <= 4; lag++) {
            int modulus = 0;
            if (!collision_table_modulus(base, lag, &modulus)) continue;
            int base_power = modulus / base;
            int first_value = 0;
            int second_value = 0;
            int second = modulus - base_power + 1;
            int expected = -(base - 1) * (base_power / base);
            optimal_models++;
            if (!collision_table_value(base, lag, 1, &first_value) ||
                !collision_table_value(base, lag, second, &second_value) ||
                first_value != 0 || second_value != expected)
                optimal_failures++;
        }
    }
    int lag_one_count = lag_one_instances == 2623;
    int lag_one_values = lag_one_failures == 0;
    int class_coverage = represented_classes == expected_classes;
    int base_three_count = base_three_instances == 2986;
    int base_three_values = base_three_failures == 0;
    int optimal = optimal_failures == 0;
    int all_size = all_size_failures == 0 && all_size_instances > 0;
    int slice_bridge = slice_bridge_failures == 0 &&
                       slice_bridge_instances == all_size_instances;
    int passed = lag_one_count + lag_one_values + class_coverage +
                 base_three_count + base_three_values + optimal + all_size +
                 slice_bridge;

    printf("Finite-determination verification\n\n");
    printf("  lag-one prime instances=%d; expected 2623       %s\n",
           lag_one_instances, lag_one_count ? "PASS" : "FAIL");
    printf("  four-base direct/table comparisons               %s\n",
           lag_one_values ? "PASS" : "FAIL");
    printf("  represented unit classes=%d; expected %d        %s\n",
           represented_classes, expected_classes,
           class_coverage ? "PASS" : "FAIL");
    printf("  base-three all-lag instances=%d; expected 2986  %s\n",
           base_three_instances, base_three_count ? "PASS" : "FAIL");
    printf("  base-three lags one through three                %s\n",
           base_three_values ? "PASS" : "FAIL");
    printf("  optimal-base-power models=%d                     %s\n",
           optimal_models, optimal ? "PASS" : "FAIL");
    printf("  all-size quotient-zero and positive-quotient instances=%d  %s\n",
           all_size_instances, all_size ? "PASS" : "FAIL");
    printf("  pointwise slice bridge and endpoint correction=%d  %s\n",
           slice_bridge_instances, slice_bridge ? "PASS" : "FAIL");
    printf("\n%d/8 verification groups passed.\n", passed);
    printf("Computed  exact integer comparisons over the declared finite ranges.\n");
    printf("Proof boundary  the universal direct/table bridge and finite\n");
    printf("determination are proved separately; bounded sweeps are corroboration.\n");
    return passed == 8;
}

void finite_determination_help(void)
{
    printf(
        "Finite determination\n\n"
        "Commands\n"
        "  nfield finite-determination inspect <N> [--base <b>] [--lag <ell>]\n"
        "      Compare the direct collision deviation with its residue-table value.\n"
        "  nfield finite-determination optimal [--base <b>] [--lag <ell>]\n"
        "      Display the two witness classes for the optimal-base-power test.\n"
        "  nfield finite-determination verify\n"
        "  nfield verify finite-determination\n\n"
        "Scope\n"
        "  object             pointwise slice bridge, all-lag residue table, and\n"
        "                     optimal base power.\n"
        "  mathematical scope for every N>=2 coprime to b, S_ell(N) depends only\n"
        "                     on N modulo b^(ell+1), and\n"
        "                     no smaller power of b determines the whole table.\n"
        "  exact computation 2623 declared lag-one prime instances, every unit\n"
        "                     class, and 2986 base-three all-lag instances.\n"
        "  boundary           the sweeps are independent finite checks, not the\n"
        "                     universal proof for arbitrary eligible integers.\n"
    );
}
