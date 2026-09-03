/* Exact finite-table reflection identity and grand-mean checks. */

#include <stdio.h>
#include <stdint.h>

#include "nfield.h"

static int ri_floor_jump(int modulus, int residue, int index)
{
    return (int)((int64_t)(index + 1) * residue / modulus) -
           (int)((int64_t)index * residue / modulus);
}

static int ri_local_model(
    int base, int lag, int residue,
    int *interior_ok, int *endpoints_ok, int *quotient_ok,
    int *interior_count)
{
    int modulus = 0;
    if (!interior_ok || !endpoints_ok || !quotient_ok ||
        !interior_count ||
        !collision_table_modulus(base, lag, &modulus) ||
        residue <= 0 || residue >= modulus ||
        collision_table_gcd(residue, modulus) != 1)
        return 0;

    int reflected = modulus - residue;
    *interior_ok = 1;
    *endpoints_ok = 1;
    *quotient_ok = 1;
    *interior_count = 0;
    for (int index = 1; index <= modulus - 2; index++) {
        int left =
            (int)((int64_t)index * reflected / modulus);
        int right = index - 1 -
            (int)((int64_t)index * residue / modulus);
        if (left != right ||
            ri_floor_jump(modulus, residue, index) +
                ri_floor_jump(modulus, reflected, index) != 1)
            *interior_ok = 0;
        (*interior_count)++;
    }
    if (ri_floor_jump(modulus, residue, 0) != 0 ||
        ri_floor_jump(modulus, residue, modulus - 1) != 1 ||
        ri_floor_jump(modulus, reflected, 0) != 0 ||
        ri_floor_jump(modulus, reflected, modulus - 1) != 1)
        *endpoints_ok = 0;
    if (residue / base + reflected / base != modulus / base - 1)
        *quotient_ok = 0;
    return 1;
}

int reflection_identity_local_values(
    int base, int lag, int residue, int *interior_count, int *structure_ok)
{
    int interior = 0;
    int endpoints = 0;
    int quotient = 0;
    if (!structure_ok ||
        !ri_local_model(
            base, lag, residue, &interior, &endpoints, &quotient,
            interior_count))
        return 0;
    *structure_ok = interior && endpoints && quotient;
    return 1;
}

int reflection_identity_pair_values(int base, int lag, int residue,
                                    int *value, int *reflected_value)
{
    int modulus = 0;
    if (!value || !reflected_value ||
        !collision_table_modulus(base, lag, &modulus) ||
        residue <= 0 || residue >= modulus ||
        collision_table_gcd(residue, modulus) != 1)
        return 0;
    return collision_table_value(base, lag, residue, value) &&
           collision_table_value(
               base, lag, modulus - residue, reflected_value);
}

int reflection_identity_inspect(int base, int lag, int residue)
{
    int modulus = 0;
    int value = 0;
    int reflected = 0;
    int interior = 0;
    int endpoints = 0;
    int quotient = 0;
    int interior_count = 0;
    if (!collision_table_modulus(base, lag, &modulus)) {
        fprintf(stderr, "base and lag must give a modulus not exceeding 2000000\n");
        return 1;
    }
    if (!reflection_identity_pair_values(
            base, lag, residue, &value, &reflected)) {
        fprintf(stderr, "residue must be a positive unit below the table modulus\n");
        return 1;
    }
    if (!ri_local_model(
            base, lag, residue, &interior, &endpoints, &quotient,
            &interior_count))
        return 1;
    int ok = interior && endpoints && quotient && value + reflected == -1;
    printf("Reflection identity\n\n");
    printf("  base=%d lag=%d modulus=%d\n", base, lag, modulus);
    printf("  S_l(%d)=%d\n", residue, value);
    printf("  S_l(%d)=%d\n", modulus - residue, reflected);
    printf("  interior floor-complement identities=%d       %s\n",
           interior_count, interior ? "PASS" : "FAIL");
    printf("  endpoint jumps d_0=0 and d_(m-1)=1            %s\n",
           endpoints ? "PASS" : "FAIL");
    printf("  floor quotients sum to b^lag-1                %s\n",
           quotient ? "PASS" : "FAIL");
    printf("  reflected pair sum=%d; expected -1  %s\n",
           value + reflected, ok ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int reflection_identity_table(int base, int lag)
{
    int modulus = 0;
    if (!collision_table_modulus(base, lag, &modulus)) {
        fprintf(stderr, "base and lag must give a modulus not exceeding 2000000\n");
        return 1;
    }
    long long sum = 0;
    int count = 0;
    int failures = 0;
    for (int residue = 1; residue < modulus; residue++) {
        int value = 0;
        int reflected = 0;
        if (collision_table_gcd(residue, modulus) != 1) continue;
        if (!reflection_identity_pair_values(
                base, lag, residue, &value, &reflected) ||
            value + reflected != -1)
            failures++;
        sum += value;
        count++;
    }
    int mean_ok = 2 * sum == -(long long)count;
    int ok = failures == 0 && mean_ok;
    printf("Reflection table\n\n");
    printf("  base=%d lag=%d modulus=%d unit classes=%d\n",
           base, lag, modulus, count);
    printf("  reflection failures=%d                         %s\n",
           failures, failures == 0 ? "PASS" : "FAIL");
    printf("  2*sum S_l(a)=%lld; -phi(m)=%d                 %s\n",
           2 * sum, -count, mean_ok ? "PASS" : "FAIL");
    printf("  exact grand mean=-1/2                          %s\n",
           mean_ok ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int reflection_identity_verify(void)
{
    static const int bases[] = {3, 5, 7, 10};
    int pair_failures = 0;
    int mean_failures = 0;
    int local_failures = 0;
    int classes = 0;
    for (size_t index = 0; index < sizeof(bases) / sizeof(bases[0]);
         index++) {
        int modulus = bases[index] * bases[index];
        long long sum = 0;
        int count = 0;
        for (int residue = 1; residue < modulus; residue++) {
            int value = 0;
            int reflected = 0;
            if (collision_table_gcd(residue, modulus) != 1) continue;
            if (!reflection_identity_pair_values(
                    bases[index], 1, residue, &value, &reflected) ||
                value + reflected != -1)
                pair_failures++;
            int interior = 0;
            int endpoints = 0;
            int quotient = 0;
            int interior_count = 0;
            if (!ri_local_model(
                    bases[index], 1, residue, &interior, &endpoints,
                    &quotient, &interior_count) ||
                !interior || !endpoints || !quotient)
                local_failures++;
            sum += value;
            count++;
        }
        if (2 * sum != -(long long)count) mean_failures++;
        classes += count;
    }
    int class_count = classes == 108;
    int pairs = pair_failures == 0;
    int local = local_failures == 0;
    int means = mean_failures == 0;
    int passed = class_count + local + pairs + means;
    printf("Reflection-identity verification\n\n");
    printf("  every unit in four declared lag-one tables=%d  %s\n",
           classes, class_count ? "PASS" : "FAIL");
    printf("  S_l(a)+S_l(m-a)=-1 at every checked unit       %s\n",
           pairs ? "PASS" : "FAIL");
    printf("  local floor, endpoint, and quotient identities  %s\n",
           local ? "PASS" : "FAIL");
    printf("  exact grand mean -1/2 in every checked table   %s\n",
           means ? "PASS" : "FAIL");
    printf("\n%d/4 verification groups passed.\n", passed);
    printf("Computed  all table values and sums use exact integer arithmetic.\n");
    printf("Proof boundary  reflection and the mean are universal theorems;\n");
    printf("the declared finite tables are independent corroboration.\n");
    return passed == 4;
}

void reflection_identity_help(void)
{
    printf(
        "Reflection identity\n\n"
        "Commands\n"
        "  nfield reflection-identity inspect <a> [--base <b>] [--lag <ell>]\n"
        "      Check one exact reflected pair.\n"
        "  nfield reflection-identity table [--base <b>] [--lag <ell>]\n"
        "      Check every unit pair and the exact grand mean.\n"
        "  nfield reflection-identity verify\n"
        "  nfield verify reflection-identity\n\n"
        "Scope\n"
        "  mathematical scope local floor complement, endpoint jumps,\n"
        "                     S_ell(a)+S_ell(m-a)=-1, and exact mean -1/2.\n"
        "  exact computation every unit in the declared base 3, 5, 7, and 10\n"
        "                     lag-one tables, with no floating-point arithmetic.\n"
        "  boundary           finite tables check instances and do not prove\n"
        "                     the universal reflection identities.\n"
    );
}
