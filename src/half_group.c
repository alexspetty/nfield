/* Exact finite checks for the half-group wrapping theorem. */

#include <stdint.h>
#include <stdio.h>

#include "nfield.h"

#define HALF_GROUP_MAX_MODULUS 1000000

static int hg_valid(int modulus, int index, int report)
{
    if (modulus < 3 || modulus > HALF_GROUP_MAX_MODULUS) {
        if (report)
            fprintf(stderr, "m must be between 3 and %d\n",
                    HALF_GROUP_MAX_MODULUS);
        return 0;
    }
    if (index < 1 || index > modulus - 2) {
        if (report) fprintf(stderr, "n must satisfy 1 <= n <= m-2\n");
        return 0;
    }
    return 1;
}

static int hg_wraps(int modulus, int index, int unit)
{
    int coefficient = index + 1;
    int image = (int)((int64_t)coefficient * unit % modulus);
    return image < unit;
}

int half_group_cardinality(int modulus, int index,
                           int *wrapping_count, int *totient)
{
    if (!wrapping_count || !totient || !hg_valid(modulus, index, 0))
        return 0;
    int wraps = 0;
    int units = 0;
    for (int unit = 1; unit < modulus; unit++) {
        if (collision_table_gcd(unit, modulus) != 1) continue;
        units++;
        wraps += hg_wraps(modulus, index, unit);
    }
    *wrapping_count = wraps;
    *totient = units;
    return 1;
}

static int hg_reflection_model(
    int modulus, int index, int *identity_ok, int *complement_ok,
    int *unit_count)
{
    if (!identity_ok || !complement_ok || !unit_count ||
        !hg_valid(modulus, index, 0))
        return 0;
    *identity_ok = 1;
    *complement_ok = 1;
    *unit_count = 0;
    int coefficient = index + 1;
    for (int unit = 1; unit < modulus; unit++) {
        if (collision_table_gcd(unit, modulus) != 1) continue;
        int image = (int)((int64_t)coefficient * unit % modulus);
        int reflected_image =
            (int)((int64_t)coefficient * (modulus - unit) % modulus);
        (*unit_count)++;
        if (image == 0 || reflected_image != modulus - image)
            *identity_ok = 0;
        if (hg_wraps(modulus, index, unit) ==
            hg_wraps(modulus, index, modulus - unit))
            *complement_ok = 0;
    }
    return 1;
}

int half_group_reflection_values(
    int modulus, int index, int *unit_count, int *structure_ok)
{
    int identity = 0;
    int complement = 0;
    if (!structure_ok ||
        !hg_reflection_model(
            modulus, index, &identity, &complement, unit_count))
        return 0;
    *structure_ok = identity && complement;
    return 1;
}

int half_group_inspect(int modulus, int index)
{
    if (!hg_valid(modulus, index, 1)) return 1;
    int wraps = 0;
    int totient = 0;
    half_group_cardinality(modulus, index, &wraps, &totient);
    int identity = 0;
    int complement = 0;
    int unit_count = 0;
    if (!hg_reflection_model(
            modulus, index, &identity, &complement, &unit_count))
        return 1;
    int cardinality = 2 * wraps == totient;
    int ok = identity && complement && cardinality && unit_count == totient;
    printf("Half-group theorem\n\n");
    printf("  modulus m=%d interior index n=%d coefficient c=n+1=%d\n",
           modulus, index, index + 1);
    printf("  phi(m)=%d\n", totient);
    printf("  |W_n|=%d; phi(m)/2=%d                       %s\n",
           wraps, totient / 2, cardinality ? "PASS" : "FAIL");
    printf("  [c(m-a)]_m=m-[ca]_m at every unit           %s\n",
           identity ? "PASS" : "FAIL");
    printf("  a -> m-a exchanges W_n with its complement  %s\n",
           complement ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int half_group_verify(void)
{
    int models = 0;
    int complement_failures = 0;
    int identity_failures = 0;
    int cardinality_failures = 0;
    for (int modulus = 3; modulus <= 256; modulus++) {
        for (int index = 1; index <= modulus - 2; index++) {
            int wraps = 0;
            int totient = 0;
            models++;
            if (!half_group_cardinality(
                    modulus, index, &wraps, &totient) ||
                2 * wraps != totient)
                cardinality_failures++;
            int identity = 0;
            int complement = 0;
            int unit_count = 0;
            if (!hg_reflection_model(
                    modulus, index, &identity, &complement, &unit_count) ||
                !identity)
                identity_failures++;
            if (!complement)
                complement_failures++;
        }
    }
    int count = models == 32385;
    int identity = identity_failures == 0;
    int complement = complement_failures == 0;
    int cardinality = cardinality_failures == 0;
    int passed = count + identity + complement + cardinality;
    printf("Half-group verification\n\n");
    printf("  every interior cut for 3<=m<=256: %d models  %s\n",
           models, count ? "PASS" : "FAIL");
    printf("  negation exchanges each set and complement     %s\n",
           complement ? "PASS" : "FAIL");
    printf("  exact residue reflection at every unit          %s\n",
           identity ? "PASS" : "FAIL");
    printf("  every wrapping set has cardinality phi(m)/2    %s\n",
           cardinality ? "PASS" : "FAIL");
    printf("\n%d/4 verification groups passed.\n", passed);
    printf("Computed  the sweep uses exact residues, gcds, and cardinalities.\n");
    printf("Proof boundary  the universal complement bijection is a theorem;\n");
    printf("the exhaustive bounded sweep is independent corroboration.\n");
    return passed == 4;
}

void half_group_help(void)
{
    printf(
        "Half-group theorem\n\n"
        "Commands\n"
        "  nfield half-group inspect <m> <n>\n"
        "      Count W_n and check the complement bijection for one interior cut.\n"
        "  nfield half-group verify\n"
        "  nfield verify half-group\n\n"
        "Scope\n"
        "  mathematical scope exact residue reflection, complement bijection,\n"
        "                     and |W_n|=phi(m)/2 for every interior cut.\n"
        "  exact computation all 32385 interior cuts with 3<=m<=256.\n"
        "  boundary           the exhaustive bounded sweep is corroboration and\n"
        "                     does not prove the universal bijection.\n"
    );
}
