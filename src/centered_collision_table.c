/* Exact reflection and fiber-centering checks for collision tables. */

#include <stdio.h>

#include "finite_character_core.h"
#include "nfield.h"

enum { CENTERED_COLLISION_TABLE_ROW_COUNT = 14 };

static const int published_rows[CENTERED_COLLISION_TABLE_ROW_COUNT][2] = {
    {3, 1}, {3, 2}, {3, 3}, {3, 4}, {3, 5}, {3, 6}, {3, 7},
    {5, 1}, {5, 2}, {5, 3}, {5, 4},
    {7, 1}, {7, 2}, {7, 3}
};

int centered_collision_table_inspect(int base, int lag, int residue)
{
    CollisionCenteredTable table = {0};
    long long numerator = 0, denominator = 0;
    int reflected;
    int failures;

    if (!collision_centered_table_build(base, lag, &table)) {
        fprintf(stderr,
                "base and lag must define a table with base^(lag+1) <= 2000000\n");
        return 1;
    }
    if (residue <= 0 || residue >= table.modulus ||
        collision_table_gcd(residue, table.modulus) != 1) {
        fprintf(stderr,
                "residue must be a unit strictly between 0 and the modulus\n");
        collision_centered_table_free(&table);
        return 1;
    }
    reflected = table.modulus - residue;
    failures = centered_collision_table_audit(&table, NULL, NULL);
    if (!collision_centered_table_fraction(&table, residue,
                                           &numerator, &denominator))
        failures++;

    printf("Centered collision table\n");
    printf("Exact residue inspection\n\n");
    printf("  base b = %d; lag ell = %d; modulus b^(ell+1) = %d\n",
           base, lag, table.modulus);
    printf("  unit residue a = %d; reduction fiber a mod b = %d\n",
           residue, residue % base);
    printf("  raw table T_b,ell(a) = %+d\n", table.value[residue]);
    printf("  centered table f_b,ell(a) = %+lld/%lld",
           numerator, denominator);
    if (denominator != 1)
        printf(" = %+.12Lf", (long double)numerator / denominator);
    printf("\n");
    printf("  reflected residue = %d; T(a)+T(-a) = %d  %s\n",
           reflected, table.value[residue] + table.value[reflected],
           table.value[residue] + table.value[reflected] == -1
               ? "PASS" : "FAIL");
    printf("  centered numerators add to %lld  %s\n",
           table.centered_numerator[residue] +
               table.centered_numerator[reflected],
           table.centered_numerator[residue] +
               table.centered_numerator[reflected] == 0 ? "PASS" : "FAIL");
    printf("\nClassification  exact finite integer and rational arithmetic.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return failures == 0 ? 0 : 1;
}

int centered_collision_table_complete(int base, int lag)
{
    CollisionCenteredTable table = {0};
    int reflection_cases = 0, fiber_cases = 0;
    int failures;

    if (!collision_centered_table_build(base, lag, &table)) {
        fprintf(stderr,
                "base and lag must define a table with base^(lag+1) <= 2000000\n");
        return 1;
    }
    failures = centered_collision_table_audit(
        &table, &reflection_cases, &fiber_cases);
    printf("Centered collision table\n");
    printf("Complete exact table gate\n\n");
    printf("  base=%d lag=%d modulus=%d unit residues=%d\n",
           base, lag, table.modulus, table.phi);
    printf("  every raw reflection T(a)+T(-a)=-1: %d cases  %s\n",
           reflection_cases, failures == 0 ? "PASS" : "FAIL");
    printf("  every centered reduction fiber has sum zero: %d fibers  %s\n",
           fiber_cases, failures == 0 ? "PASS" : "FAIL");
    printf("  every centered reflection f(-a)=-f(a)  %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  complete raw mean is exactly -1/2  %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("\nAll %d unit residue classes were checked from the floor formula.\n",
           table.phi);
    printf("Classification  exact finite computation; no prime representatives.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return failures == 0 ? 0 : 1;
}

static int published_table_suite(int *residue_cases)
{
    int failures = 0;
    int cases = 0;

    for (int row = 0; row < CENTERED_COLLISION_TABLE_ROW_COUNT; row++) {
        CollisionCenteredTable table = {0};
        if (!collision_centered_table_build(
                published_rows[row][0], published_rows[row][1], &table)) {
            failures++;
            continue;
        }
        failures += centered_collision_table_audit(&table, NULL, NULL);
        cases += table.phi;
        collision_centered_table_free(&table);
    }
    {
        CollisionCenteredTable fixture = {0};
        static const int residues[6] = {1, 2, 4, 5, 7, 8};
        static const int raw[6] = {0, 1, 0, -1, -2, -1};
        static const long long centered[6] = {2, 4, 2, -2, -4, -2};

        if (!collision_centered_table_build(3, 1, &fixture)) failures++;
        else {
            for (int index = 0; index < 6; index++)
                if (fixture.value[residues[index]] != raw[index] ||
                    fixture.centered_numerator[residues[index]] !=
                        centered[index])
                    failures++;
            collision_centered_table_free(&fixture);
        }
    }
    if (residue_cases) *residue_cases = cases;
    return failures;
}

int centered_collision_table_verify(void)
{
    int residue_cases = 0;
    int ok = published_table_suite(&residue_cases) == 0;

    printf("Centered collision table verification\n\n");
    printf("  fourteen declared tables and %d unit residues  %s\n",
           residue_cases, ok ? "PASS" : "FAIL");
    printf("  base-three lag-one raw and centered fixture     %s\n",
           ok ? "PASS" : "FAIL");
    printf("\n2/2 verification groups %s.\n", ok ? "passed" : "did not pass");
    printf("Classification  exact finite integer and rational arithmetic.\n");
    printf("Coverage  fourteen reference tables and every declared unit residue.\n");
    return ok;
}

void centered_collision_table_help(void)
{
    printf(
        "Centered collision table\n\n"
        "Exact commands\n"
        "  nfield centered-collision-table inspect <base> <lag> <unit-residue>\n"
        "      Show a raw value, its fiber-centered value, and reflection.\n"
        "  nfield centered-collision-table complete <base> <lag>\n"
        "      Exhaust every unit residue, reflection, and reduction fiber.\n"
        "  nfield centered-collision-table verify\n"
        "  nfield verify centered-collision-table\n\n"
        "Scope\n"
        "  exact computation  Integer floor tables and rational centering.\n"
        "  finite boundary    Exhaustion covers the requested table and the\n"
        "                     fourteen-table reference suite.\n"
    );
}
