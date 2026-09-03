/*
 * collision_periodic_table.c
 *
 * Exact finite verification tools for the lag-one collision table.
 * The table is defined directly by the finite floor formula and checked
 * against the original digit-bin collision count.
 */

#include <stdint.h>
#include <stdio.h>
#include "nfield.h"

#define CPT_MAX_BASE 128
#define CPT_MAX_INPUT 10000000

typedef struct {
    int phi;
    int minimum;
    int maximum;
    int positive;
    int zero;
    int negative;
    long long sum;
} CPTSummary;

typedef struct {
    int base;
    int phi;
    int minimum;
    int maximum;
    int positive;
    int zero;
    int negative;
} CPTReferenceSummary;

static const int cpt_base_ten_table[100] = {
    [1] = 0,   [3] = 2,   [7] = 0,   [9] = 8,
    [11] = -1, [13] = -1, [17] = 1,  [19] = -1,
    [21] = 0,  [23] = -2, [27] = 6,  [29] = 0,
    [31] = -1, [33] = -1, [37] = -3, [39] = -1,
    [41] = -4, [43] = 0,  [47] = -2, [49] = 0,
    [51] = -1, [53] = 1,  [57] = -1, [59] = 3,
    [61] = 0,  [63] = 2,  [67] = 0,  [69] = 0,
    [71] = -1, [73] = -7, [77] = 1,  [79] = -1,
    [81] = 0,  [83] = -2, [87] = 0,  [89] = 0,
    [91] = -9, [93] = -1, [97] = -3, [99] = -1
};

static const CPTReferenceSummary cpt_reference_summaries[] = {
    {3, 6, -2, 1, 1, 2, 3},
    {5, 20, -4, 3, 4, 6, 10},
    {6, 12, -5, 4, 2, 4, 6},
    {7, 42, -6, 5, 10, 11, 21},
    {8, 32, -7, 6, 7, 9, 16},
    {10, 40, -9, 8, 8, 12, 20},
    {12, 48, -11, 10, 11, 13, 24}
};

static int cpt_validate_base(int base, int report)
{
    if (base < 2 || base > CPT_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n", CPT_MAX_BASE);
        return 0;
    }
    int modulus = 0;
    if (!collision_table_modulus(base, 1, &modulus)) {
        if (report) fprintf(stderr, "base square exceeds the table limit\n");
        return 0;
    }
    return 1;
}

int collision_periodic_value(int base, int residue, int *value)
{
    return cpt_validate_base(base, 0) &&
           collision_table_value(base, 1, residue, value);
}

static int cpt_summarize(int base, CPTSummary *summary)
{
    if (!summary || !cpt_validate_base(base, 0)) return 0;
    int modulus = base * base;
    *summary = (CPTSummary){0};
    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1) continue;
        int value = 0;
        if (!collision_periodic_value(base, a, &value)) return 0;
        if (summary->phi == 0 || value < summary->minimum)
            summary->minimum = value;
        if (summary->phi == 0 || value > summary->maximum)
            summary->maximum = value;
        summary->phi++;
        summary->sum += value;
        if (value < 0) summary->negative++;
        else if (value > 0) summary->positive++;
        else summary->zero++;
    }
    return summary->phi > 0;
}

int collision_periodic_inspect(int n, int base)
{
    if (!cpt_validate_base(base, 1)) return 1;
    int modulus = base * base;
    if (n < 2) {
        fprintf(stderr, "n must be at least 2\n");
        return 1;
    }
    if (n > CPT_MAX_INPUT) {
        fprintf(stderr, "n must not exceed %d for direct inspection\n",
                CPT_MAX_INPUT);
        return 1;
    }
    if (collision_table_gcd(n, base) != 1) {
        fprintf(stderr, "n must be coprime to the base\n");
        return 1;
    }
    int residue = n % modulus;
    int table_value = 0, collision = 0, deviation = 0, multiplier = 0;
    int ok = collision_periodic_value(base, residue, &table_value) &&
             collision_table_direct_deviation(
                 n, base, 1, &collision, &deviation, &multiplier) &&
             deviation == table_value;
    printf("Lag-one collision table\n\n");
    printf("n = %d; base b = %d; table modulus b^2 = %d\n",
           n, base, modulus);
    printf("fingerprint class n mod b^2 = %d\n", residue);
    printf("lag-one multiplier = %d\n", multiplier);
    printf("direct collision count C_b(n) = %d\n", collision);
    printf("direct deviation C_b(n)-floor((n-1)/b) = %+d\n", deviation);
    printf("table fingerprint T_b(%d) = %+d  %s\n",
           residue, table_value, ok ? "PASS" : "FAIL");
    printf("No primality assumption is used.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int cpt_valid_input(int n, int base, const char *label)
{
    if (n < 2) {
        fprintf(stderr, "%s must be at least 2\n", label);
        return 0;
    }
    if (n > CPT_MAX_INPUT) {
        fprintf(stderr, "%s must not exceed %d for direct comparison\n",
                label, CPT_MAX_INPUT);
        return 0;
    }
    if (collision_table_gcd(n, base) != 1) {
        fprintf(stderr, "%s must be coprime to the base\n", label);
        return 0;
    }
    return 1;
}

int collision_periodic_compare(int first, int second, int base)
{
    if (!cpt_validate_base(base, 1) ||
        !cpt_valid_input(first, base, "first input") ||
        !cpt_valid_input(second, base, "second input"))
        return 1;
    int modulus = base * base;
    int first_residue = first % modulus;
    int second_residue = second % modulus;
    int first_value = 0, second_value = 0;
    if (!collision_periodic_value(base, first_residue, &first_value) ||
        !collision_periodic_value(base, second_residue, &second_value))
        return 1;
    int same_class = first_residue == second_residue;
    printf("Lag-one collision table\n");
    printf("Fingerprint comparison in base %d modulo %d\n\n", base, modulus);
    printf("  n=%d: class %d, T=%+d\n", first, first_residue, first_value);
    printf("  n=%d: class %d, T=%+d\n", second, second_residue, second_value);
    printf("same residue class modulo b^2 = %s\n", same_class ? "yes" : "no");
    printf("same integer table value = %s\n",
           first_value == second_value ? "yes" : "no");
    if (same_class)
        printf("The finite-determination theorem forces identical fingerprints.\n");
    else if (first_value == second_value)
        printf("Different classes can share a value; the class is the full fingerprint.\n");
    else
        printf("The two classes have different collision values.\n");
    printf("Result  PASS\n");
    return 0;
}

int collision_periodic_table(int base)
{
    if (!cpt_validate_base(base, 1)) return 1;
    int modulus = base * base;
    int ok = 1;
    printf("Lag-one collision table\n");
    printf("Complete unit table in base %d modulo %d\n\n", base, modulus);
    printf("  class a   T_b(a)   complement   T_b(-a)   pair\n");
    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1) continue;
        int value = 0, reflected = 0;
        if (!collision_periodic_value(base, a, &value) ||
            !collision_periodic_value(base, modulus - a, &reflected))
            return 1;
        int pair_ok = value + reflected == -1;
        if (!pair_ok) ok = 0;
        printf("  %-9d %+6d   %-10d   %+6d     %s\n",
               a, value, modulus - a, reflected,
               pair_ok ? "PASS" : "FAIL");
    }
    printf("\nDots in a full residue grid are nonunit classes and are not table cells.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int collision_periodic_summary(int base)
{
    if (!cpt_validate_base(base, 1)) return 1;
    CPTSummary summary;
    if (!cpt_summarize(base, &summary)) return 1;
    int modulus = base * base;
    int maximum_class = base - 1;
    int minimum_class = modulus - base + 1;
    int maximum_value = 0, minimum_value = 0;
    collision_periodic_value(base, maximum_class, &maximum_value);
    collision_periodic_value(base, minimum_class, &minimum_value);
    int extrema_ok = summary.maximum == base - 2 &&
        summary.minimum == -(base - 1) &&
        maximum_value == base - 2 && minimum_value == -(base - 1);
    int signs_ok = 2 * summary.negative == summary.phi;
    int mean_ok = 2 * summary.sum == -summary.phi;
    printf("Lag-one collision table\n");
    printf("Exact base-%d summary\n\n", base);
    printf("unit cells phi(b^2) = %d\n", summary.phi);
    printf("minimum/maximum = %+d/%+d\n", summary.minimum, summary.maximum);
    printf("minimum class b^2-b+1 = %d; maximum class b-1 = %d  %s\n",
           minimum_class, maximum_class, extrema_ok ? "PASS" : "FAIL");
    printf("positive/zero/negative = %d/%d/%d\n",
           summary.positive, summary.zero, summary.negative);
    printf("exactly half the cells are negative  %s\n",
           signs_ok ? "PASS" : "FAIL");
    printf("table sum = %lld; exact mean = -1/2  %s\n",
           summary.sum, mean_ok ? "PASS" : "FAIL");
    printf("Result  %s\n",
           extrema_ok && signs_ok && mean_ok ? "PASS" : "FAIL");
    return extrema_ok && signs_ok && mean_ok ? 0 : 1;
}

int collision_periodic_examples(void)
{
    int value_9 = 0, value_91 = 0;
    int table = collision_periodic_value(10, 9, &value_9) &&
                collision_periodic_value(10, 91, &value_91) &&
                value_9 == 8 && value_91 == -9;
    int checks = 1;
    const int examples[][3] = {
        {109, 1009, 8}, {191, 991, -9}
    };
    for (int i = 0; i < 2; i++) {
        int first_c = 0, first_s = 0, first_m = 0;
        int second_c = 0, second_s = 0, second_m = 0;
        if (!collision_table_direct_deviation(
                examples[i][0], 10, 1, &first_c, &first_s, &first_m) ||
            !collision_table_direct_deviation(
                examples[i][1], 10, 1, &second_c, &second_s, &second_m) ||
            first_s != examples[i][2] || second_s != examples[i][2])
            checks = 0;
    }
    printf("Lag-one collision table\n");
    printf("Named exact fingerprints\n\n");
    printf("  T_10(9)=+8 and T_10(91)=-9                        %s\n",
           table ? "PASS" : "FAIL");
    printf("  109 and 1009 share class 9 and value +8          %s\n",
           checks ? "PASS" : "FAIL");
    printf("  191 and 991 share class 91 and value -9           %s\n",
           checks ? "PASS" : "FAIL");
    printf("Result  %s\n", table && checks ? "PASS" : "FAIL");
    return table && checks ? 0 : 1;
}

static const CPTReferenceSummary *cpt_reference_row(int base)
{
    int count = (int)(sizeof(cpt_reference_summaries) /
                      sizeof(cpt_reference_summaries[0]));
    for (int i = 0; i < count; i++)
        if (cpt_reference_summaries[i].base == base)
            return &cpt_reference_summaries[i];
    return NULL;
}

static void cpt_report(const char *label, int ok, int *passed)
{
    printf("  %-66s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int collision_periodic_verify(void)
{
    int floor_formula = 1, direct = 1, reflection = 1, extrema = 1;
    int signs = 1, mean = 1, base_ten = 1, summaries = 1;
    int unit_classes = 0, direct_checks = 0;
    for (int base = 2; base <= 12; base++) {
        int modulus = base * base;
        CPTSummary summary;
        if (!cpt_summarize(base, &summary)) {
            floor_formula = 0;
            continue;
        }
        unit_classes += summary.phi;
        if (summary.minimum != -(base - 1) ||
            summary.maximum != base - 2)
            extrema = 0;
        if (2 * summary.negative != summary.phi) signs = 0;
        if (2 * summary.sum != -summary.phi) mean = 0;
        int extreme_value = 0;
        if (!collision_periodic_value(base, base - 1, &extreme_value) ||
            extreme_value != base - 2 ||
            !collision_periodic_value(
                base, modulus - base + 1, &extreme_value) ||
            extreme_value != -(base - 1))
            extrema = 0;

        const CPTReferenceSummary *expected = cpt_reference_row(base);
        if (expected &&
            (summary.phi != expected->phi ||
             summary.minimum != expected->minimum ||
             summary.maximum != expected->maximum ||
             summary.positive != expected->positive ||
             summary.zero != expected->zero ||
             summary.negative != expected->negative))
            summaries = 0;

        for (int a = 1; a < modulus; a++) {
            if (collision_table_gcd(a, modulus) != 1) continue;
            int value = 0, reflected = 0;
            if (!collision_periodic_value(base, a, &value)) {
                floor_formula = 0;
                continue;
            }
            if (!collision_periodic_value(
                    base, modulus - a, &reflected) ||
                value + reflected != -1)
                reflection = 0;
            if (base == 10 && value != cpt_base_ten_table[a]) base_ten = 0;
            for (int multiple = 0; multiple <= 3; multiple++) {
                int n = multiple * modulus + a;
                if (n < 2) continue;
                int collision = 0, deviation = 0, multiplier = 0;
                if (!collision_table_direct_deviation(
                        n, base, 1, &collision, &deviation, &multiplier) ||
                    deviation != value)
                    direct = 0;
                direct_checks++;
            }
        }
    }
    int examples = collision_periodic_examples() == 0;
    int passed = 0;
    printf("\nFinite verification of the lag-one collision table\n");
    printf("Exact sweep: %d unit classes across bases 2 through 12.\n",
           unit_classes);
    printf("Direct comparison: %d checks over all admissible inputs in the "
           "first four square-quotient blocks.\n\n",
           direct_checks);
    cpt_report("finite floor formula on every unit class", floor_formula,
               &passed);
    cpt_report("floor table equals every direct collision deviation", direct,
               &passed);
    cpt_report("reflection T(a)+T(-a)=-1", reflection, &passed);
    cpt_report("sharp extrema and their displayed classes", extrema, &passed);
    cpt_report("exactly half of all unit cells are negative", signs, &passed);
    cpt_report("exact grand mean -1/2", mean, &passed);
    cpt_report("complete forty-cell base-ten table", base_ten, &passed);
    cpt_report("all seven reference selected-base summaries", summaries,
               &passed);
    cpt_report("named repeated-fingerprint examples", examples, &passed);
    printf("\n%d/9 verification groups passed.\n", passed);
    printf("All checks use exact integer arithmetic. They verify the complete\n"
           "finite tables, reference data, and direct formulas over the stated\n"
           "range; the universal proofs remain logically separate.\n");
    return passed == 9;
}

void collision_periodic_help(void)
{
    printf(
        "Lag-one collision table\n\n"
        "This verifies the floor formula against direct collision counts, every\n"
        "tested unit class, the complete decimal table, and every selected-base\n"
        "reference summary.\n\n"
        "Usage:\n"
        "  nfield collision-table inspect <n> [--base <b>]\n"
        "  nfield collision-table compare <n1> <n2> [--base <b>]\n"
        "  nfield collision-table table [--base <b>]\n"
        "  nfield collision-table summary [--base <b>]\n"
        "  nfield collision-table examples\n"
        "  nfield collision-table verify\n"
        "  nfield verify collision-table\n\n"
        "inspect evaluates the original digit-bin collision count and its exact\n"
        "floor-table fingerprint at n mod b^2. n may be prime or composite.\n"
        "compare shows whether two inputs have the same full residue fingerprint\n"
        "or merely happen to share an integer table value. table prints every unit\n"
        "cell with its reflected partner. summary certifies the sharp extrema,\n"
        "sign counts, and exact mean.\n\n"
        "The verifier checks every coprime input from 2 through 4b^2-1 in bases\n"
        "2 through 12, the complete forty-cell base-ten table, and all seven\n"
        "reference summary rows. Everything here is exact finite arithmetic.\n"
        "Direct inspection and comparison accept inputs through ten million.\n"
        "These calculations check the finite data and formulas but do not replace\n"
        "the universal proofs. The legacy collision_table command searches for\n"
        "prime examples. The collision-periodic-table spelling remains a "
        "compatibility alias.\n"
    );
}
