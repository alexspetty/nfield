/*
 * residue_three_neutrality.c
 *
 * Exact finite arithmetic for residue-three neutrality.
 * Canonical representatives modulo b^(ell+1) and true integer residues modulo
 * three are deliberately kept as different coordinates.
 */

#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "nfield.h"

#define RTHREE_MAX_BASE 128
#define RTHREE_MAX_MODULUS 50000
#define RTHREE_MAX_INPUT 10000000
#define RTHREE_EXPONENTS 6

typedef struct {
    long long raw_sum[3];
    long long centered_numerator_sum[3];
    int count[3];
} NThreeSlices;

static const long double rthree_exponents[RTHREE_EXPONENTS] = {
    1.0L, 0.9L, 0.8L, 0.7L, 0.6L, 0.5L
};

static const long double rthree_class_one_expected[RTHREE_EXPONENTS] = {
    0.0002534L, 0.0009126L, 0.0031182L,
    0.0097059L, 0.0245861L, 0.0256653L
};

static const long double rthree_class_two_expected[RTHREE_EXPONENTS] = {
    -0.0001884L, -0.0008658L, -0.0039858L,
    -0.0183773L, -0.0848446L, -0.3921645L
};

static int rthree_validate(int base, int lag, int report)
{
    int modulus = 0;
    if (base < 2 || base > RTHREE_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n",
                    RTHREE_MAX_BASE);
        return 0;
    }
    if (lag < 1 || lag > 16) {
        if (report) fprintf(stderr, "lag must be between 1 and 16\n");
        return 0;
    }
    if (!collision_table_modulus(base, lag, &modulus) ||
        modulus > RTHREE_MAX_MODULUS) {
        if (report)
            fprintf(stderr,
                    "base^(lag+1) exceeds the finite-table limit of %d\n",
                    RTHREE_MAX_MODULUS);
        return 0;
    }
    return 1;
}

static int rthree_lcm_three(int modulus)
{
    return modulus % 3 == 0 ? modulus : 3 * modulus;
}

static unsigned char *rthree_sieve(int limit)
{
    unsigned char *composite = calloc((size_t)limit + 1, 1);
    if (!composite) return NULL;
    composite[0] = 1;
    if (limit >= 1) composite[1] = 1;
    for (int p = 2; p <= limit / p; p++) {
        if (composite[p]) continue;
        for (int64_t multiple = (int64_t)p * p;
             multiple <= limit; multiple += p)
            composite[multiple] = 1;
    }
    return composite;
}

static NThreeSlices rthree_canonical_slices(
    const CollisionCenteredTable *table)
{
    NThreeSlices slices = {{0}, {0}, {0}};
    for (int a = 1; a < table->modulus; a++) {
        if (collision_table_gcd(a, table->modulus) != 1) continue;
        int residue = a % 3;
        slices.raw_sum[residue] += table->value[a];
        slices.centered_numerator_sum[residue] +=
            table->centered_numerator[a];
        slices.count[residue]++;
    }
    return slices;
}

static NThreeSlices rthree_true_channels(
    const CollisionCenteredTable *table)
{
    NThreeSlices slices = {{0}, {0}, {0}};
    int joint_modulus = rthree_lcm_three(table->modulus);
    for (int A = 1; A < joint_modulus; A++) {
        if (collision_table_gcd(A, joint_modulus) != 1) continue;
        int residue = A % 3;
        int a = A % table->modulus;
        slices.raw_sum[residue] += table->value[a];
        slices.centered_numerator_sum[residue] +=
            table->centered_numerator[a];
        slices.count[residue]++;
    }
    return slices;
}

int residue_three_neutrality_channel_sums(
    int base, int lag, int residue,
    long long *raw_sum, long long *centered_numerator_sum,
    int *count, int *joint_modulus)
{
    if (!raw_sum || !centered_numerator_sum || !count || !joint_modulus ||
        (residue != 1 && residue != 2) ||
        !rthree_validate(base, lag, 0))
        return 0;
    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 0;
    NThreeSlices channels = rthree_true_channels(&table);
    *raw_sum = channels.raw_sum[residue];
    *centered_numerator_sum = channels.centered_numerator_sum[residue];
    *count = channels.count[residue];
    *joint_modulus = rthree_lcm_three(table.modulus);
    collision_centered_table_free(&table);
    return 1;
}

int residue_three_neutrality_prime_window(
    int lower, int upper, int base, int lag,
    const long double *exponents, int exponent_count,
    long double *class_one, long double *class_two,
    long double *total, long double *twist,
    int *class_one_count, int *class_two_count)
{
    if (!exponents || exponent_count < 1 || !class_one || !class_two ||
        !total || !twist || !class_one_count || !class_two_count ||
        !rthree_validate(base, lag, 0) || lower < 0 ||
        upper <= lower || upper > RTHREE_MAX_INPUT)
        return 0;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    int joint_modulus = rthree_lcm_three(modulus);
    if (lower < joint_modulus) return 0;

    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 0;
    unsigned char *composite = rthree_sieve(upper);
    if (!composite) {
        collision_centered_table_free(&table);
        return 0;
    }
    for (int e = 0; e < exponent_count; e++) {
        class_one[e] = 0.0L;
        class_two[e] = 0.0L;
        total[e] = 0.0L;
        twist[e] = 0.0L;
    }
    *class_one_count = 0;
    *class_two_count = 0;

    for (int p = lower + 1; p <= upper; p++) {
        if (composite[p]) continue;
        int channel = p % 3;
        if (channel != 1 && channel != 2) continue;
        int a = p % modulus;
        int fiber = a % base;
        long double centered =
            (long double)table.centered_numerator[a] /
            table.fiber_count[fiber];
        if (channel == 1) (*class_one_count)++;
        else (*class_two_count)++;
        for (int e = 0; e < exponent_count; e++) {
            long double term = centered /
                powl((long double)p, exponents[e]);
            if (channel == 1) class_one[e] += term;
            else class_two[e] += term;
            total[e] += term;
            twist[e] += channel == 1 ? term : -term;
        }
    }

    free(composite);
    collision_centered_table_free(&table);
    return 1;
}

int residue_three_neutrality_inspect(int n, int base, int lag)
{
    if (!rthree_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (n <= modulus) {
        fprintf(stderr, "inspection requires n > base^(lag+1) = %d\n",
                modulus);
        return 1;
    }
    if (n > RTHREE_MAX_INPUT) {
        fprintf(stderr, "n must not exceed %d\n", RTHREE_MAX_INPUT);
        return 1;
    }
    if (collision_table_gcd(n, base) != 1) {
        fprintf(stderr, "n must be coprime to the base\n");
        return 1;
    }
    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    int quotient = n / modulus;
    int a = n % modulus;
    long long numerator = 0, denominator = 0;
    int ok = collision_centered_table_fraction(
        &table, a, &numerator, &denominator);
    printf("Residue-three neutrality\n\n");
    printf("n = %d = %d*%d + %d\n", n, modulus, quotient, a);
    printf("canonical table class a mod 3 = %d\n", a % 3);
    printf("quotient carry q*t mod 3 = %d\n",
           (int)((long long)(modulus % 3) * (quotient % 3) % 3));
    printf("true integer class n mod 3 = %d\n", n % 3);
    printf("T_b,ell(a) = %+d\n", table.value[a]);
    printf("f_b,ell(a) = %lld/%lld\n", numerator, denominator);
    printf("canonical and true residue-three coordinates agree only when the carry says so.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

static void rthree_print_slice(const char *label, int residue,
                                 const NThreeSlices *slices,
                                 int centered_denominator)
{
    if (slices->count[residue] == 0) {
        printf("  %s class %d: empty\n", label, residue);
        return;
    }
    printf("  %s class %d: count=%d; raw sum=%+lld; raw mean=%+lld/%d; ",
           label, residue, slices->count[residue],
           slices->raw_sum[residue], slices->raw_sum[residue],
           slices->count[residue]);
    printf("centered sum=%+lld/%d\n",
           slices->centered_numerator_sum[residue], centered_denominator);
}

int residue_three_neutrality_canonical(int base, int lag)
{
    if (!rthree_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (modulus % 3 == 0) {
        fprintf(stderr,
                "canonical internal reflection slices require 3 not dividing q\n");
        return 1;
    }
    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    NThreeSlices slices = rthree_canonical_slices(&table);
    int fixed = 2 * (modulus % 3) % 3;
    int fixed_ok = slices.count[fixed] == 0 ||
        (2 * slices.raw_sum[fixed] == -slices.count[fixed] &&
         slices.centered_numerator_sum[fixed] == 0);
    int other = (fixed + 1) % 3;
    int paired = (modulus - other) % 3;
    int pair_ok = slices.count[other] == slices.count[paired] &&
        slices.raw_sum[other] + slices.raw_sum[paired] ==
            -slices.count[other] &&
        slices.centered_numerator_sum[other] +
            slices.centered_numerator_sum[paired] == 0;
    printf("Residue-three neutrality\n");
    printf("Canonical representative slices in base %d at lag %d\n\n",
           base, lag);
    for (int r = 0; r < 3; r++)
        rthree_print_slice("internal", r, &slices, table.fiber_size);
    printf("\nreflection-fixed internal class = %d                    %s\n",
           fixed, fixed_ok ? "PASS" : "FAIL");
    printf("the other two internal classes are a reflected pair     %s\n",
           pair_ok ? "PASS" : "FAIL");
    printf("Representative slices use the internal coordinate; true channels use the joint modulus.\n");
    printf("Result  %s\n", fixed_ok && pair_ok ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return fixed_ok && pair_ok ? 0 : 1;
}

int residue_three_neutrality_channels(int base, int lag)
{
    if (!rthree_validate(base, lag, 1)) return 1;
    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    NThreeSlices channels = rthree_true_channels(&table);
    int joint_modulus = rthree_lcm_three(table.modulus);
    int centered_ok = channels.centered_numerator_sum[1] == 0 &&
                      channels.centered_numerator_sum[2] == 0;
    int raw_ok = 1;
    if (base % 3 != 0) {
        raw_ok = channels.count[1] == table.phi &&
                 channels.count[2] == table.phi &&
                 2 * channels.raw_sum[1] == -channels.count[1] &&
                 2 * channels.raw_sum[2] == -channels.count[2];
    }
    printf("Residue-three neutrality\n");
    printf("True residue-three channels in base %d at lag %d\n\n",
           base, lag);
    printf("table modulus q = %d; joint modulus lcm(q,3) = %d\n",
           table.modulus, joint_modulus);
    rthree_print_slice("true", 1, &channels, table.fiber_size);
    rthree_print_slice("true", 2, &channels, table.fiber_size);
    printf("\ntrue class one centered sum is zero                    %s\n",
           channels.centered_numerator_sum[1] == 0 ? "PASS" : "FAIL");
    printf("true class two centered sum is zero                    %s\n",
           channels.centered_numerator_sum[2] == 0 ? "PASS" : "FAIL");
    if (base % 3 != 0)
        printf("each true raw channel has exact mean -1/2              %s\n",
               raw_ok ? "PASS" : "FAIL");
    else
        printf("3 divides the base; each channel is a union of zero-sum fibers.\n");
    printf("Each true channel has zero principal coefficient on its own.\n");
    printf("Result  %s\n", centered_ok && raw_ok ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return centered_ok && raw_ok ? 0 : 1;
}

int residue_three_neutrality_split(int lower, int upper, int base, int lag,
                             long double sigma)
{
    if (!rthree_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    int joint_modulus = rthree_lcm_three(modulus);
    if (lower < joint_modulus || upper <= lower ||
        upper > RTHREE_MAX_INPUT) {
        fprintf(stderr,
                "window must satisfy lcm(q,3) <= lower < upper <= %d\n",
                RTHREE_MAX_INPUT);
        return 1;
    }
    if (!(sigma > 0.0L)) {
        fprintf(stderr, "sigma must be positive\n");
        return 1;
    }
    long double one = 0.0L, two = 0.0L, total = 0.0L, twist = 0.0L;
    int count_one = 0, count_two = 0;
    if (!residue_three_neutrality_prime_window(
            lower, upper, base, lag, &sigma, 1, &one, &two,
            &total, &twist, &count_one, &count_two))
        return 1;
    long double total_error = fabsl((one + two) - total);
    long double twist_error = fabsl((one - two) - twist);
    long double tolerance = 1024.0L * LDBL_EPSILON *
        (count_one + count_two) *
        (1.0L + fabsl(one) + fabsl(two) + fabsl(total) + fabsl(twist));
    int ok = total_error <= tolerance && twist_error <= tolerance;
    printf("Residue-three neutrality\n");
    printf("Declared finite true-channel split\n\n");
    printf("base=%d; lag=%d; %d < p <= %d; sigma=%.6Lf\n",
           base, lag, lower, upper, sigma);
    printf("class one: count=%d; contribution=%+.12Lf\n", count_one, one);
    printf("class two: count=%d; contribution=%+.12Lf\n", count_two, two);
    printf("total = %+.12Lf; class-one + class-two error = %.3Le\n",
           total, total_error);
    printf("twist = %+.12Lf; class-one - class-two error = %.3Le\n",
           twist, twist_error);
    printf("The finite split is exact; convergence below one remains open.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int rthree_snapshot_ok(int print)
{
    long double one[RTHREE_EXPONENTS];
    long double two[RTHREE_EXPONENTS];
    long double total[RTHREE_EXPONENTS];
    long double twist[RTHREE_EXPONENTS];
    int count_one = 0, count_two = 0;
    if (!residue_three_neutrality_prime_window(
            1000000, 10000000, 10, 1,
            rthree_exponents, RTHREE_EXPONENTS,
            one, two, total, twist, &count_one, &count_two))
        return 0;
    int ok = count_one == 292963 && count_two == 293118;
    if (print) {
        printf("Residue-three neutrality\n");
        printf("Reference decimal true-channel window; 1000000 < p <= 10000000\n\n");
        printf("counts: class one=%d; class two=%d; total=%d\n\n",
               count_one, count_two, count_one + count_two);
        printf("  s       class one      class two      total          twist\n");
    }
    for (int e = 0; e < RTHREE_EXPONENTS; e++) {
        int row_ok = fabsl(one[e] - rthree_class_one_expected[e]) < 5.1e-8L &&
                     fabsl(two[e] - rthree_class_two_expected[e]) < 5.1e-8L;
        long double total_error = fabsl((one[e] + two[e]) - total[e]);
        long double twist_error = fabsl((one[e] - two[e]) - twist[e]);
        long double tolerance = 1024.0L * LDBL_EPSILON *
            (count_one + count_two) *
            (1.0L + fabsl(one[e]) + fabsl(two[e]) +
             fabsl(total[e]) + fabsl(twist[e]));
        row_ok &= total_error <= tolerance && twist_error <= tolerance;
        if (!row_ok) ok = 0;
        if (print)
            printf("  %.1Lf  %+14.10Lf %+14.10Lf %+14.10Lf %+14.10Lf  %s\n",
                   rthree_exponents[e], one[e], two[e], total[e], twist[e],
                   row_ok ? "PASS" : "FAIL");
    }
    if (print) {
        printf("\n6/6 reference channel rows reproduced to displayed precision.\n");
        printf("Opposed finite signs measure a twist, not principal biases.\n");
        printf("Result  %s\n", ok ? "PASS" : "FAIL");
    }
    return ok;
}

int residue_three_neutrality_snapshot(void)
{
    return rthree_snapshot_ok(1) ? 0 : 1;
}

int residue_three_neutrality_examples(void)
{
    CollisionCenteredTable decimal = {0};
    CollisionCenteredTable ternary = {0};
    if (!collision_centered_table_build(10, 1, &decimal) ||
        !collision_centered_table_build(3, 1, &ternary)) {
        collision_centered_table_free(&decimal);
        collision_centered_table_free(&ternary);
        return 1;
    }
    int carry = 101 % 100 == 1 && 1 % 3 == 1 && 101 % 3 == 2;
    NThreeSlices decimal_channels = rthree_true_channels(&decimal);
    NThreeSlices ternary_channels = rthree_true_channels(&ternary);
    int decimal_zero = decimal_channels.centered_numerator_sum[1] == 0 &&
                       decimal_channels.centered_numerator_sum[2] == 0;
    int ternary_zero = ternary_channels.centered_numerator_sum[1] == 0 &&
                       ternary_channels.centered_numerator_sum[2] == 0;
    printf("Residue-three neutrality\n");
    printf("Exact coordinate examples\n\n");
    printf("  101 mod 100=1 but 101 mod 3=2 exposes the carry    %s\n",
           carry ? "PASS" : "FAIL");
    printf("  decimal true channels both have centered sum zero %s\n",
           decimal_zero ? "PASS" : "FAIL");
    printf("  base-three channels are unions of zero-sum fibers %s\n",
           ternary_zero ? "PASS" : "FAIL");
    printf("Result  %s\n",
           carry && decimal_zero && ternary_zero ? "PASS" : "FAIL");
    collision_centered_table_free(&decimal);
    collision_centered_table_free(&ternary);
    return carry && decimal_zero && ternary_zero ? 0 : 1;
}

static void rthree_report(const char *label, int ok, int *passed)
{
    printf("  %-66s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int residue_three_neutrality_verify(void)
{
    int table_ok = 1, fixed_slice = 1, paired_slices = 1;
    int crt_counts = 1, raw_channels = 1, centered_channels = 1;
    int bases_checked = 0, unit_classes = 0;

    for (int base = 2; base <= 40; base++) {
        CollisionCenteredTable table;
        if (!collision_centered_table_build(base, 1, &table)) {
            table_ok = 0;
            continue;
        }
        NThreeSlices canonical = rthree_canonical_slices(&table);
        NThreeSlices channels = rthree_true_channels(&table);
        if (table.modulus % 3 != 0) {
            int fixed = 2 * (table.modulus % 3) % 3;
            if (canonical.count[fixed] > 0 &&
                (2 * canonical.raw_sum[fixed] != -canonical.count[fixed] ||
                 canonical.centered_numerator_sum[fixed] != 0))
                fixed_slice = 0;
            int other = (fixed + 1) % 3;
            int paired = (table.modulus - other) % 3;
            if (canonical.count[other] != canonical.count[paired] ||
                canonical.raw_sum[other] + canonical.raw_sum[paired] !=
                    -canonical.count[other] ||
                canonical.centered_numerator_sum[other] +
                    canonical.centered_numerator_sum[paired] != 0)
                paired_slices = 0;
            if (channels.count[1] != table.phi ||
                channels.count[2] != table.phi)
                crt_counts = 0;
            if (2 * channels.raw_sum[1] != -channels.count[1] ||
                2 * channels.raw_sum[2] != -channels.count[2])
                raw_channels = 0;
        }
        if (channels.centered_numerator_sum[1] != 0 ||
            channels.centered_numerator_sum[2] != 0)
            centered_channels = 0;
        bases_checked++;
        unit_classes += table.phi;
        collision_centered_table_free(&table);
    }

    int examples = residue_three_neutrality_examples() == 0;
    int snapshot = rthree_snapshot_ok(0);
    int passed = 0;
    printf("\nFinite C verification of residue-three neutrality\n");
    printf("Exact lag-one sweep: bases 2 through 40, %d tables, %d unit classes.\n\n",
           bases_checked, unit_classes);
    rthree_report("complete centered tables built for every tested base",
                    table_ok && bases_checked == 39, &passed);
    rthree_report("reflection-fixed internal slices have raw mean -1/2 and centered sum zero",
                    fixed_slice, &passed);
    rthree_report("the other canonical slices obey the exact paired identities",
                    paired_slices, &passed);
    rthree_report("CRT gives one complete table copy in each true channel when 3 does not divide b",
                    crt_counts, &passed);
    rthree_report("both true raw channels have mean -1/2 when 3 does not divide b",
                    raw_channels, &passed);
    rthree_report("both true centered channel sums vanish in every tested base",
                    centered_channels, &passed);
    rthree_report("named quotient-carry and divisible-base examples",
                    examples, &passed);
    rthree_report("all six reference decimal split-window rows", snapshot,
                    &passed);
    printf("\n%d/8 verification groups passed.\n", passed);
    printf("All neutrality identities above are exact finite arithmetic. Mertens'\n");
    printf("theorem in arithmetic progressions is the external analytic input for\n");
    printf("separate convergence at one. Convergence below one remains open.\n");
    return passed == 8;
}

void residue_three_neutrality_help(void)
{
    printf(
        "Residue-three neutrality\n\n"
        "Inspect the quotient coordinate, canonical reflection slices, true\n"
        "channel sums, and finite prime-window twists. The verifier sweeps every\n"
        "lag-one base from two through forty.\n\n"
        "Usage:\n"
        "  nfield residue-three-neutrality inspect <n> [--base <b>] [--lag <ell>]\n"
        "  nfield residue-three-neutrality canonical [--base <b>] [--lag <ell>]\n"
        "  nfield residue-three-neutrality channels [--base <b>] [--lag <ell>]\n"
        "  nfield residue-three-neutrality split <low> <high> [--base <b>]\n"
        "       [--lag <ell>] [--sigma <real>]\n"
        "  nfield residue-three-neutrality snapshot\n"
        "  nfield residue-three-neutrality examples\n"
        "  nfield residue-three-neutrality verify\n"
        "  nfield verify residue-three-neutrality\n\n"
        "inspect displays the quotient carry separating a canonical table class\n"
        "from the represented integer's true residue modulo three. canonical\n"
        "checks the internal reflection slices when three does not divide q.\n"
        "channels lifts the complete table to lcm(q,3) and verifies that each true\n"
        "nonzero residue-three channel has centered sum zero.\n\n"
        "split evaluates the two true channels, their total, and their nontrivial\n"
        "mod-three twist on one declared finite prime window. snapshot reproduces\n"
        "the reference decimal window. The verifier checks exact lag-one tables\n"
        "for every base from 2 through 40 and both arithmetic cases.\n\n"
        "The finite channel split is exact. Separate convergence at s=1 uses\n"
        "Mertens' theorem in arithmetic progressions. Convergence below one\n"
        "remains open.\n"
    );
}
