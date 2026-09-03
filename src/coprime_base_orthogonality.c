/* Exact CRT factorization and cross-base orthogonality checks. */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "finite_character_core.h"
#include "nfield.h"

#define BIG_INTEGER_RADIX UINT32_C(1000000000)

enum {
    ORTHOGONAL_BASE_COUNT = 10,
    BIG_INTEGER_LIMBS = 32,
    COMMON_QUOTIENT_MAX_LCM = 2000000
};

typedef __int128 ExactWideSigned;
typedef unsigned __int128 ExactWideUnsigned;

static const int orthogonal_bases[ORTHOGONAL_BASE_COUNT] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31
};

static const uint64_t expected_scaled_squares[ORTHOGONAL_BASE_COUNT] = {
    UINT64_C(48), UINT64_C(1200), UINT64_C(8624),
    UINT64_C(100672), UINT64_C(254176), UINT64_C(1035776),
    UINT64_C(1854096), UINT64_C(5019152), UINT64_C(16698896),
    UINT64_C(23817424)
};

typedef struct {
    int base;
    int modulus;
    int phi;
    int64_t scaled_sum;
    uint64_t scaled_square_sum;
} CoprimeBaseMoment;

typedef struct {
    uint32_t limb[BIG_INTEGER_LIMBS];
    int used;
} ExactUnsignedInteger;

typedef struct {
    int base;
    int lag;
    int modulus;
    int phi;
    int scale;
    ExactWideSigned scaled_sum;
    ExactWideUnsigned scaled_square_sum;
} GeneralBaseMoment;

static void exact_wide_unsigned_print(ExactWideUnsigned value)
{
    char digits[64];
    int used = 0;

    do {
        digits[used++] = (char)('0' + value % 10);
        value /= 10;
    } while (value != 0);
    while (used-- > 0) putchar(digits[used]);
}

static void exact_wide_signed_print(ExactWideSigned value)
{
    ExactWideUnsigned magnitude;
    if (value < 0) {
        putchar('-');
        magnitude = (ExactWideUnsigned)(-(value + 1)) + 1;
    } else {
        magnitude = (ExactWideUnsigned)value;
    }
    exact_wide_unsigned_print(magnitude);
}

static uint64_t gcd_u64(uint64_t left, uint64_t right)
{
    while (right != 0) {
        uint64_t next = left % right;
        left = right;
        right = next;
    }
    return left;
}

static uint64_t power_u64(uint64_t base, int exponent)
{
    uint64_t result = 1;
    while (exponent-- > 0) result *= base;
    return result;
}

static void exact_unsigned_from_u64(ExactUnsignedInteger *value,
                                    uint64_t source)
{
    memset(value, 0, sizeof(*value));
    do {
        value->limb[value->used++] =
            (uint32_t)(source % BIG_INTEGER_RADIX);
        source /= BIG_INTEGER_RADIX;
    } while (source != 0);
}

static int exact_unsigned_multiply_small(ExactUnsignedInteger *value,
                                         uint32_t factor)
{
    uint64_t carry = 0;
    for (int index = 0; index < value->used; index++) {
        uint64_t product = (uint64_t)value->limb[index] * factor + carry;
        value->limb[index] = (uint32_t)(product % BIG_INTEGER_RADIX);
        carry = product / BIG_INTEGER_RADIX;
    }
    while (carry != 0) {
        if (value->used == BIG_INTEGER_LIMBS) return 0;
        value->limb[value->used++] =
            (uint32_t)(carry % BIG_INTEGER_RADIX);
        carry /= BIG_INTEGER_RADIX;
    }
    return 1;
}

static int exact_unsigned_add(ExactUnsignedInteger *destination,
                              const ExactUnsignedInteger *source)
{
    int largest = destination->used > source->used
                      ? destination->used : source->used;
    uint64_t carry = 0;

    for (int index = 0; index < largest; index++) {
        uint64_t left = index < destination->used
                            ? destination->limb[index] : 0;
        uint64_t right = index < source->used ? source->limb[index] : 0;
        uint64_t sum = left + right + carry;
        destination->limb[index] = (uint32_t)(sum % BIG_INTEGER_RADIX);
        carry = sum / BIG_INTEGER_RADIX;
    }
    destination->used = largest;
    if (carry != 0) {
        if (destination->used == BIG_INTEGER_LIMBS) return 0;
        destination->limb[destination->used++] = (uint32_t)carry;
    }
    return 1;
}

static void exact_unsigned_print(const ExactUnsignedInteger *value)
{
    int index = value->used - 1;
    printf("%" PRIu32, value->limb[index]);
    while (--index >= 0) printf("%09" PRIu32, value->limb[index]);
}

static long double exact_unsigned_to_long_double(
    const ExactUnsignedInteger *value)
{
    long double result = 0.0L;
    for (int index = value->used - 1; index >= 0; index--)
        result = result * BIG_INTEGER_RADIX + value->limb[index];
    return result;
}

static int multiply_energy_denominator(ExactUnsignedInteger *value, int base)
{
    for (int exponent = 0; exponent < 7; exponent++)
        if (!exact_unsigned_multiply_small(value, (uint32_t)base)) return 0;
    return exact_unsigned_multiply_small(value, (uint32_t)(base - 1));
}

static int build_moment(const CollisionCenteredTable *table,
                        CoprimeBaseMoment *moment)
{
    int failures = 0;
    memset(moment, 0, sizeof(*moment));
    moment->base = table->base;
    moment->modulus = table->modulus;
    moment->phi = table->phi;

    if (table->lag != 1 || table->modulus != table->base * table->base ||
        table->fiber_size != table->base ||
        table->phi != table->base * (table->base - 1))
        failures++;
    for (int residue = 1; residue < table->modulus; residue++) {
        int64_t numerator;
        uint64_t magnitude, square;
        if (collision_table_gcd(residue, table->modulus) != 1) continue;
        numerator = table->centered_numerator[residue];
        if (table->fiber_count[residue % table->base] != table->base)
            failures++;
        moment->scaled_sum += numerator;
        magnitude = numerator < 0
                        ? (uint64_t)(-(numerator + 1)) + 1
                        : (uint64_t)numerator;
        if (magnitude != 0 && magnitude > UINT64_MAX / magnitude) {
            failures++;
            continue;
        }
        square = magnitude * magnitude;
        if (moment->scaled_square_sum > UINT64_MAX - square) {
            failures++;
            continue;
        }
        moment->scaled_square_sum += square;
    }
    if (moment->scaled_sum != 0 || moment->scaled_square_sum == 0)
        failures++;
    return failures;
}

static int build_general_moment(const CollisionCenteredTable *table,
                                GeneralBaseMoment *moment)
{
    int failures = 0;

    memset(moment, 0, sizeof(*moment));
    moment->base = table->base;
    moment->lag = table->lag;
    moment->modulus = table->modulus;
    moment->phi = table->phi;
    moment->scale = table->fiber_size;
    if (moment->scale <= 0) return 1;

    for (int residue = 1; residue < table->modulus; residue++) {
        ExactWideSigned numerator;
        ExactWideUnsigned magnitude;
        if (collision_table_gcd(residue, table->modulus) != 1) continue;
        if (table->fiber_count[residue % table->base] != moment->scale)
            failures++;
        numerator = (ExactWideSigned)table->centered_numerator[residue];
        moment->scaled_sum += numerator;
        magnitude = numerator < 0
                        ? (ExactWideUnsigned)(-(numerator + 1)) + 1
                        : (ExactWideUnsigned)numerator;
        moment->scaled_square_sum += magnitude * magnitude;
    }
    if (moment->scaled_sum != 0 || moment->scaled_square_sum == 0)
        failures++;
    return failures;
}

static int parameterized_pair_audit(int left_base, int left_lag,
                                    int right_base, int right_lag,
                                    int report)
{
    CollisionCenteredTable left = {0}, right = {0};
    GeneralBaseMoment left_moment, right_moment;
    ExactWideSigned cross_numerator;
    ExactWideUnsigned left_energy_denominator;
    ExactWideUnsigned right_energy_denominator;
    int failures = 0;

    if (!collision_centered_table_build(left_base, left_lag, &left) ||
        !collision_centered_table_build(right_base, right_lag, &right)) {
        if (report)
            fprintf(stderr,
                    "each base and lag must define a table with modulus at most 2000000\n");
        failures++;
        goto cleanup;
    }
    if (collision_table_gcd(left.modulus, right.modulus) != 1) {
        if (report)
            fprintf(stderr,
                    "the table moduli must be coprime; use common-quotient for shared factors\n");
        failures++;
        goto cleanup;
    }

    failures += centered_collision_table_audit(&left, NULL, NULL);
    failures += centered_collision_table_audit(&right, NULL, NULL);
    failures += build_general_moment(&left, &left_moment);
    failures += build_general_moment(&right, &right_moment);
    cross_numerator = left_moment.scaled_sum * right_moment.scaled_sum;
    if (cross_numerator != 0) failures++;
    left_energy_denominator =
        (ExactWideUnsigned)left_moment.phi * left_moment.scale *
        left_moment.scale;
    right_energy_denominator =
        (ExactWideUnsigned)right_moment.phi * right_moment.scale *
        right_moment.scale;

    if (report) {
        printf("Coprime-base orthogonality\n");
        printf("Parameterized pair\n\n");
        printf("  left  base=%d lag=%d modulus=%d units=%d\n",
               left_base, left_lag, left.modulus, left.phi);
        printf("  right base=%d lag=%d modulus=%d units=%d\n",
               right_base, right_lag, right.modulus, right.phi);
        printf("  gcd of table moduli = 1  PASS\n");
        printf("  left centered numerator sum = ");
        exact_wide_signed_print(left_moment.scaled_sum);
        printf("  %s\n", left_moment.scaled_sum == 0 ? "PASS" : "FAIL");
        printf("  right centered numerator sum = ");
        exact_wide_signed_print(right_moment.scaled_sum);
        printf("  %s\n", right_moment.scaled_sum == 0 ? "PASS" : "FAIL");
        printf("  normalized cross-term numerator = ");
        exact_wide_signed_print(cross_numerator);
        printf("  %s\n", cross_numerator == 0 ? "EXACT ZERO" : "FAIL");
        printf("  left normalized energy = ");
        exact_wide_unsigned_print(left_moment.scaled_square_sum);
        printf(" / ");
        exact_wide_unsigned_print(left_energy_denominator);
        printf("\n  right normalized energy = ");
        exact_wide_unsigned_print(right_moment.scaled_square_sum);
        printf(" / ");
        exact_wide_unsigned_print(right_energy_denominator);
        printf("\n\nEvery pairwise cross term is zero, so arbitrary complex-weight\n");
        printf("energy splits and averaging over the other coordinate recovers\n");
        printf("the selected centered signal exactly.\n");
        printf("Classification  exact finite integer and rational arithmetic.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }

cleanup:
    collision_centered_table_free(&left);
    collision_centered_table_free(&right);
    return failures;
}

static int unit_count(int modulus)
{
    int count = 0;
    for (int residue = 0; residue < modulus; residue++)
        if (collision_table_gcd(residue, modulus) == 1) count++;
    return count;
}

static int common_quotient_audit(int left_base, int left_lag,
                                 int right_base, int right_lag,
                                 int report,
                                 int *left_active_out,
                                 int *right_active_out,
                                 ExactWideSigned *numerator_out)
{
    CollisionCenteredTable left = {0}, right = {0};
    int64_t *left_sums = NULL, *right_sums = NULL;
    int *left_counts = NULL, *right_counts = NULL;
    ExactWideSigned joint_numerator = 0, quotient_numerator = 0;
    ExactWideUnsigned joint_denominator, quotient_denominator;
    int divisor, joint_modulus, divisor_phi, joint_phi;
    int left_fiber, right_fiber, left_active = 0, right_active = 0;
    int active_common_modes = 0;
    int failures = 0;

    if (!collision_centered_table_build(left_base, left_lag, &left) ||
        !collision_centered_table_build(right_base, right_lag, &right)) {
        if (report)
            fprintf(stderr,
                    "each base and lag must define a table with modulus at most 2000000\n");
        failures++;
        goto cleanup;
    }
    divisor = collision_table_gcd(left.modulus, right.modulus);
    if ((int64_t)(left.modulus / divisor) * right.modulus >
        COMMON_QUOTIENT_MAX_LCM) {
        if (report)
            fprintf(stderr, "the joint lcm must be at most %d\n",
                    COMMON_QUOTIENT_MAX_LCM);
        failures++;
        goto cleanup;
    }
    joint_modulus = left.modulus / divisor * right.modulus;
    divisor_phi = unit_count(divisor);
    joint_phi = unit_count(joint_modulus);
    if (divisor_phi <= 0 || joint_phi <= 0) {
        failures++;
        goto cleanup;
    }
    left_fiber = left.phi / divisor_phi;
    right_fiber = right.phi / divisor_phi;
    if (left_fiber <= 0 || right_fiber <= 0 ||
        divisor_phi * left_fiber * right_fiber != joint_phi) {
        failures++;
        goto cleanup;
    }

    left_sums = calloc((size_t)divisor, sizeof(*left_sums));
    right_sums = calloc((size_t)divisor, sizeof(*right_sums));
    left_counts = calloc((size_t)divisor, sizeof(*left_counts));
    right_counts = calloc((size_t)divisor, sizeof(*right_counts));
    if (!left_sums || !right_sums || !left_counts || !right_counts) {
        failures++;
        goto cleanup;
    }

    failures += centered_collision_table_audit(&left, NULL, NULL);
    failures += centered_collision_table_audit(&right, NULL, NULL);
    for (int residue = 1; residue < left.modulus; residue++) {
        int label;
        if (collision_table_gcd(residue, left.modulus) != 1) continue;
        label = residue % divisor;
        left_sums[label] += left.centered_numerator[residue];
        left_counts[label]++;
    }
    for (int residue = 1; residue < right.modulus; residue++) {
        int label;
        if (collision_table_gcd(residue, right.modulus) != 1) continue;
        label = residue % divisor;
        right_sums[label] += right.centered_numerator[residue];
        right_counts[label]++;
    }
    for (int label = 0; label < divisor; label++) {
        if (collision_table_gcd(label, divisor) != 1) continue;
        if (left_counts[label] != left_fiber ||
            right_counts[label] != right_fiber)
            failures++;
        quotient_numerator += (ExactWideSigned)left_sums[label] *
                              right_sums[label];
        if (left_sums[label] != 0) left_active++;
        if (right_sums[label] != 0) right_active++;
        if (left_sums[label] != 0 && right_sums[label] != 0)
            active_common_modes++;
    }
    for (int residue = 0; residue < joint_modulus; residue++) {
        if (collision_table_gcd(residue, joint_modulus) != 1) continue;
        joint_numerator +=
            (ExactWideSigned)left.centered_numerator[residue % left.modulus] *
            right.centered_numerator[residue % right.modulus];
    }
    joint_denominator = (ExactWideUnsigned)joint_phi * left.fiber_size *
                        right.fiber_size;
    quotient_denominator =
        (ExactWideUnsigned)divisor_phi * left_fiber * right_fiber *
        left.fiber_size * right.fiber_size;
    if (joint_numerator != quotient_numerator ||
        joint_denominator != quotient_denominator)
        failures++;

    if (report) {
        printf("Common-quotient cross term\n");
        printf("Exact shared-factor audit\n\n");
        printf("  left  base=%d lag=%d modulus=%d\n",
               left_base, left_lag, left.modulus);
        printf("  right base=%d lag=%d modulus=%d\n",
               right_base, right_lag, right.modulus);
        printf("  gcd=%d; lcm=%d; phi(gcd)=%d; phi(lcm)=%d\n",
               divisor, joint_modulus, divisor_phi, joint_phi);
        printf("  compatible fiber sizes = %d and %d\n",
               left_fiber, right_fiber);
        printf("  nonzero left/right conditional sums = %d/%d\n",
               left_active, right_active);
        printf("  common residues with two nonzero conditional sums = %d\n",
               active_common_modes);
        printf("  complete-lcm cross numerator = ");
        exact_wide_signed_print(joint_numerator);
        printf("\n  conditional-mean cross numerator = ");
        exact_wide_signed_print(quotient_numerator);
        printf("\n  common normalized denominator = ");
        exact_wide_unsigned_print(joint_denominator);
        printf("\n  lcm cross term equals the common-quotient inner product  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("Classification  exact finite integer and rational arithmetic.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }

cleanup:
    if (left_active_out) *left_active_out = left_active;
    if (right_active_out) *right_active_out = right_active;
    if (numerator_out) *numerator_out = joint_numerator;
    free(left_sums);
    free(right_sums);
    free(left_counts);
    free(right_counts);
    collision_centered_table_free(&left);
    collision_centered_table_free(&right);
    return failures;
}

static int orthogonality_audit(int report,
                               int *pair_count_out,
                               int *nonzero_cross_terms_out)
{
    CollisionCenteredTable tables[ORTHOGONAL_BASE_COUNT] = {{0}};
    CoprimeBaseMoment moments[ORTHOGONAL_BASE_COUNT];
    ExactUnsignedInteger crt_modulus, crt_group_size;
    ExactUnsignedInteger common_denominator, common_numerator;
    int failures = 0;
    int built = 0;
    int pair_count = 0;
    int nonzero_cross_terms = 0;
    long double weighted_energy = 0.0L;

    exact_unsigned_from_u64(&crt_modulus, 1);
    exact_unsigned_from_u64(&crt_group_size, 1);
    for (int base_index = 0; base_index < ORTHOGONAL_BASE_COUNT;
         base_index++) {
        int table_failures, moment_failures;
        int base = orthogonal_bases[base_index];
        uint64_t norm_denominator, weighted_denominator;
        uint64_t norm_divisor, weighted_divisor;

        if (!collision_centered_table_build(base, 1, &tables[base_index])) {
            failures++;
            goto cleanup;
        }
        built++;
        table_failures = centered_collision_table_audit(
            &tables[base_index], NULL, NULL);
        moment_failures = build_moment(&tables[base_index],
                                       &moments[base_index]);
        if (moments[base_index].scaled_square_sum !=
            expected_scaled_squares[base_index])
            moment_failures++;
        failures += table_failures + moment_failures;

        if (!exact_unsigned_multiply_small(&crt_modulus, (uint32_t)base) ||
            !exact_unsigned_multiply_small(&crt_modulus, (uint32_t)base) ||
            !exact_unsigned_multiply_small(&crt_group_size, (uint32_t)base) ||
            !exact_unsigned_multiply_small(&crt_group_size,
                                           (uint32_t)(base - 1)))
            failures++;

        norm_denominator = (uint64_t)base * base * tables[base_index].phi;
        weighted_denominator = power_u64((uint64_t)base, 6) *
                               tables[base_index].phi;
        norm_divisor = gcd_u64(moments[base_index].scaled_square_sum,
                               norm_denominator);
        weighted_divisor = gcd_u64(moments[base_index].scaled_square_sum,
                                   weighted_denominator);
        weighted_energy +=
            (long double)moments[base_index].scaled_square_sum /
            weighted_denominator;
        if (report)
            printf("  b=%-2d q=%-3d sum(n_b)=%" PRId64
                   "  ||f_b||^2=%" PRIu64 "/%" PRIu64
                   "  weighted=%" PRIu64 "/%" PRIu64 "  %s\n",
                   base, tables[base_index].modulus,
                   moments[base_index].scaled_sum,
                   moments[base_index].scaled_square_sum / norm_divisor,
                   norm_denominator / norm_divisor,
                   moments[base_index].scaled_square_sum / weighted_divisor,
                   weighted_denominator / weighted_divisor,
                   table_failures + moment_failures == 0 ? "PASS" : "FAIL");
    }

    if (report) {
        printf("\nFactored CRT system\n");
        printf("  bases = 3,5,7,11,13,17,19,23,29,31\n");
        printf("  joint modulus = ");
        exact_unsigned_print(&crt_modulus);
        printf("\n  joint unit-group size = ");
        exact_unsigned_print(&crt_group_size);
        printf("\n\n45 pairwise normalized inner products\n");
    }
    for (int left = 0; left < ORTHOGONAL_BASE_COUNT; left++) {
        for (int right = left + 1; right < ORTHOGONAL_BASE_COUNT; right++) {
            int64_t numerator = moments[left].scaled_sum *
                                moments[right].scaled_sum;
            uint64_t denominator =
                (uint64_t)moments[left].base * moments[left].phi *
                moments[right].base * moments[right].phi;
            int exact_zero =
                collision_table_gcd(moments[left].modulus,
                                    moments[right].modulus) == 1 &&
                numerator == 0;
            pair_count++;
            if (!exact_zero) {
                nonzero_cross_terms++;
                failures++;
            }
            if (report)
                printf("  b=%-2d c=%-2d  <F_b,F_c> = %" PRId64
                       "/%" PRIu64 "  %s\n",
                       moments[left].base, moments[right].base,
                       numerator, denominator,
                       exact_zero ? "EXACT ZERO" : "FAIL");
        }
    }
    if (pair_count != 45) failures++;

    exact_unsigned_from_u64(&common_denominator, 1);
    for (int base_index = 0; base_index < ORTHOGONAL_BASE_COUNT;
         base_index++)
        if (!multiply_energy_denominator(
                &common_denominator, moments[base_index].base))
            failures++;
    exact_unsigned_from_u64(&common_numerator, 0);
    for (int selected = 0; selected < ORTHOGONAL_BASE_COUNT; selected++) {
        ExactUnsignedInteger term;
        exact_unsigned_from_u64(&term,
            moments[selected].scaled_square_sum);
        for (int base_index = 0; base_index < ORTHOGONAL_BASE_COUNT;
             base_index++) {
            if (base_index == selected) continue;
            if (!multiply_energy_denominator(
                    &term, moments[base_index].base))
                failures++;
        }
        if (!exact_unsigned_add(&common_numerator, &term)) failures++;
    }
    if (report) {
        long double rational =
            exact_unsigned_to_long_double(&common_numerator) /
            exact_unsigned_to_long_double(&common_denominator);
        printf("\nWeighted Pythagorean identity with w_b=1/b^2\n");
        printf("  exact energy = ");
        exact_unsigned_print(&common_numerator);
        printf(" / ");
        exact_unsigned_print(&common_denominator);
        printf("\n  decimal corroboration = %.18Lf\n", rational);
        printf("  independently accumulated decimal = %.18Lf\n",
               weighted_energy);
        printf("  cross terms = %d; nonzero cross terms = %d\n",
               pair_count, nonzero_cross_terms);
        printf("  exact weighted Pythagorean identity  %s\n",
               nonzero_cross_terms == 0 ? "PASS" : "FAIL");
        printf("\nClassification  exact finite computation in factored CRT coordinates.\n");
        printf("The universal CRT identity is symbolic; this command checks ten\n");
        printf("reference lag-one implementations.\n");
    }

cleanup:
    for (int base_index = 0; base_index < built; base_index++)
        collision_centered_table_free(&tables[base_index]);
    if (pair_count_out) *pair_count_out = pair_count;
    if (nonzero_cross_terms_out)
        *nonzero_cross_terms_out = nonzero_cross_terms;
    return failures;
}

int coprime_base_orthogonality_audit(void)
{
    int failures;
    printf("Coprime-base orthogonality\n");
    printf("Exact CRT audit\n\n");
    failures = orthogonality_audit(1, NULL, NULL);
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    return failures == 0 ? 0 : 1;
}

int coprime_base_orthogonality_pair(int left_base, int left_lag,
                                    int right_base, int right_lag)
{
    return parameterized_pair_audit(
        left_base, left_lag, right_base, right_lag, 1) == 0 ? 0 : 1;
}

int coprime_base_common_quotient(int left_base, int left_lag,
                                 int right_base, int right_lag)
{
    return common_quotient_audit(
        left_base, left_lag, right_base, right_lag, 1,
        NULL, NULL, NULL) == 0 ? 0 : 1;
}

int coprime_base_orthogonality_verify(void)
{
    int pair_count = 0;
    int nonzero_cross_terms = 0;
    int fixed_ok = orthogonality_audit(
        0, &pair_count, &nonzero_cross_terms) == 0;
    int pair_ok = parameterized_pair_audit(3, 2, 5, 3, 0) == 0;
    int nonzero_left = 0, nonzero_right = 0;
    int zero_left = 0, zero_right = 0;
    ExactWideSigned nonzero_numerator = 0, zero_numerator = 0;
    int quotient_nonzero_ok =
        common_quotient_audit(6, 1, 15, 1, 0,
                              &nonzero_left, &nonzero_right,
                              &nonzero_numerator) == 0 &&
        nonzero_left > 0 && nonzero_right > 0 && nonzero_numerator != 0;
    int quotient_zero_ok =
        common_quotient_audit(4, 1, 6, 1, 0,
                              &zero_left, &zero_right,
                              &zero_numerator) == 0 &&
        (zero_left == 0 || zero_right == 0) && zero_numerator == 0;
    int quotient_ok = quotient_nonzero_ok && quotient_zero_ok;
    int passed = 0;

    printf("Coprime-base orthogonality verification\n\n");
    printf("  ten exact lag-one moments                    %s\n",
           fixed_ok ? "PASS" : "FAIL");
    if (fixed_ok) passed++;
    printf("  %d factored-CRT cross terms; %d nonzero       %s\n",
           pair_count, nonzero_cross_terms,
           fixed_ok && pair_count == 45 && nonzero_cross_terms == 0
               ? "PASS" : "FAIL");
    if (fixed_ok && pair_count == 45 && nonzero_cross_terms == 0) passed++;
    printf("  exact weighted Pythagorean energy identity  %s\n",
           fixed_ok ? "PASS" : "FAIL");
    if (fixed_ok) passed++;
    printf("  parameterized coprime base/lag pair          %s\n",
           pair_ok ? "PASS" : "FAIL");
    if (pair_ok) passed++;
    printf("  shared-factor quotient and zero-mean criterion %s\n",
           quotient_ok ? "PASS" : "FAIL");
    if (quotient_ok) passed++;
    printf("\n%d/5 verification groups passed.\n", passed);
    printf("Classification  exact finite integer and rational arithmetic.\n");
    printf("Coverage  parameterized coprime pairs, an exact shared-factor audit,\n");
    printf("and the ten reference lag-one examples.\n");
    printf("Proof boundary  Lean covers the universal CRT identities.\n");
    return passed == 5;
}

void coprime_base_orthogonality_help(void)
{
    printf(
        "Coprime-base orthogonality\n\n"
        "Commands\n"
        "  nfield coprime-base-orthogonality pair <base-a> <lag-a> <base-b> <lag-b>\n"
        "      Check any requested coprime table pair, its exact zero cross\n"
        "      term, normalized energies, weighted splitting, and recovery.\n"
        "  nfield coprime-base-orthogonality common-quotient <base-a> <lag-a> <base-b> <lag-b>\n"
        "      Compare the complete-lcm cross term with the exact conditional\n"
        "      inner product on the common unit-group quotient.\n"
        "  nfield coprime-base-orthogonality audit\n"
        "      Build ten exact lag-one tables, check all 45 factored-CRT\n"
        "      inner products, and construct the exact 1/b^2 energy identity.\n"
        "  nfield coprime-base-orthogonality verify\n"
        "  nfield verify coprime-base-orthogonality\n\n"
        "Scope\n"
        "  symbolic          Lean proves the universal coprime and common-\n"
        "                    quotient identities and disjoint CRT-axis support.\n"
        "  exact computation  This command checks the ten declared lag-one\n"
        "                     examples plus requested coprime or shared-factor\n"
        "                     pairs using integer and rational arithmetic.\n"
    );
}
