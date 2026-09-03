/* Exact finite forms of the prime-base lag-one collision energy. */

#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"

#define PBCE_MAX_BASE 251

static long long pbce_abs(long long value)
{
    return value < 0 ? -value : value;
}

static long long pbce_gcd(long long first, long long second)
{
    first = pbce_abs(first);
    second = pbce_abs(second);
    while (second != 0) {
        long long remainder = first % second;
        first = second;
        second = remainder;
    }
    return first == 0 ? 1 : first;
}

static int pbce_is_prime(int value)
{
    if (value < 2) return 0;
    if (value % 2 == 0) return value == 2;
    for (int divisor = 3; divisor <= value / divisor; divisor += 2)
        if (value % divisor == 0) return 0;
    return 1;
}

static int pbce_valid_base(int base)
{
    return base >= 3 && base <= PBCE_MAX_BASE && base % 2 == 1 &&
           pbce_is_prime(base);
}

static long long pbce_inverse_mod(long long value, long long modulus)
{
    long long old_remainder = value;
    long long remainder = modulus;
    long long old_coefficient = 1;
    long long coefficient = 0;
    while (remainder != 0) {
        long long quotient = old_remainder / remainder;
        long long next_remainder = old_remainder - quotient * remainder;
        long long next_coefficient =
            old_coefficient - quotient * coefficient;
        old_remainder = remainder;
        remainder = next_remainder;
        old_coefficient = coefficient;
        coefficient = next_coefficient;
    }
    if (old_remainder != 1) return 0;
    old_coefficient %= modulus;
    if (old_coefficient < 0) old_coefficient += modulus;
    return old_coefficient;
}

/* Return the exact integer 12*m*s(h,m). */
static int pbce_dedekind_scaled(long long h, long long m, long long *value)
{
    if (!value || m < 1) return 0;
    h %= m;
    if (h < 0) h += m;
    if (m == 1) {
        *value = 0;
        return 1;
    }
    if (h == 0 || pbce_gcd(h, m) != 1) return 0;
    if (h == 1) {
        *value = (m - 1) * (m - 2);
        return 1;
    }
    long long reciprocal = 0;
    if (!pbce_dedekind_scaled(m % h, h, &reciprocal)) return 0;
    long long numerator =
        h * h + m * m + 1 - 3 * h * m - m * reciprocal;
    if (numerator % h != 0) return 0;
    *value = numerator / h;
    return 1;
}

static int pbce_dedekind_scaled_direct(
        long long h, long long m, long long *value)
{
    if (!value || m < 1) return 0;
    h %= m;
    if (h < 0) h += m;
    if (m == 1) {
        *value = 0;
        return 1;
    }
    if (h == 0 || pbce_gcd(h, m) != 1) return 0;
    long long product_sum = 0;
    for (long long residue = 1; residue < m; residue++) {
        long long image = h * residue % m;
        product_sum +=
            (2 * residue - m) * (2 * image - m);
    }
    if ((3 * product_sum) % m != 0) return 0;
    *value = 3 * product_sum / m;
    return 1;
}

static void pbce_print_fraction(long long numerator, long long denominator)
{
    long long divisor = pbce_gcd(numerator, denominator);
    numerator /= divisor;
    denominator /= divisor;
    if (denominator == 1) printf("%lld", numerator);
    else printf("%lld/%lld", numerator, denominator);
}

int prime_base_collision_energy_dedekind(
        int base, long long *total_scaled, long long *diagonal_scaled,
        long long *upper_scaled, long long *lower_scaled,
        int *weight_law, int *correction_cancellation,
        int *inverse_symmetry)
{
    if (!total_scaled || !diagonal_scaled || !upper_scaled ||
        !lower_scaled || !weight_law || !correction_cancellation ||
        !inverse_symmetry || !pbce_valid_base(base))
        return 0;

    long long modulus = (long long)base * base;
    int *weights = calloc((size_t)modulus, sizeof(*weights));
    if (!weights) return 0;

    long long total = 0;
    long long diagonal = 0;
    long long upper = 0;
    long long lower = 0;
    int symmetry_ok = 1;
    for (int first = 1; first < base; first++) {
        long long inverse = pbce_inverse_mod(first, modulus);
        if (inverse == 0) {
            free(weights);
            return 0;
        }
        for (int second = 1; second < base; second++) {
            long long argument = inverse * second % modulus;
            long long dedekind = 0;
            long long inverse_dedekind = 0;
            long long inverse_argument = pbce_inverse_mod(argument, modulus);
            if (!pbce_dedekind_scaled(
                    argument, modulus, &dedekind) ||
                inverse_argument == 0 ||
                !pbce_dedekind_scaled(
                    inverse_argument, modulus, &inverse_dedekind)) {
                free(weights);
                return 0;
            }
            if (dedekind != inverse_dedekind) symmetry_ok = 0;
            weights[argument]++;
            total += 4 * dedekind;
            if (first == second) diagonal += 4 * dedekind;
            else if (second > first) upper += 4 * dedekind;
            else lower += 4 * dedekind;
        }
    }

    int weight_ok = 1;
    long long correction = 0;
    long long weighted_total = 0;
    for (int alpha = 1; alpha < base; alpha++) {
        int column_total = 0;
        for (int beta = 0; beta < base; beta++) {
            long long argument = alpha + (long long)base * beta;
            long long dedekind = 0;
            long long small_dedekind = 0;
            if (!pbce_dedekind_scaled(
                    argument, modulus, &dedekind) ||
                !pbce_dedekind_scaled(alpha, base, &small_dedekind)) {
                free(weights);
                return 0;
            }
            column_total += weights[argument];
            weighted_total += 4LL * weights[argument] * dedekind;
            correction += (long long)weights[argument] * small_dedekind;
        }
        if (column_total != base - 1) weight_ok = 0;
    }
    if (weighted_total != total) weight_ok = 0;

    long long diagonal_closed =
        4LL * (base - 1) * (modulus - 1) * (modulus - 2);
    if (diagonal != diagonal_closed || upper != lower ||
        diagonal + upper + lower != total)
        symmetry_ok = 0;

    *total_scaled = total;
    *diagonal_scaled = diagonal;
    *upper_scaled = upper;
    *lower_scaled = lower;
    *weight_law = weight_ok;
    *correction_cancellation = correction == 0;
    *inverse_symmetry = symmetry_ok;
    free(weights);
    return 1;
}

int prime_base_collision_energy_values(
        int base, PrimeBaseCollisionEnergy *result)
{
    if (!result || !pbce_valid_base(base)) return 0;
    *result = (PrimeBaseCollisionEnergy){0};
    long long modulus = (long long)base * base;
    int *crossings = calloc((size_t)modulus, sizeof(*crossings));
    int *centered = calloc((size_t)modulus, sizeof(*centered));
    long long *column_sum = calloc((size_t)base, sizeof(*column_sum));
    if (!crossings || !centered || !column_sum) {
        free(crossings);
        free(centered);
        free(column_sum);
        return 0;
    }

    long long energy_numerator = 0;
    long long raw_variance = 0;
    long long half_centered_square = 0;
    int threshold_ok = 1;
    int units = 0;
    for (long long multiplier = 1; multiplier < modulus; multiplier++) {
        if (multiplier % base == 0) continue;
        int crossing_count = 0;
        for (int digit = 0; digit < base; digit++) {
            long long diagonal = (long long)(base + 1) * digit;
            long long residue = diagonal * multiplier % modulus;
            int threshold = residue >= modulus - multiplier;
            int floor_difference =
                (int)(((diagonal + 1) * multiplier) / modulus -
                      (diagonal * multiplier) / modulus);
            if (threshold != floor_difference) threshold_ok = 0;
            crossing_count += threshold;
        }
        int residue_class = (int)(multiplier % base);
        int centered_value =
            crossing_count - 1 - (int)((multiplier - 1) / base);
        long long class_centered_numerator =
            (long long)base * centered_value + base - residue_class;
        crossings[multiplier] = crossing_count;
        centered[multiplier] = centered_value;
        column_sum[residue_class] += crossing_count;
        energy_numerator +=
            class_centered_numerator * class_centered_numerator;
        raw_variance += (long long)centered_value * centered_value;
        long long half_centered = 2LL * centered_value + 1;
        half_centered_square += half_centered * half_centered;
        units++;
    }

    int column_ok = 1;
    for (int residue_class = 1; residue_class < base; residue_class++) {
        long long expected =
            (long long)base * (base - 1) / 2 + residue_class;
        if (column_sum[residue_class] != expected) column_ok = 0;
    }

    int reflection_ok = 1;
    for (long long multiplier = 1; multiplier < modulus; multiplier++) {
        if (multiplier % base == 0) continue;
        long long reflected = modulus - multiplier;
        int residue_class = (int)(multiplier % base);
        int reflected_class = (int)(reflected % base);
        long long first_numerator =
            (long long)base * centered[multiplier] + base - residue_class;
        long long reflected_numerator =
            (long long)base * centered[reflected] +
            base - reflected_class;
        if (crossings[multiplier] + crossings[reflected] != base ||
            centered[multiplier] + centered[reflected] != -1 ||
            first_numerator + reflected_numerator != 0)
            reflection_ok = 0;
    }

    long long total_scaled = 0;
    long long diagonal_scaled = 0;
    long long upper_scaled = 0;
    long long lower_scaled = 0;
    int weight_ok = 0;
    int correction_ok = 0;
    int symmetry_ok = 0;
    int dedekind_ok = prime_base_collision_energy_dedekind(
        base, &total_scaled, &diagonal_scaled, &upper_scaled, &lower_scaled,
        &weight_ok, &correction_ok, &symmetry_ok);

    int normalization_ok =
        4 * raw_variance ==
            half_centered_square + (long long)base * (base - 1) &&
        6 * energy_numerator ==
            modulus *
                (6 * raw_variance -
                 (long long)(base - 1) * (2 * base - 1)) &&
        12 * energy_numerator ==
            modulus *
                (3 * half_centered_square -
                 (long long)(base - 1) * (base - 2));
    int dictionary_ok = dedekind_ok && total_scaled == 12 * energy_numerator;

    result->base = base;
    result->modulus = (int)modulus;
    result->unit_count = units;
    result->energy_numerator = energy_numerator;
    result->energy_denominator = modulus;
    result->raw_variance = raw_variance;
    result->half_centered_square = half_centered_square;
    result->dedekind_scaled_numerator = total_scaled;
    result->diagonal_scaled_numerator = diagonal_scaled;
    result->upper_scaled_numerator = upper_scaled;
    result->lower_scaled_numerator = lower_scaled;
    result->threshold_equivalence = threshold_ok;
    result->column_law = column_ok;
    result->reflection_law = reflection_ok;
    result->threshold_normalization = normalization_ok;
    result->weight_law = weight_ok;
    result->correction_cancellation = correction_ok;
    result->inverse_symmetry = symmetry_ok;
    result->energy_dictionary = dictionary_ok;

    free(crossings);
    free(centered);
    free(column_sum);
    return threshold_ok && column_ok && reflection_ok && normalization_ok &&
           weight_ok && correction_ok && symmetry_ok && dictionary_ok;
}

int prime_base_collision_energy_inspect(int base)
{
    if (!pbce_valid_base(base)) {
        fprintf(stderr, "base must be an odd prime not exceeding 251\n");
        return 1;
    }
    PrimeBaseCollisionEnergy result = {0};
    int ok = prime_base_collision_energy_values(base, &result);
    long long denominator = 12LL * result.modulus;
    long long off_diagonal =
        result.upper_scaled_numerator + result.lower_scaled_numerator;

    printf("Prime-base collision energy\n\n");
    printf("  base=%d modulus=b^2=%d units=%d\n",
           result.base, result.modulus, result.unit_count);
    printf("  floor difference equals threshold indicator     %s\n",
           result.threshold_equivalence ? "PASS" : "FAIL");
    printf("  carry-table column law                           %s\n",
           result.column_law ? "PASS" : "FAIL");
    printf("  carry-table reflection law                       %s\n",
           result.reflection_law ? "PASS" : "FAIL");
    printf("  threshold and class-centering normalizations     %s\n",
           result.threshold_normalization ? "PASS" : "FAIL");
    printf("  exact centered energy E_b=");
    pbce_print_fraction(result.energy_numerator, result.energy_denominator);
    printf("\n");
    printf("  raw variance V_b=%lld; sum T_b(a)^2=%lld\n",
           result.raw_variance, result.half_centered_square);
    printf("  12*b^2*E_b from carry table=%lld\n",
           12 * result.energy_numerator);
    printf("  12*b^2*E_b from ratio/Dedekind sum=%lld  %s\n",
           result.dedekind_scaled_numerator,
           result.energy_dictionary ? "PASS" : "FAIL");
    printf("  collision-weight column law                      %s\n",
           result.weight_law ? "PASS" : "FAIL");
    printf("  weighted modulus-b correction cancels exactly    %s\n",
           result.correction_cancellation ? "PASS" : "FAIL");
    printf("  inverse symmetry and upper/lower pairing          %s\n",
           result.inverse_symmetry ? "PASS" : "FAIL");
    printf("\nExact finite pole split, common denominator 12*b^2\n");
    printf("  diagonal numerator=%lld  value=", result.diagonal_scaled_numerator);
    pbce_print_fraction(result.diagonal_scaled_numerator, denominator);
    printf("\n  off-diagonal numerator=%lld  value=", off_diagonal);
    pbce_print_fraction(off_diagonal, denominator);
    printf("\n  total numerator=%lld  value=",
           result.dedekind_scaled_numerator);
    pbce_print_fraction(result.dedekind_scaled_numerator, denominator);
    printf("\n\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int prime_base_collision_energy_poles(int base)
{
    if (!pbce_valid_base(base)) {
        fprintf(stderr, "base must be an odd prime not exceeding 251\n");
        return 1;
    }
    long long total = 0;
    long long diagonal = 0;
    long long upper = 0;
    long long lower = 0;
    int weight_ok = 0;
    int correction_ok = 0;
    int symmetry_ok = 0;
    int ok = prime_base_collision_energy_dedekind(
        base, &total, &diagonal, &upper, &lower,
        &weight_ok, &correction_ok, &symmetry_ok);
    long long modulus = (long long)base * base;
    long double scale = 12.0L * modulus * base * base * base;
    printf("Prime-base collision-energy pole split\n\n");
    printf("  base=%d; exact common denominator=12*b^2=%lld\n",
           base, 12 * modulus);
    printf("  diagonal numerator=%lld; diagonal/b^3=%.12Lf\n",
           diagonal, (long double)diagonal / scale);
    printf("  upper numerator=%lld; lower numerator=%lld  %s\n",
           upper, lower, upper == lower ? "PASS" : "FAIL");
    printf("  off-diagonal numerator=%lld; off-diagonal/b^3=%.12Lf\n",
           upper + lower, (long double)(upper + lower) / scale);
    printf("  total numerator=%lld; E_b/b^3=%.12Lf\n",
           total, (long double)total / scale);
    printf("  exact diagonal closed form and ratio pairing      %s\n",
           symmetry_ok ? "PASS" : "FAIL");
    printf("  exact collision-weight and correction laws        %s\n",
           weight_ok && correction_ok ? "PASS" : "FAIL");
    printf("\nResult  %s\n",
           ok && symmetry_ok && weight_ok && correction_ok ? "PASS" : "FAIL");
    return ok && symmetry_ok && weight_ok && correction_ok ? 0 : 1;
}

int prime_base_collision_energy_verify(void)
{
    int carry_ok = 1;
    int dictionary_ok = 1;
    int poles_ok = 1;
    int direct_dedekind_ok = 1;
    int domain_ok = 1;
    int known_ok = 0;
    int prime_models = 0;
    int row_models = 0;
    int ratio_models = 0;
    int direct_models = 0;

    for (int base = 3; base <= 61; base += 2) {
        if (!pbce_is_prime(base)) continue;
        PrimeBaseCollisionEnergy result = {0};
        prime_models++;
        row_models += base * (base - 1);
        ratio_models += (base - 1) * (base - 1);
        if (!prime_base_collision_energy_values(base, &result)) carry_ok = 0;
        if (!result.threshold_equivalence || !result.column_law ||
            !result.reflection_law || !result.threshold_normalization)
            carry_ok = 0;
        if (!result.energy_dictionary || !result.weight_law ||
            !result.correction_cancellation)
            dictionary_ok = 0;
        if (!result.inverse_symmetry ||
            result.upper_scaled_numerator != result.lower_scaled_numerator ||
            result.diagonal_scaled_numerator +
                result.upper_scaled_numerator +
                result.lower_scaled_numerator !=
                result.dedekind_scaled_numerator)
            poles_ok = 0;
        if (base == 3) {
            known_ok = result.energy_numerator == 48 &&
                       result.energy_denominator == 9 &&
                       result.raw_variance == 7 &&
                       result.half_centered_square == 22;
        }
        if (base <= 19) {
            long long modulus = (long long)base * base;
            for (long long h = 1; h < modulus; h++) {
                if (h % base == 0) continue;
                long long reciprocal = 0;
                long long direct = 0;
                direct_models++;
                if (!pbce_dedekind_scaled(h, modulus, &reciprocal) ||
                    !pbce_dedekind_scaled_direct(h, modulus, &direct) ||
                    reciprocal != direct)
                    direct_dedekind_ok = 0;
            }
        }
    }
    PrimeBaseCollisionEnergy rejected = {0};
    domain_ok = !prime_base_collision_energy_values(2, &rejected) &&
                !prime_base_collision_energy_values(9, &rejected) &&
                !prime_base_collision_energy_values(257, &rejected);

    int coverage_ok = prime_models == 17 && row_models > 0 &&
                      ratio_models > 0 && direct_models > 0;
    int passed = carry_ok + dictionary_ok + poles_ok +
                 direct_dedekind_ok + known_ok + domain_ok + coverage_ok;
    printf("Prime-base collision-energy verification\n\n");
    printf("  odd-prime models=%d; carry rows=%d              %s\n",
           prime_models, row_models, carry_ok ? "PASS" : "FAIL");
    printf("  exact collision-ratio pairs=%d                   %s\n",
           ratio_models, dictionary_ok ? "PASS" : "FAIL");
    printf("  diagonal/off-diagonal and inverse pairing        %s\n",
           poles_ok ? "PASS" : "FAIL");
    printf("  direct versus reciprocity Dedekind values=%d      %s\n",
           direct_models, direct_dedekind_ok ? "PASS" : "FAIL");
    printf("  base-three closed fixture E_3=16/3               %s\n",
           known_ok ? "PASS" : "FAIL");
    printf("  even, composite, and over-limit rejection         %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("  declared bounded families are nonempty            %s\n",
           coverage_ok ? "PASS" : "FAIL");
    printf("\n%d/7 verification groups passed.\n", passed);
    printf("Exact boundary  carry counts, centered numerators, collision weights,\n");
    printf("and 12*m-scaled Dedekind sums use signed integer arithmetic.\n");
    printf("Proved  the universal asymptotic is E_b=b^3+O(b^2(log b)^2); this\n");
    printf("finite audit checks the exact identities used by its analytic proof.\n");
    printf("Scope  reusable prime-base carry, Dedekind, and pole objects.\n");
    return passed == 7;
}

void prime_base_collision_energy_help(void)
{
    printf(
        "Prime-base collision energy\n\n"
        "Commands\n"
        "  nfield prime-base-collision-energy inspect <odd-prime-base>\n"
        "      Build the carry table and compare every exact finite form of E_b.\n"
        "  nfield prime-base-collision-energy poles <odd-prime-base>\n"
        "      Show the exact diagonal, upper, lower, and total Dedekind masses.\n"
        "  nfield prime-base-collision-energy verify\n"
        "  nfield verify prime-base-collision-energy\n\n"
        "Example\n"
        "  nfield prime-base-collision-energy inspect 5\n\n"
        "Scope\n"
        "  proved       for odd prime b, E_b=b^3+O(b^2(log b)^2), with leading\n"
        "               diagonal/off-diagonal proportions one-third and two-thirds.\n"
        "  exact        threshold/floor equivalence, column and reflection laws,\n"
        "               class centering, collision weights, modulus-b cancellation,\n"
        "               weight-free Dedekind dictionary, and finite pole split.\n"
        "  finite audit odd prime bases through 61; inspect accepts b<=251.\n"
        "  boundary     C checks exact finite inputs; the uniform analytic big-O\n"
        "               argument remains a symbolic proof.\n"
    );
}
