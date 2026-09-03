/* Exact finite checks for the collision-coordinate lemma and its gate. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"

#define COLLISION_COORDINATE_MAX_PRIME 4093
#define COLLISION_COORDINATE_MAX_MODULUS 1000000

static int cc_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0) return 0;
    return 1;
}

static int cc_valid(int prime, int base, int report)
{
    if (!cc_is_prime(prime)) {
        if (report) fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (prime > COLLISION_COORDINATE_MAX_PRIME) {
        if (report)
            fprintf(stderr, "prime must not exceed %d\n",
                    COLLISION_COORDINATE_MAX_PRIME);
        return 0;
    }
    if (base < 2 || base >= prime) {
        if (report)
            fprintf(stderr, "the theorem requires 2 <= base < p\n");
        return 0;
    }
    return 1;
}

static int cc_normalize(int64_t value, int prime)
{
    int result = (int)(value % prime);
    return result < 0 ? result + prime : result;
}

static int cc_inverse(int value, int prime)
{
    int64_t old_remainder = value;
    int64_t remainder = prime;
    int64_t old_coefficient = 1;
    int64_t coefficient = 0;
    while (remainder != 0) {
        int64_t quotient = old_remainder / remainder;
        int64_t next = old_remainder - quotient * remainder;
        old_remainder = remainder;
        remainder = next;
        next = old_coefficient - quotient * coefficient;
        old_coefficient = coefficient;
        coefficient = next;
    }
    return old_remainder == 1 ? cc_normalize(old_coefficient, prime) : 0;
}

static int cc_digit(int residue, int prime, int base)
{
    return (int)((int64_t)base * residue / prime);
}

static int cc_direct_count(int prime, int base, int multiplier)
{
    int count = 0;
    for (int residue = 1; residue < prime; residue++) {
        int image = (int)((int64_t)multiplier * residue % prime);
        count += cc_digit(residue, prime, base) ==
                 cc_digit(image, prime, base);
    }
    return count;
}

static int cc_congruence_count(int prime, int base, int multiplier)
{
    int count = 0;
    for (int coordinate = 1; coordinate < prime; coordinate++) {
        int image = (int)((int64_t)multiplier * coordinate % prime);
        count += coordinate % base == image % base;
    }
    return count;
}

static int cc_general_valid(int modulus, int base, int multiplier, int report)
{
    if (modulus < 2 || modulus > COLLISION_COORDINATE_MAX_MODULUS) {
        if (report)
            fprintf(stderr, "N must be between 2 and %d\n",
                    COLLISION_COORDINATE_MAX_MODULUS);
        return 0;
    }
    if (base < 2 || base >= modulus) {
        if (report) fprintf(stderr, "general conjugation requires 2 <= base < N\n");
        return 0;
    }
    if (collision_table_gcd(modulus, base) != 1) {
        if (report) fprintf(stderr, "N must be coprime to the base\n");
        return 0;
    }
    int normalized = cc_normalize(multiplier, modulus);
    if (normalized == 0 || collision_table_gcd(normalized, modulus) != 1) {
        if (report) fprintf(stderr, "g must represent a unit modulo N\n");
        return 0;
    }
    return 1;
}

static int cc_general_conjugation_model(
    int modulus, int base, int multiplier,
    int *decomposition_ok, int *class_bijection_ok,
    int *pointwise_ok, int *direct_count, int *congruence_count)
{
    if (!decomposition_ok || !class_bijection_ok || !pointwise_ok ||
        !direct_count || !congruence_count ||
        !cc_general_valid(modulus, base, multiplier, 0))
        return 0;

    int *digit_to_class = malloc((size_t)base * sizeof(*digit_to_class));
    int *class_to_digit = malloc((size_t)base * sizeof(*class_to_digit));
    if (!digit_to_class || !class_to_digit) {
        free(digit_to_class);
        free(class_to_digit);
        return 0;
    }
    for (int index = 0; index < base; index++) {
        digit_to_class[index] = -1;
        class_to_digit[index] = -1;
    }

    int normalized = cc_normalize(multiplier, modulus);
    *decomposition_ok = 1;
    *class_bijection_ok = 1;
    *pointwise_ok = 1;
    *direct_count = 0;
    *congruence_count = 0;

    for (int residue = 1; residue < modulus; residue++) {
        int digit = cc_digit(residue, modulus, base);
        int coordinate = (int)((int64_t)base * residue % modulus);
        int residue_class = coordinate % base;
        if ((int64_t)base * residue !=
            (int64_t)modulus * digit + coordinate)
            *decomposition_ok = 0;
        if ((digit_to_class[digit] >= 0 &&
             digit_to_class[digit] != residue_class) ||
            (class_to_digit[residue_class] >= 0 &&
             class_to_digit[residue_class] != digit))
            *class_bijection_ok = 0;
        digit_to_class[digit] = residue_class;
        class_to_digit[residue_class] = digit;

        int image = (int)((int64_t)normalized * residue % modulus);
        int image_coordinate =
            (int)((int64_t)normalized * coordinate % modulus);
        int transported_image =
            (int)((int64_t)base * image % modulus);
        int digit_match =
            digit == cc_digit(image, modulus, base);
        int class_match =
            coordinate % base == image_coordinate % base;
        if (image_coordinate != transported_image ||
            digit_match != class_match)
            *pointwise_ok = 0;
        *direct_count += digit_match;
    }
    for (int index = 0; index < base; index++) {
        if (digit_to_class[index] < 0 || class_to_digit[index] < 0)
            *class_bijection_ok = 0;
    }
    for (int coordinate = 1; coordinate < modulus; coordinate++) {
        int image =
            (int)((int64_t)normalized * coordinate % modulus);
        *congruence_count += coordinate % base == image % base;
    }

    free(digit_to_class);
    free(class_to_digit);
    return 1;
}

int collision_coordinate_conjugation_values(
    int modulus, int base, int multiplier,
    int *direct_count, int *congruence_count, int *structure_ok)
{
    int decomposition = 0;
    int bijection = 0;
    int pointwise = 0;
    if (!structure_ok ||
        !cc_general_conjugation_model(
            modulus, base, multiplier, &decomposition, &bijection,
            &pointwise, direct_count, congruence_count))
        return 0;
    *structure_ok = decomposition && bijection && pointwise;
    return 1;
}

static int cc_coordinate(int prime, int base, int multiplier)
{
    int denominator = cc_normalize(1LL - multiplier, prime);
    if (denominator == 0) return 0;
    return (int)((int64_t)base * cc_inverse(denominator, prime) % prime);
}

static int cc_formula_count(int prime, int base, int coordinate,
                            int *wrapping_indices)
{
    int quotient = (prime - 1) / base;
    int wraps = 0;
    for (int index = 1; index <= quotient; index++) {
        int residue = (int)((int64_t)index * coordinate % prime);
        wraps += residue > index * base;
    }
    if (wrapping_indices) *wrapping_indices = wraps;
    return 2 * wraps;
}

int collision_coordinate_values(int prime, int base, int multiplier,
                                int *direct_count, int *formula_count,
                                int *coordinate)
{
    if (!direct_count || !formula_count || !coordinate ||
        !cc_valid(prime, base, 0))
        return 0;
    int normalized = cc_normalize(multiplier, prime);
    if (normalized <= 1) return 0;
    int c = cc_coordinate(prime, base, normalized);
    *direct_count = cc_direct_count(prime, base, normalized);
    *formula_count = cc_formula_count(prime, base, c, NULL);
    *coordinate = c;
    return 1;
}

static int cc_check_conjugation(int prime, int base, int multiplier)
{
    for (int residue = 1; residue < prime; residue++) {
        int image = (int)((int64_t)multiplier * residue % prime);
        int coordinate = (int)((int64_t)base * residue % prime);
        int image_coordinate =
            (int)((int64_t)multiplier * coordinate % prime);
        if ((cc_digit(residue, prime, base) ==
             cc_digit(image, prime, base)) !=
            (coordinate % base == image_coordinate % base))
            return 0;
    }
    return cc_direct_count(prime, base, multiplier) ==
           cc_congruence_count(prime, base, multiplier);
}

static int cc_family_value(int prime, int base, int parameter)
{
    int denominator = base - parameter;
    return cc_normalize(
        -(int64_t)parameter * cc_inverse(denominator, prime), prime);
}

static int cc_check_model(int prime, int base,
                          int *conjugation_ok, int *coordinate_ok,
                          int *parity_ok, int *gate_ok)
{
    unsigned char *observed = calloc((size_t)prime, 1);
    unsigned char *predicted = calloc((size_t)prime, 1);
    if (!observed || !predicted) {
        free(observed);
        free(predicted);
        return 0;
    }
    *conjugation_ok = 1;
    *coordinate_ok = 1;
    *parity_ok = 1;
    *gate_ok = 1;
    for (int multiplier = 1; multiplier < prime; multiplier++) {
        int direct = cc_direct_count(prime, base, multiplier);
        if (!cc_check_conjugation(prime, base, multiplier))
            *conjugation_ok = 0;
        if (direct % 2 != 0) *parity_ok = 0;
        if (multiplier > 1) {
            int coordinate = cc_coordinate(prime, base, multiplier);
            if (direct != cc_formula_count(
                    prime, base, coordinate, NULL))
                *coordinate_ok = 0;
        }
        if (direct == 0) observed[multiplier] = 1;
    }
    for (int parameter = 1; parameter < base; parameter++) {
        int multiplier = cc_family_value(prime, base, parameter);
        if (multiplier <= 0 || predicted[multiplier]) *gate_ok = 0;
        predicted[multiplier] = 1;
    }
    for (int multiplier = 1; multiplier < prime; multiplier++)
        if (observed[multiplier] != predicted[multiplier]) *gate_ok = 0;
    free(observed);
    free(predicted);
    return 1;
}

int collision_coordinate_inspect(int prime, int multiplier, int base)
{
    if (!cc_valid(prime, base, 1)) return 1;
    int normalized = cc_normalize(multiplier, prime);
    if (normalized <= 1) {
        fprintf(stderr, "g must represent a nonidentity nonzero multiplier\n");
        return 1;
    }
    int direct = 0;
    int formula = 0;
    int coordinate = 0;
    int wraps = 0;
    int conjugation = cc_check_conjugation(prime, base, normalized);
    collision_coordinate_values(
        prime, base, normalized, &direct, &formula, &coordinate);
    cc_formula_count(prime, base, coordinate, &wraps);
    int ok = conjugation && direct == formula && direct % 2 == 0;

    printf("Collision-coordinate lemma\n\n");
    printf("  p=%d base=%d multiplier g=%d\n", prime, base, normalized);
    printf("  Q=floor((p-1)/b)=%d\n", (prime - 1) / base);
    printf("  c(g)=[b(1-g)^(-1)]_p=%d\n", coordinate);
    printf("  wrapping indices=%d\n", wraps);
    printf("  direct C(g)=%d\n", direct);
    printf("  coordinate formula 2*#wraps=%d  %s\n", formula,
           direct == formula ? "PASS" : "FAIL");
    printf("  bin conjugation and collision congruence  %s\n",
           conjugation ? "PASS" : "FAIL");
    printf("  bilateral parity C(g) even               %s\n",
           direct % 2 == 0 ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int collision_coordinate_conjugation(int modulus, int multiplier, int base)
{
    if (!cc_general_valid(modulus, base, multiplier, 1)) return 1;
    int decomposition = 0;
    int bijection = 0;
    int pointwise = 0;
    int direct = 0;
    int congruence = 0;
    if (!cc_general_conjugation_model(
            modulus, base, multiplier, &decomposition, &bijection,
            &pointwise, &direct, &congruence))
        return 1;
    int ok = decomposition && bijection && pointwise && direct == congruence;
    printf("Base conjugation on a coprime modulus\n\n");
    printf("  N=%d base=%d multiplier g=%d\n",
           modulus, base, cc_normalize(multiplier, modulus));
    printf("  br=N*delta_N(r)+[br]_N at every residue       %s\n",
           decomposition ? "PASS" : "FAIL");
    printf("  digit bins biject with transformed classes     %s\n",
           bijection ? "PASS" : "FAIL");
    printf("  collision equivalence holds point by point      %s\n",
           pointwise ? "PASS" : "FAIL");
    printf("  direct C_N(g)=%d; congruence count=%d          %s\n",
           direct, congruence, direct == congruence ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int collision_coordinate_gate(int prime, int base)
{
    if (!cc_valid(prime, base, 1)) return 1;
    int conjugation = 0;
    int coordinate = 0;
    int parity = 0;
    int gate = 0;
    if (!cc_check_model(prime, base, &conjugation, &coordinate,
                        &parity, &gate))
        return 1;
    int zero_count = 0;
    for (int multiplier = 1; multiplier < prime; multiplier++)
        zero_count += cc_direct_count(prime, base, multiplier) == 0;
    int ok = conjugation && coordinate && parity && gate &&
             zero_count == base - 1;

    printf("Gate-width theorem\n\n");
    printf("  p=%d base=%d\n", prime, base);
    printf("  zero family {-u/(b-u): 1<=u<b}\n");
    printf("  observed collision-free multipliers=%d\n", zero_count);
    printf("  exact width b-1=%d                         %s\n",
           base - 1, zero_count == base - 1 ? "PASS" : "FAIL");
    printf("  family equals complete observed zero set   %s\n",
           gate ? "PASS" : "FAIL");
    printf("  coordinate formula at every nonidentity g  %s\n",
           coordinate ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int collision_coordinate_verify(void)
{
    int models = 0;
    int conjugation = 1;
    int coordinate = 1;
    int parity = 1;
    int gate = 1;
    for (int base = 2; base <= 16; base++) {
        for (int prime = base + 1; prime <= 127; prime++) {
            if (!cc_is_prime(prime)) continue;
            int model_conjugation = 0;
            int model_coordinate = 0;
            int model_parity = 0;
            int model_gate = 0;
            models++;
            if (!cc_check_model(prime, base, &model_conjugation,
                                &model_coordinate, &model_parity,
                                &model_gate)) {
                conjugation = coordinate = parity = gate = 0;
                continue;
            }
            conjugation = conjugation && model_conjugation;
            coordinate = coordinate && model_coordinate;
            parity = parity && model_parity;
            gate = gate && model_gate;
        }
    }
    int general_models = 0;
    int general_conjugation = 1;
    for (int base = 2; base <= 16; base++) {
        for (int modulus = base + 1; modulus <= 64; modulus++) {
            if (cc_is_prime(modulus) ||
                collision_table_gcd(modulus, base) != 1)
                continue;
            for (int multiplier = 1; multiplier < modulus; multiplier++) {
                if (collision_table_gcd(multiplier, modulus) != 1) continue;
                int decomposition = 0;
                int bijection = 0;
                int pointwise = 0;
                int direct = 0;
                int congruence = 0;
                general_models++;
                if (!cc_general_conjugation_model(
                        modulus, base, multiplier, &decomposition,
                        &bijection, &pointwise, &direct, &congruence) ||
                    !decomposition || !bijection || !pointwise ||
                    direct != congruence)
                    general_conjugation = 0;
            }
        }
    }
    int count_ok = models == 404;
    int passed = count_ok + general_conjugation + conjugation + coordinate +
                 parity + gate;
    printf("Collision-coordinate and gate-width verification\n\n");
    printf("  coprime composite conjugation models=%d         %s\n",
           general_models, general_conjugation ? "PASS" : "FAIL");
    printf("  declared (base, prime) models=%d             %s\n",
           models, count_ok ? "PASS" : "FAIL");
    printf("  bin conjugation and collision congruence      %s\n",
           conjugation ? "PASS" : "FAIL");
    printf("  exact coordinate formula for every g != 1     %s\n",
           coordinate ? "PASS" : "FAIL");
    printf("  bilateral parity including the identity       %s\n",
           parity ? "PASS" : "FAIL");
    printf("  rational zero family and width b-1             %s\n",
           gate ? "PASS" : "FAIL");
    printf("\n%d/6 verification groups passed.\n", passed);
    printf("Computed  every comparison uses exact integer arithmetic.\n");
    printf("Proof boundary  bounded sweeps corroborate the universal identities;\n");
    printf("they do not replace their mathematical proofs.\n");
    return passed == 6;
}

void collision_coordinate_help(void)
{
    printf(
        "Collision coordinate\n\n"
        "Commands\n"
        "  nfield collision-coordinate conjugation <N> <g> [--base <b>]\n"
        "      Check the base conjugation for any coprime modulus and unit.\n"
        "  nfield collision-coordinate inspect <p> <g> [--base <b>]\n"
        "      Compare the direct collision count with the exact coordinate formula.\n"
        "  nfield collision-coordinate gate <p> [--base <b>]\n"
        "      Check the complete rational zero family and gate width b-1.\n"
        "  nfield collision-coordinate verify\n"
        "  nfield verify collision-coordinate\n\n"
        "Scope\n"
        "  object             base conjugation, collision coordinate, and zero gate.\n"
        "  mathematical scope coprime-modulus conjugation, prime coordinate\n"
        "                     formula, bilateral parity, and exact gate width.\n"
        "  exact computation 5824 unit multipliers on coprime composite moduli\n"
        "                     with 2<=b<=16 and b<N<=64, plus all 404 pairs\n"
        "                     with 2<=b<=16 and prime b<p<=127.\n"
        "  boundary           the bounded sweeps check instances and do not prove\n"
        "                     the universal identities.\n"
    );
}
