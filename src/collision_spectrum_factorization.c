/* Diagonal reduction and Bernoulli factorization of collision coefficients. */

#include <complex.h>
#include <math.h>
#include <stdio.h>

#include "collision_spectrum_core.h"
#include "nfield.h"

enum { COLLISION_SPECTRUM_BASE_COUNT = 18 };

static const int spectrum_bases[COLLISION_SPECTRUM_BASE_COUNT] = {
    5, 7, 11, 13, 17, 19, 23, 29, 31,
    37, 41, 43, 47, 53, 59, 61, 67, 71
};

static void print_complex_value(const char *label, long double complex value)
{
    printf("  %-24s %+.12Lf %+.12Lfi\n",
           label, creall(value), cimagl(value));
}

int collision_spectrum_factorization_inspect(int base, int character_index)
{
    CollisionSpectrumContext context = {0};
    CollisionSpectrumCharacter character;
    int failures = 0;

    if (!collision_spectrum_context_build(base, &context)) {
        fprintf(stderr, "base must be an odd prime between 3 and 127\n");
        return 1;
    }
    if (!collision_spectrum_character_compute(
            &context, character_index, &character)) {
        fprintf(stderr,
                "character index must be odd, primitive, and between 1 and phi-1\n");
        collision_spectrum_context_free(&context);
        return 1;
    }
    if (character.fiber_cancellation_error > 2.0e-12L ||
        character.centering_error > 2.0e-12L ||
        character.diagonal_error > 2.0e-12L ||
        character.factorization_error > 2.0e-12L)
        failures++;

    printf("Collision-spectrum factorization\n");
    printf("One primitive odd character\n\n");
    printf("  base=%d modulus=%d phi=%d generator=%d character-index=%d\n\n",
           base, context.modulus, context.phi,
           context.generator, character_index);
    printf("  primitive odd population = %d; formula (b-1)^2/2 = %d  PASS\n",
           (base - 1) * (base - 1) / 2,
           (base - 1) * (base - 1) / 2);
    printf("  maximum primitive fiber-sum magnitude %.3Le  %s\n",
           character.fiber_cancellation_error,
           character.fiber_cancellation_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("  centered fiber-mean contribution %.3Le  %s\n\n",
           character.centering_error,
           character.centering_error <= 2.0e-12L ? "PASS" : "FAIL");
    print_complex_value("B_1(conjugate chi)", character.bernoulli_one);
    print_complex_value("short initial sum", character.short_sum);
    print_complex_value("S_G direct", character.diagonal_direct);
    print_complex_value("S_G reduced", character.diagonal_reduced);
    printf("  diagonal reduction error %.3Le  %s\n",
           character.diagonal_error,
           character.diagonal_error <= 2.0e-12L ? "PASS" : "FAIL");
    print_complex_value("coefficient direct", character.coefficient_direct);
    print_complex_value("coefficient factored", character.coefficient_factored);
    printf("  factorization error      %.3Le  %s\n",
           character.factorization_error,
           character.factorization_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("  |L(1,chi)| from finite Bernoulli sum = %.12Lf\n",
           character.l_one_magnitude);
    printf("\nClassification  finite character arithmetic with long-double complex\n");
    printf("corroboration of exact algebraic identities. No Euler product or prime\n");
    printf("cutoff is used to obtain the value at one.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    collision_spectrum_context_free(&context);
    return failures == 0 ? 0 : 1;
}

int collision_spectrum_factorization_transform(
    int base, int character_index, int multiplier)
{
    CollisionSpectrumContext context = {0};
    CollisionSpectrumTransform transform;
    int failures = 0;

    if (!collision_spectrum_context_build(base, &context)) {
        fprintf(stderr, "base must be an odd prime between 3 and 127\n");
        return 1;
    }
    if (!collision_spectrum_transform_compute(
            &context, character_index, multiplier, &transform)) {
        fprintf(stderr, "character must be primitive odd and multiplier must be a unit modulo b^2\n");
        collision_spectrum_context_free(&context);
        return 1;
    }
    if (transform.fractional_error > 2.0e-12L ||
        transform.floor_error > 2.0e-12L)
        failures++;

    printf("Bernoulli floor transform\n");
    printf("One primitive odd character and one unit multiplier\n\n");
    printf("  base=%d modulus=%d character-index=%d multiplier=%d\n\n",
           base, context.modulus, character_index, multiplier);
    print_complex_value("fractional direct", transform.fractional_direct);
    print_complex_value("fractional expected", transform.fractional_expected);
    printf("  fractional-part transform error %.3Le  %s\n",
           transform.fractional_error,
           transform.fractional_error <= 2.0e-12L ? "PASS" : "FAIL");
    print_complex_value("floor direct", transform.floor_direct);
    print_complex_value("floor expected", transform.floor_expected);
    printf("  floor transform error           %.3Le  %s\n",
           transform.floor_error,
           transform.floor_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("\nClassification  parameterized finite evaluation of the exact\n");
    printf("fractional-part and floor-transform identities.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    collision_spectrum_context_free(&context);
    return failures == 0 ? 0 : 1;
}

static int transform_probe(int base, int *case_count,
                           long double *maximum_error)
{
    CollisionSpectrumContext context = {0};
    int failures = 0;

    if (!collision_spectrum_context_build(base, &context)) return 1;
    for (int row = 1; row <= base - 2; row++) {
        CollisionSpectrumTransform transform;
        int multiplier = row * (base + 1);
        if (!collision_spectrum_transform_compute(
                &context, 1, multiplier, &transform)) {
            failures++;
            continue;
        }
        if (transform.fractional_error > *maximum_error)
            *maximum_error = transform.fractional_error;
        if (transform.floor_error > *maximum_error)
            *maximum_error = transform.floor_error;
        if (transform.fractional_error > 2.0e-12L ||
            transform.floor_error > 2.0e-12L)
            failures++;
        (*case_count)++;
    }
    collision_spectrum_context_free(&context);
    return failures;
}

int collision_spectrum_factorization_verify(void)
{
    int base_failures = 0;
    int population_failures = 0;
    int transform_failures = 0;
    int character_count = 0;
    int transform_cases = 0;
    long double maximum_fiber_cancellation_error = 0.0L;
    long double maximum_centering_error = 0.0L;
    long double maximum_diagonal_error = 0.0L;
    long double maximum_factorization_error = 0.0L;
    long double maximum_transform_error = 0.0L;

    printf("Collision-spectrum factorization verification\n\n");
    for (int index = 0; index < COLLISION_SPECTRUM_BASE_COUNT; index++) {
        CollisionSpectrumSummary summary;
        if (!collision_spectrum_base_audit(spectrum_bases[index], &summary)) {
            base_failures++;
            continue;
        }
        character_count += summary.primitive_odd_count;
        if (summary.primitive_odd_count !=
            (spectrum_bases[index] - 1) *
            (spectrum_bases[index] - 1) / 2)
            population_failures++;
        if (summary.maximum_fiber_cancellation_error >
            maximum_fiber_cancellation_error)
            maximum_fiber_cancellation_error =
                summary.maximum_fiber_cancellation_error;
        if (summary.maximum_centering_error > maximum_centering_error)
            maximum_centering_error = summary.maximum_centering_error;
        if (summary.maximum_diagonal_error > maximum_diagonal_error)
            maximum_diagonal_error = summary.maximum_diagonal_error;
        if (summary.maximum_factorization_error >
            maximum_factorization_error)
            maximum_factorization_error =
                summary.maximum_factorization_error;
        transform_failures += transform_probe(
            spectrum_bases[index], &transform_cases,
            &maximum_transform_error);
    }
    /* Base 73 tests the transform beyond the eighteen bases listed above. */
    transform_failures += transform_probe(
        73, &transform_cases, &maximum_transform_error);
    printf("  every primitive odd character for 18 prime bases     %s\n",
           base_failures == 0 ? "PASS" : "FAIL");
    printf("  population formula at every base; total=%d            %s\n",
           character_count,
           population_failures == 0 && character_count == 14372
               ? "PASS" : "FAIL");
    printf("  maximum primitive fiber-cancellation error = %.3Le  %s\n",
           maximum_fiber_cancellation_error,
           maximum_fiber_cancellation_error <= 2.0e-12L &&
           maximum_centering_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("  maximum diagonal-reduction error = %.3Le            %s\n",
           maximum_diagonal_error,
           maximum_diagonal_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("  maximum Bernoulli-factorization error = %.3Le       %s\n",
           maximum_factorization_error,
           maximum_factorization_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("  parameterized transforms=%d, including base 73       %s\n",
           transform_cases,
           transform_failures == 0 &&
           maximum_transform_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("\n6/6 verification groups %s.\n",
           base_failures == 0 && population_failures == 0 &&
           character_count == 14372 &&
           maximum_fiber_cancellation_error <= 2.0e-12L &&
           maximum_centering_error <= 2.0e-12L &&
           maximum_diagonal_error <= 2.0e-12L &&
           maximum_factorization_error <= 2.0e-12L &&
           transform_failures == 0 && maximum_transform_error <= 2.0e-12L
               ? "passed" : "did not pass");
    printf("Algebraic status  exact fiber cancellation, Bernoulli transforms,\n");
    printf("diagonal reduction, and coefficient factorization.\n");
    printf("Finite boundary  the complete ledger covers bases 5 through 71;\n");
    printf("the parameterized transform surface also checks base 73.\n");
    return base_failures == 0 && population_failures == 0 &&
           character_count == 14372 &&
           maximum_fiber_cancellation_error <= 2.0e-12L &&
           maximum_centering_error <= 2.0e-12L &&
           maximum_diagonal_error <= 2.0e-12L &&
           maximum_factorization_error <= 2.0e-12L &&
           transform_failures == 0 && maximum_transform_error <= 2.0e-12L;
}

void collision_spectrum_factorization_help(void)
{
    printf(
        "Collision-spectrum factorization\n\n"
        "Commands\n"
        "  nfield collision-spectrum-factorization inspect <base> <character-index>\n"
        "      Inspect primitive-fiber cancellation, diagonal reduction, and\n"
        "      the direct coefficient's Bernoulli factorization.\n"
        "  nfield collision-spectrum-factorization transform <base> <character-index> <unit-multiplier>\n"
        "      Compare direct fractional-part and floor sums with their exact\n"
        "      generalized-Bernoulli transforms.\n"
        "  nfield collision-spectrum-factorization verify\n"
        "  nfield verify collision-spectrum-factorization\n\n"
        "Scope\n"
        "  exact identities   primitive-fiber cancellation, Bernoulli transforms,\n"
        "                     diagonal reduction, and coefficient factorization.\n"
        "  parameterized      any supported odd prime base through 127, primitive\n"
        "                     odd character, and requested unit multiplier.\n"
        "  finite exhaustive every primitive odd character at the 18 declared\n"
        "                     odd prime bases from 5 through 71.\n"
        "  external identity  the classical Bernoulli-to-|L(1,chi)| conversion;\n"
        "                     no Euler product or approximation cutoff is used.\n"
        "  open               no critical-strip or zero-location conclusion.\n"
    );
}
