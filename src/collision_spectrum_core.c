/* Finite character arithmetic for the collision-spectrum identities. */

#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "collision_spectrum_core.h"
#include "finite_character_core.h"

#define SPECTRUM_IDENTITY_TOLERANCE 2.0e-12L
#define BASE_FIVE_TOLERANCE 2.0e-11L
#define COLLISION_SPECTRUM_MAX_BASE 127

static int modular_power(int base, int exponent, int modulus)
{
    int64_t result = 1;
    int64_t factor = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * factor % modulus;
        factor = factor * factor % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int primitive_root_prime_square(int base)
{
    int modulus = base * base;
    int phi = base * (base - 1);
    int factors[16];
    int factor_count = 0;
    int remaining = phi;

    for (int factor = 2; factor <= remaining / factor; factor++) {
        if (remaining % factor != 0) continue;
        factors[factor_count++] = factor;
        while (remaining % factor == 0) remaining /= factor;
    }
    if (remaining > 1) factors[factor_count++] = remaining;
    for (int candidate = 2; candidate < modulus; candidate++) {
        int valid = collision_table_gcd(candidate, modulus) == 1;
        for (int index = 0; valid && index < factor_count; index++)
            if (modular_power(candidate, phi / factors[index], modulus) == 1)
                valid = 0;
        if (valid) return candidate;
    }
    return 0;
}

int collision_spectrum_context_build(int base,
                                     CollisionSpectrumContext *context)
{
    int residue = 1;

    if (!context || !finite_character_is_prime(base) || base == 2 ||
        base > COLLISION_SPECTRUM_MAX_BASE)
        return 0;
    memset(context, 0, sizeof(*context));
    context->base = base;
    context->modulus = base * base;
    context->phi = base * (base - 1);
    context->generator = primitive_root_prime_square(base);
    context->discrete_log =
        malloc((size_t)context->modulus * sizeof(*context->discrete_log));
    if (!context->generator || !context->discrete_log ||
        !collision_centered_table_build(base, 1, &context->table)) {
        collision_spectrum_context_free(context);
        return 0;
    }
    for (int value = 0; value < context->modulus; value++)
        context->discrete_log[value] = -1;
    for (int exponent = 0; exponent < context->phi; exponent++) {
        if (context->discrete_log[residue] != -1) {
            collision_spectrum_context_free(context);
            return 0;
        }
        context->discrete_log[residue] = exponent;
        residue = (int)((int64_t)residue * context->generator %
                        context->modulus);
    }
    if (residue != 1 ||
        centered_collision_table_audit(&context->table, NULL, NULL) != 0) {
        collision_spectrum_context_free(context);
        return 0;
    }
    return 1;
}

void collision_spectrum_context_free(CollisionSpectrumContext *context)
{
    if (!context) return;
    free(context->discrete_log);
    collision_centered_table_free(&context->table);
    memset(context, 0, sizeof(*context));
}

int collision_spectrum_character_is_primitive_odd(
    const CollisionSpectrumContext *context, int character_index)
{
    return context && character_index > 0 && character_index < context->phi &&
           character_index % 2 == 1 &&
           character_index % context->base != 0;
}

static long double complex character_bar(
    const CollisionSpectrumContext *context,
    int character_index,
    int residue)
{
    int exponent;
    int64_t phase;
    long double angle;

    residue %= context->modulus;
    if (residue < 0) residue += context->modulus;
    exponent = context->discrete_log[residue];
    if (exponent < 0) return 0.0L + I * 0.0L;
    phase = (int64_t)character_index * exponent % context->phi;
    angle = -2.0L * acosl(-1.0L) * phase / context->phi;
    return cosl(angle) + I * sinl(angle);
}

static long double relative_complex_error(long double complex actual,
                                          long double complex expected)
{
    return cabsl(actual - expected) / (1.0L + cabsl(expected));
}

int collision_spectrum_character_compute(
    const CollisionSpectrumContext *context,
    int character_index,
    CollisionSpectrumCharacter *result)
{
    long double complex bernoulli_sum = 0.0L + I * 0.0L;
    long double complex coefficient_numerator = 0.0L + I * 0.0L;
    long double complex short_sum = 0.0L + I * 0.0L;
    long double complex diagonal = 0.0L + I * 0.0L;
    long double complex centering_sum = 0.0L + I * 0.0L;
    long double complex fiber_sum[COLLISION_SPECTRUM_MAX_BASE] = {0};

    if (!result ||
        !collision_spectrum_character_is_primitive_odd(
            context, character_index))
        return 0;
    memset(result, 0, sizeof(*result));
    result->character_index = character_index;
    for (int residue = 1; residue < context->modulus; residue++) {
        long double complex value;
        if (context->discrete_log[residue] < 0) continue;
        value = character_bar(context, character_index, residue);
        bernoulli_sum += (long double)residue * value;
        fiber_sum[residue % context->base] += value;
        centering_sum +=
            ((long double)context->table.fiber_sum[residue % context->base] /
             context->base) * value;
        coefficient_numerator +=
            (long double)context->table.centered_numerator[residue] * value;
    }
    result->bernoulli_one = bernoulli_sum / context->modulus;
    result->l_one_magnitude =
        acosl(-1.0L) * cabsl(result->bernoulli_one) / context->base;
    result->coefficient_direct = coefficient_numerator /
        ((long double)context->base * context->phi);

    for (int value = 1; value < context->base; value++)
        short_sum += character_bar(context, character_index, value);
    result->short_sum = short_sum;
    for (int row = 0; row < context->base; row++) {
        int diagonal_index = row * (context->base + 1);
        diagonal += character_bar(
                        context, character_index, diagonal_index + 1) -
                    character_bar(
                        context, character_index, diagonal_index);
    }
    result->diagonal_direct = diagonal;
    result->diagonal_reduced =
        -2.0L * character_bar(
            context, character_index, context->base + 1) * short_sum;
    result->coefficient_factored =
        -result->bernoulli_one * conjl(diagonal) / context->phi;
    result->parity_error = cabsl(
        character_bar(context, character_index, context->modulus - 1) +
        1.0L);
    result->primitive_kernel_gap = cabsl(
        character_bar(context, character_index, context->base + 1) -
        1.0L);
    for (int fiber = 1; fiber < context->base; fiber++) {
        long double error = cabsl(fiber_sum[fiber]);
        if (error > result->fiber_cancellation_error)
            result->fiber_cancellation_error = error;
    }
    result->centering_error = cabsl(centering_sum) / context->phi;
    result->diagonal_error = relative_complex_error(
        result->diagonal_direct, result->diagonal_reduced);
    result->factorization_error = relative_complex_error(
        result->coefficient_direct, result->coefficient_factored);
    return 1;
}

int collision_spectrum_transform_compute(
    const CollisionSpectrumContext *context,
    int character_index,
    int multiplier,
    CollisionSpectrumTransform *result)
{
    CollisionSpectrumCharacter character;
    long double complex fractional = 0.0L + I * 0.0L;
    long double complex floor_sum = 0.0L + I * 0.0L;
    long double complex chi_multiplier;

    if (!context || !result || multiplier <= 0 ||
        multiplier >= context->modulus ||
        context->discrete_log[multiplier] < 0 ||
        !collision_spectrum_character_compute(
            context, character_index, &character))
        return 0;
    memset(result, 0, sizeof(*result));
    result->multiplier = multiplier;
    for (int residue = 1; residue < context->modulus; residue++) {
        int64_t product;
        int remainder;
        long double complex value;
        if (context->discrete_log[residue] < 0) continue;
        product = (int64_t)multiplier * residue;
        remainder = (int)(product % context->modulus);
        value = character_bar(context, character_index, residue);
        fractional += value *
            ((long double)remainder / context->modulus);
        floor_sum += value * (long double)(product / context->modulus);
    }
    chi_multiplier = conjl(character_bar(
        context, character_index, multiplier));
    result->fractional_direct = fractional;
    result->fractional_expected =
        chi_multiplier * character.bernoulli_one;
    result->floor_direct = floor_sum;
    result->floor_expected =
        ((long double)multiplier - chi_multiplier) *
        character.bernoulli_one;
    result->fractional_error = relative_complex_error(
        result->fractional_direct, result->fractional_expected);
    result->floor_error = relative_complex_error(
        result->floor_direct, result->floor_expected);
    return 1;
}

static long double correlation(const CollisionSpectrumCharacter *characters,
                               int count)
{
    long double sum_x = 0.0L, sum_y = 0.0L;
    long double covariance = 0.0L;
    long double variance_x = 0.0L, variance_y = 0.0L;

    for (int index = 0; index < count; index++) {
        sum_x += cabsl(characters[index].short_sum);
        sum_y += cabsl(characters[index].bernoulli_one);
    }
    sum_x /= count;
    sum_y /= count;
    for (int index = 0; index < count; index++) {
        long double dx = cabsl(characters[index].short_sum) - sum_x;
        long double dy = cabsl(characters[index].bernoulli_one) - sum_y;
        covariance += dx * dy;
        variance_x += dx * dx;
        variance_y += dy * dy;
    }
    return covariance / sqrtl(variance_x * variance_y);
}

int collision_spectrum_base_audit(int base, CollisionSpectrumSummary *summary)
{
    CollisionSpectrumContext context = {0};
    CollisionSpectrumCharacter *characters = NULL;
    int expected_count;
    int character_count = 0;
    int pass = 1;
    long double pi = acosl(-1.0L);
    long double special_left = 0.0L;
    long double special_right;

    if (!summary || !collision_spectrum_context_build(base, &context))
        return 0;
    memset(summary, 0, sizeof(*summary));
    expected_count = (base - 1) * (base - 1) / 2;
    characters = calloc((size_t)expected_count, sizeof(*characters));
    if (!characters) goto failure;
    for (int character_index = 1; character_index < context.phi;
         character_index += 2) {
        if (character_index % base == 0) continue;
        if (character_count >= expected_count ||
            !collision_spectrum_character_compute(
                &context, character_index, &characters[character_count]))
            goto failure;
        character_count++;
    }
    if (character_count != expected_count) goto failure;

    summary->base = base;
    summary->modulus = context.modulus;
    summary->generator = context.generator;
    summary->primitive_odd_count = character_count;
    summary->correlation = correlation(characters, character_count);
    for (int index = 0; index < character_count; index++) {
        CollisionSpectrumCharacter *character = &characters[index];
        long double diagonal_magnitude = cabsl(character->diagonal_direct);
        long double bernoulli_magnitude = cabsl(character->bernoulli_one);
        long double l_square = character->l_one_magnitude *
                               character->l_one_magnitude;
        summary->diagonal_second_moment +=
            diagonal_magnitude * diagonal_magnitude;
        special_left += l_square * diagonal_magnitude * diagonal_magnitude;
        if (character->diagonal_error > summary->maximum_diagonal_error)
            summary->maximum_diagonal_error = character->diagonal_error;
        if (character->fiber_cancellation_error >
            summary->maximum_fiber_cancellation_error)
            summary->maximum_fiber_cancellation_error =
                character->fiber_cancellation_error;
        if (character->centering_error > summary->maximum_centering_error)
            summary->maximum_centering_error = character->centering_error;
        if (character->factorization_error >
            summary->maximum_factorization_error)
            summary->maximum_factorization_error =
                character->factorization_error;
        if (character->parity_error > SPECTRUM_IDENTITY_TOLERANCE ||
            character->primitive_kernel_gap <= SPECTRUM_IDENTITY_TOLERANCE ||
            character->fiber_cancellation_error >
                SPECTRUM_IDENTITY_TOLERANCE ||
            character->centering_error > SPECTRUM_IDENTITY_TOLERANCE ||
            character->diagonal_error > SPECTRUM_IDENTITY_TOLERANCE ||
            character->factorization_error > SPECTRUM_IDENTITY_TOLERANCE)
            pass = 0;
        if (base == 5) {
            long double bernoulli_square =
                bernoulli_magnitude * bernoulli_magnitude;
            long double diagonal_square =
                diagonal_magnitude * diagonal_magnitude;
            long double l_fourth = l_square * l_square;
            long double coefficient_expected =
                5.0L * sqrtl(5.0L) /
                (4.0L * pi * pi) * l_square;
            long double relation_error = fabsl(
                diagonal_magnitude - sqrtl(5.0L) * bernoulli_magnitude) /
                (1.0L + diagonal_magnitude);
            long double coefficient_error = fabsl(
                cabsl(character->coefficient_direct) - coefficient_expected) /
                (1.0L + coefficient_expected);
            if (relation_error > summary->base_five_relation_error)
                summary->base_five_relation_error = relation_error;
            if (coefficient_error > summary->base_five_coefficient_error)
                summary->base_five_coefficient_error = coefficient_error;
            summary->base_five_bernoulli_fourth_moment +=
                bernoulli_square * bernoulli_square;
            summary->base_five_diagonal_fourth_moment +=
                diagonal_square * diagonal_square;
            summary->base_five_l_one_fourth_moment += l_fourth;
        }
    }
    summary->energy_numerator = 0;
    for (int residue = 0; residue < context.modulus; residue++)
        summary->energy_numerator +=
            context.table.centered_numerator[residue] *
            context.table.centered_numerator[residue];
    {
        long double expected =
            (long double)2 * base * (base - 1) * (base - 1);
        summary->diagonal_second_moment_error = fabsl(
            summary->diagonal_second_moment - expected) / (1.0L + expected);
        if (summary->diagonal_second_moment_error >
            SPECTRUM_IDENTITY_TOLERANCE)
            pass = 0;
    }
    special_right = pi * pi * context.phi *
        (long double)summary->energy_numerator /
        ((long double)base * base * base * base);
    summary->special_value_moment_error =
        fabsl(special_left - special_right) / (1.0L + special_right);
    if (summary->special_value_moment_error > SPECTRUM_IDENTITY_TOLERANCE)
        pass = 0;
    if (!isfinite(summary->correlation)) pass = 0;
    if (base == 5) {
        long double expected_l_fourth =
            192.0L * pi * pi * pi * pi / 625.0L;
        if (summary->energy_numerator != 1200 ||
            summary->base_five_relation_error > BASE_FIVE_TOLERANCE ||
            summary->base_five_coefficient_error > BASE_FIVE_TOLERANCE ||
            fabsl(summary->base_five_bernoulli_fourth_moment - 192.0L) >
                BASE_FIVE_TOLERANCE ||
            fabsl(summary->base_five_diagonal_fourth_moment - 4800.0L) >
                20.0L * BASE_FIVE_TOLERANCE ||
            fabsl(summary->base_five_l_one_fourth_moment -
                  expected_l_fourth) > BASE_FIVE_TOLERANCE)
            pass = 0;
    }
    summary->pass = pass;
    free(characters);
    collision_spectrum_context_free(&context);
    return pass;

failure:
    free(characters);
    collision_spectrum_context_free(&context);
    return 0;
}
