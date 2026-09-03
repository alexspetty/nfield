#ifndef NFIELD_COLLISION_SPECTRUM_CORE_H
#define NFIELD_COLLISION_SPECTRUM_CORE_H

#include <complex.h>
#include <stdint.h>

#include "nfield.h"

typedef struct {
    int character_index;
    long double complex bernoulli_one;
    long double l_one_magnitude;
    long double complex short_sum;
    long double complex diagonal_direct;
    long double complex diagonal_reduced;
    long double complex coefficient_direct;
    long double complex coefficient_factored;
    long double parity_error;
    long double primitive_kernel_gap;
    long double fiber_cancellation_error;
    long double centering_error;
    long double diagonal_error;
    long double factorization_error;
} CollisionSpectrumCharacter;

typedef struct {
    int multiplier;
    long double complex fractional_direct;
    long double complex fractional_expected;
    long double complex floor_direct;
    long double complex floor_expected;
    long double fractional_error;
    long double floor_error;
} CollisionSpectrumTransform;

typedef struct {
    int base;
    int modulus;
    int phi;
    int generator;
    int *discrete_log;
    CollisionCenteredTable table;
} CollisionSpectrumContext;

typedef struct {
    int base;
    int modulus;
    int generator;
    int primitive_odd_count;
    int64_t energy_numerator;
    long double correlation;
    long double maximum_fiber_cancellation_error;
    long double maximum_centering_error;
    long double maximum_diagonal_error;
    long double maximum_factorization_error;
    long double diagonal_second_moment;
    long double diagonal_second_moment_error;
    long double special_value_moment_error;
    long double base_five_relation_error;
    long double base_five_coefficient_error;
    long double base_five_bernoulli_fourth_moment;
    long double base_five_diagonal_fourth_moment;
    long double base_five_l_one_fourth_moment;
    int pass;
} CollisionSpectrumSummary;

int collision_spectrum_context_build(int base, CollisionSpectrumContext *context);
void collision_spectrum_context_free(CollisionSpectrumContext *context);
int collision_spectrum_character_is_primitive_odd(
    const CollisionSpectrumContext *context, int character_index);
int collision_spectrum_character_compute(
    const CollisionSpectrumContext *context,
    int character_index,
    CollisionSpectrumCharacter *result);
int collision_spectrum_transform_compute(
    const CollisionSpectrumContext *context,
    int character_index,
    int multiplier,
    CollisionSpectrumTransform *result);
int collision_spectrum_base_audit(int base, CollisionSpectrumSummary *summary);

#endif
