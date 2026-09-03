#ifndef NFIELD_PERIODIC_ZETA_CORE_H
#define NFIELD_PERIODIC_ZETA_CORE_H

#include <complex.h>
#include <stddef.h>

typedef struct {
    int base;
    int lag;
    int exponent;
    int modulus;
    int phi;
    int generator;
    int cyclic_order;
    int unit_count;
    int diagonal_count;
    int *units;
    int *diagonal;
    int *logarithm;
    signed char *negative_component;
} PeriodicZetaContext;

typedef struct {
    long double complex left;
    long double complex right;
    long double complex l_value;
    long double complex diagonal;
    long double relative_error;
} PeriodicZetaComparison;

int periodic_zeta_context_build(int base, int lag,
                                PeriodicZetaContext *context,
                                char *error, size_t error_capacity);
void periodic_zeta_context_free(PeriodicZetaContext *context);

int periodic_zeta_character_valid(const PeriodicZetaContext *context,
                                  int character_index);
int periodic_zeta_character_count(const PeriodicZetaContext *context);
long double complex periodic_zeta_character_value(
    const PeriodicZetaContext *context, int character_index, int residue);
long double complex periodic_zeta_diagonal_boundary(
    const PeriodicZetaContext *context, int character_index);
long double complex periodic_zeta_bernoulli_one(
    const PeriodicZetaContext *context, int character_index);
long double complex periodic_zeta_gauss_sum(
    const PeriodicZetaContext *context, int character_index);

int periodic_zeta_model_comparison(
    const PeriodicZetaContext *context, int character_index, int residue,
    long double complex s, PeriodicZetaComparison *comparison);
int periodic_zeta_transform_comparison(
    const PeriodicZetaContext *context, int character_index,
    long double complex s, PeriodicZetaComparison *comparison);

int periodic_zeta_boundary_transform(
    const PeriodicZetaContext *context, int character_index, int side,
    long double complex *value);
int periodic_zeta_finite_collision_coefficient(
    const PeriodicZetaContext *context, int character_index,
    long double complex *direct, long double complex *factorized);
int periodic_zeta_boundary_values(
    const PeriodicZetaContext *context, int character_index,
    long double complex *left_direct, long double complex *left_factorized,
    long double complex *right_direct, long double complex *right_factorized,
    long double complex *right_l_value);

#endif
