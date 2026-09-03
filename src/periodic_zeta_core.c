/* Prime-power characters and periodic-zeta arithmetic shared by object commands. */

#include <complex.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "periodic_zeta_core.h"

enum { PERIODIC_ZETA_MAX_MODULUS = 4096 };

static long double pi_value(void)
{
    return acosl(-1.0L);
}

static int gcd_int(int first, int second)
{
    while (second != 0) {
        int temporary = first % second;
        first = second;
        second = temporary;
    }
    return first < 0 ? -first : first;
}

static int is_prime_int(int value)
{
    if (value < 2) return 0;
    if (value % 2 == 0) return value == 2;
    for (int divisor = 3; (long long)divisor * divisor <= value;
         divisor += 2)
        if (value % divisor == 0) return 0;
    return 1;
}

static int modular_power(int base, int exponent, int modulus)
{
    long long result = 1;
    long long factor = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * factor % modulus;
        factor = factor * factor % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int primitive_root_prime_power(int modulus, int phi)
{
    int factors[16];
    int factor_count = 0;
    int remainder = phi;

    for (int prime = 2; (long long)prime * prime <= remainder; prime++) {
        if (remainder % prime != 0) continue;
        factors[factor_count++] = prime;
        while (remainder % prime == 0) remainder /= prime;
    }
    if (remainder > 1) factors[factor_count++] = remainder;

    for (int candidate = 2; candidate < modulus; candidate++) {
        int primitive = gcd_int(candidate, modulus) == 1;
        for (int index = 0; primitive && index < factor_count; index++)
            if (modular_power(candidate, phi / factors[index], modulus) == 1)
                primitive = 0;
        if (primitive) return candidate;
    }
    return 0;
}

static void set_error(char *error, size_t capacity, const char *message)
{
    if (error && capacity > 0) snprintf(error, capacity, "%s", message);
}

int periodic_zeta_context_build(int base, int lag,
                                PeriodicZetaContext *context,
                                char *error, size_t error_capacity)
{
    long long modulus = 1;

    if (!context) return 0;
    memset(context, 0, sizeof(*context));
    if (!is_prime_int(base)) {
        set_error(error, error_capacity, "base must be prime");
        return 0;
    }
    if (lag < 1) {
        set_error(error, error_capacity, "lag must be at least one");
        return 0;
    }
    for (int index = 0; index <= lag; index++) {
        modulus *= base;
        if (modulus > PERIODIC_ZETA_MAX_MODULUS) {
            set_error(error, error_capacity,
                      "base^(lag+1) exceeds the public computation limit 4096");
            return 0;
        }
    }

    context->base = base;
    context->lag = lag;
    context->exponent = lag + 1;
    context->modulus = (int)modulus;
    context->phi = context->modulus - context->modulus / base;
    context->units = malloc((size_t)context->phi * sizeof(*context->units));
    context->diagonal =
        malloc((size_t)context->modulus * sizeof(*context->diagonal));
    context->logarithm =
        malloc((size_t)context->modulus * sizeof(*context->logarithm));
    context->negative_component = calloc(
        (size_t)context->modulus, sizeof(*context->negative_component));
    if (!context->units || !context->diagonal || !context->logarithm ||
        !context->negative_component) {
        set_error(error, error_capacity, "unable to allocate character context");
        periodic_zeta_context_free(context);
        return 0;
    }
    for (int residue = 0; residue < context->modulus; residue++)
        context->logarithm[residue] = -1;

    for (int residue = 1; residue < context->modulus; residue++)
        if (gcd_int(residue, context->modulus) == 1)
            context->units[context->unit_count++] = residue;
    if (context->unit_count != context->phi) {
        set_error(error, error_capacity, "internal unit-count mismatch");
        periodic_zeta_context_free(context);
        return 0;
    }

    int leading_place = 1;
    for (int index = 0; index < lag; index++) leading_place *= base;
    for (int residue = 0; residue < context->modulus; residue++)
        if (residue / leading_place == residue % base)
            context->diagonal[context->diagonal_count++] = residue;

    if (base != 2) {
        context->generator =
            primitive_root_prime_power(context->modulus, context->phi);
        context->cyclic_order = context->phi;
        if (context->generator == 0) {
            set_error(error, error_capacity,
                      "unable to construct the odd-prime unit group");
            periodic_zeta_context_free(context);
            return 0;
        }
        int residue = 1;
        for (int exponent = 0; exponent < context->phi; exponent++) {
            context->logarithm[residue] = exponent;
            residue = (int)((long long)residue * context->generator %
                            context->modulus);
        }
    } else if (context->exponent == 2) {
        context->cyclic_order = 1;
        context->logarithm[1] = 0;
        context->logarithm[3] = 0;
        context->negative_component[3] = 1;
    } else {
        context->generator = 5;
        context->cyclic_order = 1 << (context->exponent - 2);
        int residue = 1;
        for (int exponent = 0; exponent < context->cyclic_order; exponent++) {
            int negative = context->modulus - residue;
            context->logarithm[residue] = exponent;
            context->negative_component[residue] = 0;
            context->logarithm[negative] = exponent;
            context->negative_component[negative] = 1;
            residue = (int)((long long)residue * 5 % context->modulus);
        }
    }
    return 1;
}

void periodic_zeta_context_free(PeriodicZetaContext *context)
{
    if (!context) return;
    free(context->units);
    free(context->diagonal);
    free(context->logarithm);
    free(context->negative_component);
    memset(context, 0, sizeof(*context));
}

int periodic_zeta_character_valid(const PeriodicZetaContext *context,
                                  int character_index)
{
    if (!context || character_index < 1) return 0;
    if (context->base != 2)
        return character_index < context->phi &&
               character_index % 2 == 1 &&
               character_index % context->base != 0;
    if (context->exponent == 2) return character_index == 1;
    return character_index < context->cyclic_order &&
           character_index % 2 == 1;
}

int periodic_zeta_character_count(const PeriodicZetaContext *context)
{
    int count = 0;
    int limit;
    if (!context) return 0;
    if (context->base != 2) limit = context->phi;
    else if (context->exponent == 2) limit = 2;
    else limit = context->cyclic_order;
    for (int index = 1; index < limit; index++)
        if (periodic_zeta_character_valid(context, index)) count++;
    return count;
}

long double complex periodic_zeta_character_value(
    const PeriodicZetaContext *context, int character_index, int residue)
{
    long double angle;
    long double complex value;

    if (!context || !periodic_zeta_character_valid(context, character_index))
        return 0.0L;
    residue %= context->modulus;
    if (residue < 0) residue += context->modulus;
    if (context->logarithm[residue] < 0) return 0.0L;
    if (context->base != 2) {
        angle = 2.0L * pi_value() * character_index *
                context->logarithm[residue] / context->phi;
        return cosl(angle) + I * sinl(angle);
    }
    if (context->exponent == 2)
        return context->negative_component[residue] ? -1.0L : 1.0L;
    angle = 2.0L * pi_value() * character_index *
            context->logarithm[residue] / context->cyclic_order;
    value = cosl(angle) + I * sinl(angle);
    return context->negative_component[residue] ? -value : value;
}

long double complex periodic_zeta_diagonal_boundary(
    const PeriodicZetaContext *context, int character_index)
{
    long double complex sum = 0.0L;
    if (!context || !periodic_zeta_character_valid(context, character_index))
        return 0.0L;
    for (int index = 0; index < context->diagonal_count; index++) {
        int residue = context->diagonal[index];
        sum += periodic_zeta_character_value(
                   context, character_index, (residue + 1) % context->modulus) -
               periodic_zeta_character_value(
                   context, character_index, residue);
    }
    return sum;
}

long double complex periodic_zeta_bernoulli_one(
    const PeriodicZetaContext *context, int character_index)
{
    long double complex sum = 0.0L;
    if (!context || !periodic_zeta_character_valid(context, character_index))
        return 0.0L;
    for (int residue = 1; residue < context->modulus; residue++)
        sum += residue * periodic_zeta_character_value(
                             context, character_index, residue);
    return sum / context->modulus;
}

long double complex periodic_zeta_gauss_sum(
    const PeriodicZetaContext *context, int character_index)
{
    long double complex sum = 0.0L;
    if (!context || !periodic_zeta_character_valid(context, character_index))
        return 0.0L;
    for (int residue = 0; residue < context->modulus; residue++) {
        long double angle =
            2.0L * pi_value() * residue / context->modulus;
        sum += periodic_zeta_character_value(
                   context, character_index, residue) *
               (cosl(angle) + I * sinl(angle));
    }
    return sum;
}

static long double complex complex_gamma(long double complex z)
{
    static const long double coefficients[] = {
        0.99999999999980993227684700473478L,
        676.520368121885098567009190444019L,
        -1259.13921672240287047156078755283L,
        771.3234287776530788486528258894L,
        -176.61502916214059906584551354L,
        12.507343278686904814458936853L,
        -0.13857109526572011689554707L,
        0.000009984369578019570859563L,
        0.000000150563273514931155834L
    };
    long double pi = pi_value();
    if (creall(z) < 0.5L)
        return pi / (csinl(pi * z) * complex_gamma(1.0L - z));
    z -= 1.0L;
    long double complex series = coefficients[0];
    for (int index = 1; index < 9; index++)
        series += coefficients[index] / (z + index);
    long double complex shifted = z + 7.5L;
    return csqrtl(2.0L * pi) * cpowl(shifted, z + 0.5L) *
           cexpl(-shifted) * series;
}

static long double complex hurwitz_zeta(long double complex s, long double a)
{
    static const long double bernoulli[] = {
        1.0L / 6.0L, -1.0L / 30.0L, 1.0L / 42.0L,
        -1.0L / 30.0L, 5.0L / 66.0L, -691.0L / 2730.0L,
        7.0L / 6.0L, -3617.0L / 510.0L,
        43867.0L / 798.0L, -174611.0L / 330.0L
    };
    enum { DIRECT_TERMS = 96, CORRECTION_TERMS = 10 };
    long double complex sum = 0.0L;
    long double tail = DIRECT_TERMS + a;
    long double complex rising = s;

    for (int index = 0; index < DIRECT_TERMS; index++)
        sum += cpowl(index + a, -s);
    sum += cpowl(tail, 1.0L - s) / (s - 1.0L);
    sum += 0.5L * cpowl(tail, -s);
    for (int order = 1; order <= CORRECTION_TERMS; order++) {
        long double factorial = 1.0L;
        for (int factor = 2; factor <= 2 * order; factor++)
            factorial *= factor;
        if (order > 1)
            rising *= (s + 2 * order - 3) * (s + 2 * order - 2);
        sum += bernoulli[order - 1] * rising / factorial *
               cpowl(tail, -s - 2 * order + 1);
    }
    return sum;
}

static long double complex periodic_zeta_kernel(long double x,
                                                long double complex s)
{
    long double pi = pi_value();
    long double complex phase = I * pi * s / 2.0L;
    return complex_gamma(s) / cpowl(2.0L * pi, s) *
           (cexpl(phase) * hurwitz_zeta(s, x) +
            cexpl(-phase) * hurwitz_zeta(s, 1.0L - x));
}

static long double complex dirichlet_l_hurwitz(
    const PeriodicZetaContext *context, int character_index,
    long double complex s, int conjugate_character)
{
    long double complex sum = 0.0L;
    for (int index = 0; index < context->unit_count; index++) {
        int residue = context->units[index];
        long double complex character = periodic_zeta_character_value(
            context, character_index, residue);
        if (conjugate_character) character = conjl(character);
        sum += character * hurwitz_zeta(
                               s, (long double)residue / context->modulus);
    }
    return sum * cpowl((long double)context->modulus, -s);
}

static long double comparison_error(long double complex left,
                                    long double complex right)
{
    long double scale = fmaxl(1.0L, fmaxl(cabsl(left), cabsl(right)));
    return cabsl(left - right) / scale;
}

static long double complex analytic_prefactor(
    const PeriodicZetaContext *context, long double complex s)
{
    long double pi = pi_value();
    return 2.0L * I * csinl(pi * s / 2.0L) * complex_gamma(s) *
           cpowl((long double)context->modulus / (2.0L * pi), s);
}

int periodic_zeta_model_comparison(
    const PeriodicZetaContext *context, int character_index, int residue,
    long double complex s, PeriodicZetaComparison *comparison)
{
    long double complex left = 0.0L;
    long double complex l_value;
    long double complex right;

    if (!context || !comparison ||
        !periodic_zeta_character_valid(context, character_index) ||
        residue < 1 || residue >= context->modulus ||
        creall(s) <= 0.0L || creall(s) >= 1.0L)
        return 0;
    for (int index = 0; index < context->unit_count; index++) {
        int unit = context->units[index];
        int reduced = (int)((long long)residue * unit % context->modulus);
        if (reduced == 0) reduced = context->modulus;
        left += conjl(periodic_zeta_character_value(
                    context, character_index, unit)) *
                periodic_zeta_kernel(
                    (long double)reduced / context->modulus, s);
    }
    l_value = dirichlet_l_hurwitz(context, character_index, s, 1);
    right = periodic_zeta_character_value(
                context, character_index, residue) *
            analytic_prefactor(context, s) * l_value;
    comparison->left = left;
    comparison->right = right;
    comparison->l_value = l_value;
    comparison->diagonal = periodic_zeta_diagonal_boundary(
        context, character_index);
    comparison->relative_error = comparison_error(left, right);
    return 1;
}

static int direct_transform(
    const PeriodicZetaContext *context, int character_index,
    long double complex s, int boundary_side, long double complex *result)
{
    long double complex *raw;
    long double complex transform = 0.0L;
    long double pi = pi_value();

    if (!context || !result ||
        !periodic_zeta_character_valid(context, character_index))
        return 0;
    raw = calloc((size_t)context->modulus, sizeof(*raw));
    if (!raw) return 0;

    for (int index = 0; index < context->unit_count; index++) {
        int unit = context->units[index];
        int first = unit;
        int second = context->modulus - unit;
        long double x_first = (long double)first / context->modulus;
        long double x_second = (long double)second / context->modulus;
        long double complex value;

        if (boundary_side == 0) {
            value = -clogl(1.0L - cexpl(2.0L * pi * I * x_first)) +
                    clogl(1.0L - cexpl(2.0L * pi * I * x_second));
        } else if (boundary_side == 1) {
            value = I * 0.5L *
                    (1.0L / tanl(pi * x_first) -
                     1.0L / tanl(pi * x_second));
        } else {
            value = periodic_zeta_kernel(x_first, s) -
                    periodic_zeta_kernel(x_second, s);
        }

        for (int diagonal_index = 0;
             diagonal_index < context->diagonal_count; diagonal_index++) {
            int diagonal = context->diagonal[diagonal_index];
            if (diagonal == 0 || diagonal == context->modulus - 1) continue;
            int next = (int)((long long)(diagonal + 1) * unit %
                             context->modulus);
            int current = (int)((long long)diagonal * unit %
                                context->modulus);
            long double x_next = (long double)next / context->modulus;
            long double x_current = (long double)current / context->modulus;
            if (boundary_side == 0) {
                value += -clogl(1.0L - cexpl(2.0L * pi * I * x_next)) +
                         clogl(1.0L - cexpl(2.0L * pi * I * x_current));
            } else if (boundary_side == 1) {
                value += I * 0.5L *
                         (1.0L / tanl(pi * x_next) -
                          1.0L / tanl(pi * x_current));
            } else {
                value += periodic_zeta_kernel(x_next, s) -
                         periodic_zeta_kernel(x_current, s);
            }
        }
        raw[unit] = value;
    }

    for (int residue_class = 1; residue_class < context->base;
         residue_class++) {
        long double complex sum = 0.0L;
        int count = 0;
        for (int index = 0; index < context->unit_count; index++) {
            int unit = context->units[index];
            if (unit % context->base == residue_class) {
                sum += raw[unit];
                count++;
            }
        }
        if (count == 0) continue;
        long double complex mean = sum / count;
        for (int index = 0; index < context->unit_count; index++) {
            int unit = context->units[index];
            if (unit % context->base == residue_class) raw[unit] -= mean;
        }
    }
    for (int index = 0; index < context->unit_count; index++) {
        int unit = context->units[index];
        transform += raw[unit] * conjl(periodic_zeta_character_value(
                                      context, character_index, unit));
    }
    free(raw);
    *result = transform / context->phi;
    return 1;
}

int periodic_zeta_transform_comparison(
    const PeriodicZetaContext *context, int character_index,
    long double complex s, PeriodicZetaComparison *comparison)
{
    long double complex left;
    long double complex l_value;
    long double complex diagonal;
    long double complex right;
    if (!context || !comparison || creall(s) <= 0.0L || creall(s) >= 1.0L ||
        !direct_transform(context, character_index, s, -1, &left))
        return 0;
    l_value = dirichlet_l_hurwitz(context, character_index, s, 1);
    diagonal = periodic_zeta_diagonal_boundary(context, character_index);
    right = analytic_prefactor(context, s) * diagonal * l_value /
            context->phi;
    comparison->left = left;
    comparison->right = right;
    comparison->l_value = l_value;
    comparison->diagonal = diagonal;
    comparison->relative_error = comparison_error(left, right);
    return 1;
}

int periodic_zeta_boundary_transform(
    const PeriodicZetaContext *context, int character_index, int side,
    long double complex *value)
{
    if (side != 0 && side != 1) return 0;
    return direct_transform(context, character_index, 0.0L, side, value);
}

int periodic_zeta_finite_collision_coefficient(
    const PeriodicZetaContext *context, int character_index,
    long double complex *direct, long double complex *factorized)
{
    long double *values;
    long double complex transform = 0.0L;
    long double complex diagonal;
    long double complex bernoulli_bar;

    if (!context || !direct || !factorized || context->lag != 1 ||
        context->base == 2 ||
        !periodic_zeta_character_valid(context, character_index))
        return 0;
    values = calloc((size_t)context->modulus, sizeof(*values));
    if (!values) return 0;
    for (int index = 0; index < context->unit_count; index++) {
        int unit = context->units[index];
        long long collision_sum = -1 - unit / context->base;
        for (int diagonal_index = 0;
             diagonal_index < context->diagonal_count; diagonal_index++) {
            int diagonal_residue = context->diagonal[diagonal_index];
            collision_sum +=
                (long long)(diagonal_residue + 1) * unit / context->modulus -
                (long long)diagonal_residue * unit / context->modulus;
        }
        values[unit] = collision_sum;
    }
    for (int residue_class = 1; residue_class < context->base;
         residue_class++) {
        long double sum = 0.0L;
        int count = 0;
        for (int index = 0; index < context->unit_count; index++) {
            int unit = context->units[index];
            if (unit % context->base == residue_class) {
                sum += values[unit];
                count++;
            }
        }
        long double mean = count == 0 ? 0.0L : sum / count;
        for (int index = 0; index < context->unit_count; index++) {
            int unit = context->units[index];
            if (unit % context->base == residue_class) values[unit] -= mean;
        }
    }
    for (int index = 0; index < context->unit_count; index++) {
        int unit = context->units[index];
        transform += values[unit] * conjl(periodic_zeta_character_value(
                                         context, character_index, unit));
    }
    free(values);
    diagonal = periodic_zeta_diagonal_boundary(context, character_index);
    bernoulli_bar = conjl(periodic_zeta_bernoulli_one(
        context, character_index));
    *direct = transform / context->phi;
    *factorized = -bernoulli_bar * diagonal / context->phi;
    return 1;
}

int periodic_zeta_boundary_values(
    const PeriodicZetaContext *context, int character_index,
    long double complex *left_direct, long double complex *left_factorized,
    long double complex *right_direct, long double complex *right_factorized,
    long double complex *right_l_value)
{
    long double pi = pi_value();
    long double complex diagonal;
    long double complex bernoulli;
    long double complex bernoulli_bar;
    long double complex gauss_bar;
    long double complex l_one_bar = 0.0L;

    if (!context || !left_direct || !left_factorized || !right_direct ||
        !right_factorized || !right_l_value ||
        !periodic_zeta_character_valid(context, character_index) ||
        !periodic_zeta_boundary_transform(
            context, character_index, 0, left_direct) ||
        !periodic_zeta_boundary_transform(
            context, character_index, 1, right_direct))
        return 0;
    diagonal = periodic_zeta_diagonal_boundary(context, character_index);
    bernoulli = periodic_zeta_bernoulli_one(context, character_index);
    bernoulli_bar = conjl(bernoulli);
    gauss_bar = -conjl(periodic_zeta_gauss_sum(
        context, character_index));
    for (int index = 0; index < context->unit_count; index++) {
        int residue = context->units[index];
        l_one_bar += conjl(periodic_zeta_character_value(
                         context, character_index, residue)) /
                     tanl(pi * residue / context->modulus);
    }
    l_one_bar *= pi / (2.0L * context->modulus);
    *left_factorized = -I * pi * bernoulli_bar * diagonal / context->phi;
    *right_factorized = -gauss_bar * bernoulli * diagonal / context->phi;
    *right_l_value = I * (long double)context->modulus * diagonal * l_one_bar /
                     (pi * (long double)context->phi);
    return 1;
}
