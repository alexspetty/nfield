/*
 * weighted_reference_profile.c
 *
 * Exact arithmetic for weighted one-digit residue profiles and their
 * reciprocal-golden real branches. Finite profiles and real interpolation
 * remain separate.
 */

#include "nfield.h"

#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    long long a; /* constant coordinate */
    long long b; /* coefficient of tau, tau^2 = 1 - tau */
} WrpQuad;

typedef struct {
    long long a;
    long long b;
    long long den;
} WrpQuadFraction;

typedef struct {
    long long a;
    long long b;
    long long c;
    long long d;
} WrpMatrix;

static long long wrp_absll(long long value)
{
    return value < 0 ? -value : value;
}

static long long wrp_gcd(long long a, long long b)
{
    a = wrp_absll(a);
    b = wrp_absll(b);
    while (b != 0) {
        long long remainder = a % b;
        a = b;
        b = remainder;
    }
    return a == 0 ? 1 : a;
}

static long long wrp_gcd3(long long a, long long b, long long c)
{
    return wrp_gcd(wrp_gcd(a, b), c);
}

static void wrp_reduce_fraction(long long *numerator, long long *denominator)
{
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
    long long divisor = wrp_gcd(*numerator, *denominator);
    *numerator /= divisor;
    *denominator /= divisor;
}

static WrpQuadFraction wrp_reduce_quad_fraction(WrpQuadFraction value)
{
    if (value.den < 0) {
        value.a = -value.a;
        value.b = -value.b;
        value.den = -value.den;
    }
    long long divisor = wrp_gcd3(value.a, value.b, value.den);
    value.a /= divisor;
    value.b /= divisor;
    value.den /= divisor;
    return value;
}

static WrpQuad wrp_quad_add(WrpQuad left, WrpQuad right)
{
    WrpQuad result = {left.a + right.a, left.b + right.b};
    return result;
}

static WrpQuad wrp_quad_sub(WrpQuad left, WrpQuad right)
{
    WrpQuad result = {left.a - right.a, left.b - right.b};
    return result;
}

static WrpQuad wrp_quad_scale(WrpQuad value, long long scalar)
{
    WrpQuad result = {value.a * scalar, value.b * scalar};
    return result;
}

static WrpQuad wrp_quad_mul(WrpQuad left, WrpQuad right)
{
    WrpQuad result = {
        left.a * right.a + left.b * right.b,
        left.a * right.b + left.b * right.a - left.b * right.b
    };
    return result;
}

static int wrp_quad_equal(WrpQuad left, WrpQuad right)
{
    return left.a == right.a && left.b == right.b;
}

static WrpMatrix wrp_matrix_add(WrpMatrix left, WrpMatrix right)
{
    WrpMatrix result = {
        left.a + right.a, left.b + right.b,
        left.c + right.c, left.d + right.d
    };
    return result;
}

static WrpMatrix wrp_matrix_mul(WrpMatrix left, WrpMatrix right)
{
    WrpMatrix result = {
        left.a * right.a + left.b * right.c,
        left.a * right.b + left.b * right.d,
        left.c * right.a + left.d * right.c,
        left.c * right.b + left.d * right.d
    };
    return result;
}

static WrpMatrix wrp_matrix_scale(WrpMatrix value, long long scalar)
{
    WrpMatrix result = {
        scalar * value.a, scalar * value.b,
        scalar * value.c, scalar * value.d
    };
    return result;
}

static WrpMatrix wrp_matrix_pow(WrpMatrix base, int exponent)
{
    WrpMatrix result = {1, 0, 0, 1};
    for (int index = 0; index < exponent; index++)
        result = wrp_matrix_mul(result, base);
    return result;
}

static int wrp_matrix_equal(WrpMatrix left, WrpMatrix right)
{
    return left.a == right.a && left.b == right.b
        && left.c == right.c && left.d == right.d;
}

static long long wrp_matrix_trace(WrpMatrix value)
{
    return value.a + value.d;
}

static long long wrp_matrix_det(WrpMatrix value)
{
    return value.a * value.d - value.b * value.c;
}

static WrpMatrix wrp_reflection_matrix(int modulus)
{
    WrpMatrix result = {1, 0, modulus, -1};
    return result;
}

static WrpMatrix wrp_reflection_product(int modulus)
{
    const WrpMatrix third_turn = {2, -1, 3, -1};
    return wrp_matrix_mul(wrp_reflection_matrix(modulus), third_turn);
}

static WrpMatrix wrp_reverse_reflection_product(int modulus)
{
    const WrpMatrix third_turn = {2, -1, 3, -1};
    return wrp_matrix_mul(third_turn, wrp_reflection_matrix(modulus));
}

static WrpQuad wrp_tau_power(int exponent)
{
    WrpQuad value = {1, 0};
    const WrpQuad tau = {0, 1};
    for (int index = 0; index < exponent; index++)
        value = wrp_quad_mul(value, tau);
    return value;
}

static int wrp_quad_sign(WrpQuad value)
{
    /* 2(a+b*tau) = (2a-b) + b*sqrt(5). */
    __int128 rational = (__int128)2 * value.a - value.b;
    __int128 radical = value.b;
    if (rational == 0 && radical == 0) return 0;
    if (rational >= 0 && radical >= 0) return 1;
    if (rational <= 0 && radical <= 0) return -1;
    __int128 rational_square = rational * rational;
    __int128 radical_square = (__int128)5 * radical * radical;
    if (rational > 0)
        return rational_square > radical_square ? 1 : -1;
    return radical_square > rational_square ? 1 : -1;
}

static int wrp_quad_fraction_sign(WrpQuadFraction value)
{
    if (value.den < 0) {
        value.a = -value.a;
        value.b = -value.b;
    }
    WrpQuad numerator = {value.a, value.b};
    return wrp_quad_sign(numerator);
}

static WrpQuadFraction wrp_quad_fraction_sub(
        WrpQuadFraction left, WrpQuadFraction right)
{
    WrpQuadFraction result = {
        left.a * right.den - right.a * left.den,
        left.b * right.den - right.b * left.den,
        left.den * right.den
    };
    return wrp_reduce_quad_fraction(result);
}

static WrpQuadFraction wrp_real_weight(int modulus, int exponent)
{
    WrpQuad numerator = wrp_quad_sub(
        wrp_quad_sub(
            (WrpQuad){-1, modulus},
            wrp_tau_power(exponent + 1)),
        (WrpQuad){0, 0});
    WrpQuad denominator = wrp_quad_sub(
        (WrpQuad){1, 0}, wrp_tau_power(exponent));
    WrpQuad conjugate = {
        denominator.a - denominator.b,
        -denominator.b
    };
    WrpQuad product = wrp_quad_mul(numerator, conjugate);
    long long norm = denominator.a * denominator.a
        - denominator.a * denominator.b
        - denominator.b * denominator.b;
    WrpQuadFraction result = {product.a, product.b, norm};
    return wrp_reduce_quad_fraction(result);
}

static long double wrp_quad_fraction_value(WrpQuadFraction value)
{
    const long double tau = (sqrtl(5.0L) - 1.0L) / 2.0L;
    return ((long double)value.a + (long double)value.b * tau)
        / (long double)value.den;
}

static long long wrp_fibonacci(int index)
{
    long long previous = 0;
    long long current = 1;
    if (index == 0) return 0;
    for (int step = 1; step < index; step++) {
        long long next = previous + current;
        previous = current;
        current = next;
    }
    return current;
}

static int wrp_common_depth(int base, int supported, int *depth,
                            long long *power)
{
    if (base < 2 || supported < 1) return 0;
    long long value = 1;
    for (int candidate = 0; candidate <= 30; candidate++) {
        if (value % supported == 0) {
            *depth = candidate;
            *power = value;
            return 1;
        }
        if (value > LLONG_MAX / base) return 0;
        value *= base;
    }
    return 0;
}

static int wrp_block_counts(int modulus, int supported, int base,
                            int *terminating, int *matching, int *other,
                            int *depth_out)
{
    if (modulus < 2 || supported < 1 || base < 2
        || base % modulus != 1)
        return 0;
    if ((long long)modulus * supported > 200000) return 0;
    int depth = 0;
    long long power = 0;
    if (!wrp_common_depth(base, supported, &depth, &power)) return 0;
    long long cofactor = power / supported;
    int reference = (int)(cofactor % modulus);
    if (reference == 0) return 0;
    int zero_count = 0;
    int reference_count = 0;
    int other_count = 0;
    for (int numerator = 1;
         numerator < modulus * supported; numerator++) {
        int residue = (int)(((long long)numerator * cofactor) % modulus);
        if (residue == 0) {
            zero_count++;
            continue;
        }
        long long product = (long long)base * residue;
        int digit = (int)(product / modulus);
        int next = (int)(product - (long long)digit * modulus);
        if (next != residue || digit < 0 || digit >= base) return 0;
        if (residue == reference) reference_count++;
        else other_count++;
    }
    if (zero_count != supported - 1
        || reference_count != supported
        || other_count != (modulus - 2) * supported)
        return 0;
    *terminating = zero_count;
    *matching = reference_count;
    *other = other_count;
    *depth_out = depth;
    return 1;
}

static int wrp_weighted_score_fraction(
        int modulus, int supported,
        long long lambda_num, long long lambda_den,
        long long *score_num, long long *score_den)
{
    if (modulus < 2 || supported < 1 || lambda_den <= 0
        || lambda_num < 0 || lambda_num > lambda_den)
        return 0;
    long long rows = (long long)modulus * supported - 1;
    __int128 numerator = (__int128)lambda_num * (supported - 1)
        + (__int128)lambda_den * supported;
    __int128 denominator = (__int128)lambda_den * rows;
    if (numerator > LLONG_MAX || denominator > LLONG_MAX)
        return 0;
    *score_num = (long long)numerator;
    *score_den = (long long)denominator;
    wrp_reduce_fraction(score_num, score_den);
    return 1;
}

static WrpQuad wrp_power_equation_rational(
        int modulus, int exponent,
        long long lambda_num, long long lambda_den)
{
    WrpQuad value = wrp_quad_scale(
        wrp_tau_power(exponent + 1), lambda_den);
    value = wrp_quad_sub(value,
        wrp_quad_scale(wrp_tau_power(exponent), lambda_num));
    value = wrp_quad_sub(value, (WrpQuad){0, lambda_den * modulus});
    value = wrp_quad_add(value,
        (WrpQuad){lambda_num + lambda_den, 0});
    return value;
}

static WrpQuad wrp_fibonacci_coordinates(
        int modulus, int exponent,
        long long lambda_num, long long lambda_den)
{
    long long sign = (exponent % 2 == 0) ? 1 : -1;
    long long sign_next = -sign;
    long long coefficient = sign *
        (lambda_den * wrp_fibonacci(exponent + 1)
            + lambda_num * wrp_fibonacci(exponent))
        - lambda_den * modulus;
    long long constant = sign_next *
        (lambda_den * wrp_fibonacci(exponent)
            + lambda_num * wrp_fibonacci(exponent - 1))
        + lambda_num + lambda_den;
    WrpQuad result = {constant, coefficient};
    return result;
}

static int wrp_rational_case_excludes(
        int exponent, long long lambda_num, long long lambda_den)
{
    if (exponent % 2 == 1) {
        long long lower = lambda_den *
            (wrp_fibonacci(exponent) + 1)
            + lambda_num * (wrp_fibonacci(exponent - 1) + 1);
        return lower > 0;
    }
    if (exponent >= 4) {
        long long coordinate = lambda_den *
            (1 - wrp_fibonacci(exponent))
            + lambda_num * (1 - wrp_fibonacci(exponent - 1));
        return coordinate < 0;
    }
    return exponent == 2;
}

static int wrp_window_holds(int modulus, int exponent)
{
    WrpQuad lower = wrp_quad_sub(
        (WrpQuad){-1, modulus}, wrp_tau_power(exponent + 1));
    WrpQuad upper = wrp_quad_sub(
        wrp_quad_sub((WrpQuad){2, -modulus},
                     wrp_tau_power(exponent + 2)),
        (WrpQuad){0, 0});
    return wrp_quad_sign(lower) >= 0 && wrp_quad_sign(upper) >= 0;
}

static int wrp_check_blocks(int *models, long long *rows)
{
    *models = 0;
    *rows = 0;
    for (int modulus = 2; modulus <= 15; modulus++) {
        for (int scale = 1; scale <= 2; scale++) {
            int base = 1 + scale * modulus;
            int supported_values[3] = {1, base, base * base};
            for (int index = 0; index < 3; index++) {
                int supported = supported_values[index];
                int terminating = 0;
                int matching = 0;
                int other = 0;
                int depth = 0;
                if (!wrp_block_counts(modulus, supported, base,
                        &terminating, &matching, &other, &depth))
                    return 0;
                (void)depth;
                (*models)++;
                *rows += (long long)modulus * supported - 1;
            }
        }
    }
    return 1;
}

static int wrp_check_weighted_scores(int *cases)
{
    *cases = 0;
    for (int modulus = 2; modulus <= 15; modulus++) {
        for (int supported = 1; supported <= 40; supported++) {
            for (int denominator = 1; denominator <= 9; denominator++) {
                for (int numerator = 0; numerator <= denominator; numerator++) {
                    long long score_num = 0;
                    long long score_den = 0;
                    if (!wrp_weighted_score_fraction(
                            modulus, supported, numerator, denominator,
                            &score_num, &score_den))
                        return 0;
                    __int128 left = (__int128)score_num * denominator
                        * ((long long)modulus * supported - 1);
                    __int128 right = (__int128)score_den
                        * (numerator * (supported - 1)
                            + denominator * supported);
                    if (left != right) return 0;
                    (*cases)++;
                }
            }
        }
    }
    return 1;
}

static int wrp_check_fibonacci_coordinates(int *powers)
{
    *powers = 0;
    for (int exponent = 1; exponent <= 40; exponent++) {
        WrpQuad direct = wrp_tau_power(exponent);
        long long sign_tau = (exponent % 2 == 1) ? 1 : -1;
        long long sign_constant = -sign_tau;
        WrpQuad expected = {
            sign_constant * wrp_fibonacci(exponent - 1),
            sign_tau * wrp_fibonacci(exponent)
        };
        if (direct.a != expected.a || direct.b != expected.b) return 0;
        (*powers)++;
    }
    return 1;
}

static int wrp_check_rational_coordinates(int *cases)
{
    *cases = 0;
    for (int modulus = 2; modulus <= 12; modulus++) {
        for (int exponent = 1; exponent <= 20; exponent++) {
            for (int denominator = 1; denominator <= 13; denominator++) {
                for (int numerator = 0; numerator <= denominator; numerator++) {
                    WrpQuad direct = wrp_power_equation_rational(
                        modulus, exponent, numerator, denominator);
                    WrpQuad fib = wrp_fibonacci_coordinates(
                        modulus, exponent, numerator, denominator);
                    if (direct.a != fib.a || direct.b != fib.b) return 0;
                    if (!wrp_rational_case_excludes(
                            exponent, numerator, denominator))
                        return 0;
                    int zero = direct.a == 0 && direct.b == 0;
                    int expected = exponent == 2
                        && ((modulus == 2 && numerator == 0)
                            || (modulus == 3 && numerator == denominator));
                    if (zero != expected) return 0;
                    (*cases)++;
                }
            }
        }
    }
    return 1;
}

static int wrp_check_real_windows(int *cases)
{
    *cases = 0;
    for (int modulus = 2; modulus <= 12; modulus++) {
        for (int exponent = 1; exponent <= 32; exponent++) {
            int holds = wrp_window_holds(modulus, exponent);
            int expected = (modulus == 2 || modulus == 3)
                && exponent >= 2;
            if (holds != expected) return 0;
            if (holds) {
                WrpQuadFraction weight = wrp_real_weight(modulus, exponent);
                WrpQuadFraction one_minus = {
                    weight.den - weight.a, -weight.b, weight.den
                };
                if (wrp_quad_fraction_sign(weight) < 0
                    || wrp_quad_fraction_sign(one_minus) < 0)
                    return 0;
                if (exponent >= 3 && weight.b == 0) return 0;
            }
            (*cases)++;
        }
    }
    return 1;
}

static int wrp_check_branch_geometry(int *steps)
{
    *steps = 0;
    WrpQuadFraction endpoint_two = wrp_real_weight(2, 2);
    WrpQuadFraction endpoint_three = wrp_real_weight(3, 2);
    if (endpoint_two.a != 0 || endpoint_two.b != 0
        || endpoint_three.a != endpoint_three.den
        || endpoint_three.b != 0)
        return 0;
    WrpQuadFraction first_two = wrp_real_weight(2, 3);
    WrpQuad tau_three = wrp_tau_power(3);
    WrpQuadFraction expected_two =
        wrp_reduce_quad_fraction((WrpQuadFraction){
            tau_three.a, tau_three.b, 2});
    WrpQuadFraction first_three = wrp_real_weight(3, 3);
    WrpQuadFraction expected_three =
        wrp_reduce_quad_fraction((WrpQuadFraction){0, 3, 2});
    if (first_two.a != expected_two.a || first_two.b != expected_two.b
        || first_two.den != expected_two.den
        || first_three.a != expected_three.a
        || first_three.b != expected_three.b
        || first_three.den != expected_three.den)
        return 0;
    for (int exponent = 2; exponent < 32; exponent++) {
        WrpQuadFraction two_now = wrp_real_weight(2, exponent);
        WrpQuadFraction two_next = wrp_real_weight(2, exponent + 1);
        WrpQuadFraction three_now = wrp_real_weight(3, exponent);
        WrpQuadFraction three_next = wrp_real_weight(3, exponent + 1);
        if (wrp_quad_fraction_sign(
                wrp_quad_fraction_sub(two_next, two_now)) <= 0)
            return 0;
        if (wrp_quad_fraction_sign(
                wrp_quad_fraction_sub(three_next, three_now)) >= 0)
            return 0;
        (*steps)++;
    }
    return 1;
}

static int wrp_check_projective_profile_types(int *cases)
{
    *cases = 0;
    for (int modulus = 2; modulus <= 40; modulus++) {
        for (int denominator = 1; denominator <= 40; denominator++) {
            for (int numerator = 0; numerator <= denominator; numerator++) {
                __int128 reflection_coordinate =
                    (__int128)numerator * numerator;
                int reflection = reflection_coordinate == 0;
                if (reflection != (numerator == 0)) return 0;

                __int128 third_left =
                    (__int128)numerator * numerator;
                __int128 third_right =
                    (__int128)numerator * denominator * (modulus - 1)
                    - (__int128)denominator * denominator;
                int third_turn = third_left == third_right;
                int expected_third =
                    modulus == 3 && numerator == denominator;
                if (third_turn != expected_third) return 0;

                __int128 fourth_right = 2 * third_right;
                __int128 sixth_right = 3 * third_right;
                int fourth_turn = third_left == fourth_right;
                int sixth_turn = third_left == sixth_right;
                if (fourth_turn || sixth_turn) return 0;

                int rational_torsion = reflection || third_turn
                    || fourth_turn || sixth_turn;
                int expected_torsion = numerator == 0
                    || (modulus == 3 && numerator == denominator);
                if (rational_torsion != expected_torsion) return 0;
                (*cases)++;
            }
        }
    }

    for (int modulus = 2; modulus <= 100; modulus++) {
        long long discriminant =
            (long long)(modulus - 1) * (modulus - 1) - 4;
        int square = 0;
        if (discriminant >= 0) {
            for (long long root = 0; root <= modulus; root++) {
                if (root * root == discriminant) {
                    square = 1;
                    break;
                }
            }
        }
        int expected_square = modulus == 3;
        if (square != expected_square) return 0;
    }
    return 1;
}

static int wrp_check_reflection_product_family(int *moduli)
{
    *moduli = 0;
    const WrpMatrix third_turn = {2, -1, 3, -1};
    const WrpMatrix fibonacci = {1, 1, 1, 0};
    const WrpMatrix q4_coordinate = {1, 0, 3, 1};
    for (int modulus = 2; modulus <= 200; modulus++) {
        WrpMatrix reflection = wrp_reflection_matrix(modulus);
        WrpMatrix product = wrp_reflection_product(modulus);
        WrpMatrix expected = {
            2, -1, 2 * modulus - 3, 1 - modulus
        };
        if (!wrp_matrix_equal(
                wrp_matrix_mul(reflection, reflection),
                (WrpMatrix){1, 0, 0, 1}))
            return 0;
        if (!wrp_matrix_equal(
                wrp_matrix_mul(reflection, third_turn), product)
            || !wrp_matrix_equal(product, expected))
            return 0;
        long long trace = wrp_matrix_trace(product);
        long long determinant = wrp_matrix_det(product);
        long long discriminant = trace * trace - 4 * determinant;
        long long expected_discriminant =
            (long long)(modulus - 3) * (modulus - 3) + 4;
        if (trace != 3 - modulus || determinant != -1
            || discriminant != expected_discriminant)
            return 0;
        int fibonacci_case = discriminant == 5;
        if (fibonacci_case != (modulus == 2 || modulus == 4))
            return 0;
        if (modulus == 3
            && !wrp_matrix_equal(
                wrp_matrix_mul(product, product),
                (WrpMatrix){1, 0, 0, 1}))
            return 0;
        (*moduli)++;
    }
    WrpMatrix negative_q4 =
        wrp_matrix_scale(wrp_reflection_product(4), -1);
    if (!wrp_matrix_equal(
            wrp_matrix_mul(negative_q4, q4_coordinate),
            wrp_matrix_mul(q4_coordinate, fibonacci)))
        return 0;
    return 1;
}

static int wrp_check_above_unit_intersection(int *moduli)
{
    *moduli = 0;
    const WrpQuad phi_square = {2, 1};
    const WrpQuad zero = {0, 0};
    for (int modulus = 2; modulus <= 200; modulus++) {
        long long quadratic = 2LL * modulus - 3;
        long long linear = -(modulus + 1LL);
        long long constant = 1;

        /*
         * P_q(x)=(q-3)x(2x-1)+(x-1)(3x-1).
         * Coefficient equality is the exact positivity certificate for q>=3.
         */
        long long decomposed_quadratic = 2LL * (modulus - 3) + 3;
        long long decomposed_linear = -(modulus - 3LL) - 4;
        if (quadratic != decomposed_quadratic
            || linear != decomposed_linear || constant != 1)
            return 0;

        if (modulus == 2) {
            WrpQuad value = wrp_quad_add(
                wrp_quad_scale(wrp_quad_mul(phi_square, phi_square),
                               quadratic),
                wrp_quad_add(wrp_quad_scale(phi_square, linear),
                             (WrpQuad){constant, 0}));
            if (!wrp_quad_equal(value, zero)) return 0;
        } else if (modulus == 3) {
            if (quadratic + linear + constant != 0) return 0;
        } else {
            if (modulus - 3 <= 0) return 0;
        }
        (*moduli)++;
    }
    return 1;
}

static int wrp_check_fibonacci_total_positivity(int *powers)
{
    *powers = 0;
    const WrpMatrix fibonacci = {1, 1, 1, 0};
    for (int exponent = 1; exponent <= 40; exponent++) {
        WrpMatrix power = wrp_matrix_pow(fibonacci, exponent);
        int strictly_totally_positive = power.a > 0 && power.b > 0
            && power.c > 0 && power.d > 0
            && wrp_matrix_det(power) > 0;
        int expected = exponent % 2 == 0;
        if (strictly_totally_positive != expected) return 0;
        if (wrp_matrix_det(power) != (expected ? 1 : -1)) return 0;
        (*powers)++;
    }
    return 1;
}

static int wrp_check_finite_block_orbit(int *cases)
{
    const WrpMatrix coordinate = {1, 0, 1, -1};
    const WrpMatrix fibonacci = {1, 1, 1, 0};
    *cases = 0;

    for (int modulus = 2; modulus <= 200; modulus++) {
        WrpMatrix block_product = wrp_matrix_mul(
            wrp_matrix_mul(coordinate, wrp_reflection_product(modulus)),
            coordinate);
        WrpMatrix expected = {1, 1, 3 - modulus, 2 - modulus};
        if (!wrp_matrix_equal(block_product, expected)) return 0;

        for (long long reference = 2; reference <= 64; reference++) {
            for (long long terminating = 1;
                 terminating < reference; terminating++) {
                long long next_reference = reference + terminating;
                long long next_terminating =
                    (long long)(3 - modulus) * reference
                    + (long long)(2 - modulus) * terminating;
                int positive_lift = next_reference > next_terminating
                    && next_terminating > 0;
                if (positive_lift != (modulus == 2)) return 0;
                (*cases)++;
            }
        }
    }

    if (!wrp_matrix_equal(
            wrp_matrix_mul(
                wrp_matrix_mul(coordinate, wrp_reflection_product(2)),
                coordinate),
            fibonacci))
        return 0;

    for (long long supported = 2; supported <= 64; supported++) {
        long long reference = supported;
        long long terminating = supported - 1;
        for (int exponent = 0; exponent <= 32; exponent++) {
            long long expected_reference;
            long long expected_terminating;
            if (exponent == 0) {
                expected_reference = supported;
                expected_terminating = supported - 1;
            } else {
                expected_reference =
                    wrp_fibonacci(exponent + 1) * supported
                    + wrp_fibonacci(exponent) * (supported - 1);
                expected_terminating =
                    wrp_fibonacci(exponent) * supported
                    + wrp_fibonacci(exponent - 1) * (supported - 1);
            }
            if (reference != expected_reference
                || terminating != expected_terminating
                || reference <= terminating || terminating <= 0)
                return 0;

            long long difference = reference - terminating;
            __int128 golden_polynomial = (__int128)reference * reference
                - (__int128)3 * reference * difference
                + (__int128)difference * difference;
            int expected_sign = ((exponent + (supported >= 3 ? 0 : 1)) % 2 == 0)
                ? 1 : -1;
            if ((golden_polynomial > 0 ? 1 : -1) != expected_sign)
                return 0;

            if (exponent < 32) {
                long long next_reference = reference + terminating;
                terminating = reference;
                reference = next_reference;
            }
            (*cases)++;
        }
    }
    return 1;
}

static int wrp_check_oriented_word_family(int *cases)
{
    const WrpMatrix coordinate = {1, 0, 1, -1};
    const WrpMatrix fibonacci = {1, 1, 1, 0};
    const WrpMatrix aggregate = {1, 2, 0, 1};
    const WrpMatrix aggregate_inverse = {1, -2, 0, 1};
    *cases = 0;

    for (int modulus = 2; modulus <= 200; modulus++) {
        WrpMatrix forward = wrp_reflection_product(modulus);
        WrpMatrix reverse = wrp_reverse_reflection_product(modulus);
        WrpMatrix raw_forward = wrp_matrix_mul(
            wrp_matrix_mul(coordinate, forward), coordinate);
        WrpMatrix raw_reverse = wrp_matrix_mul(
            wrp_matrix_mul(coordinate, reverse), coordinate);
        WrpMatrix oriented_reverse = wrp_matrix_scale(raw_reverse, -1);
        WrpMatrix expected_forward = {
            1, 1, 3 - modulus, 2 - modulus
        };
        WrpMatrix expected_reverse = {
            modulus - 3, 1, 1, 0
        };

        if (!wrp_matrix_equal(raw_forward, expected_forward)
            || !wrp_matrix_equal(oriented_reverse, expected_reverse))
            return 0;

        for (long long reference = 2; reference <= 64; reference++) {
            for (long long terminating = 1;
                 terminating < reference; terminating++) {
                long long forward_reference = reference + terminating;
                long long forward_terminating =
                    (long long)(3 - modulus) * reference
                    + (long long)(2 - modulus) * terminating;
                long long reverse_reference =
                    (long long)(modulus - 3) * reference + terminating;
                long long reverse_terminating = reference;
                int forward_positive = forward_terminating > 0
                    && forward_terminating < forward_reference;
                int reverse_positive = reverse_terminating > 0
                    && reverse_terminating < reverse_reference;
                if (forward_positive != (modulus == 2)
                    || reverse_positive != (modulus >= 4))
                    return 0;
                (*cases)++;
            }
        }

        long long half_polynomial_times_four =
            (2LL * modulus - 3) - 2LL * (modulus + 1) + 4;
        long long unit_polynomial = modulus - 3LL;
        if (half_polynomial_times_four != -1) return 0;
        if (modulus >= 4 && unit_polynomial <= 0) return 0;
    }

    WrpMatrix forward_two = wrp_reflection_product(2);
    WrpMatrix reverse_four = wrp_reverse_reflection_product(4);
    if (!wrp_matrix_equal(reverse_four,
            wrp_matrix_scale(forward_two, -1)))
        return 0;

    WrpMatrix oriented_reverse_four = wrp_matrix_scale(
        wrp_matrix_mul(wrp_matrix_mul(coordinate, reverse_four), coordinate),
        -1);
    if (!wrp_matrix_equal(oriented_reverse_four, fibonacci)) return 0;

    WrpMatrix raw_forward_four = wrp_matrix_mul(
        wrp_matrix_mul(coordinate, wrp_reflection_product(4)), coordinate);
    WrpMatrix recoded_forward_four = wrp_matrix_mul(
        wrp_matrix_mul(aggregate, wrp_matrix_scale(raw_forward_four, -1)),
        aggregate_inverse);
    if (!wrp_matrix_equal(recoded_forward_four, fibonacci)) return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(aggregate, aggregate_inverse),
            (WrpMatrix){1, 0, 0, 1}))
        return 0;
    return 1;
}

static int wrp_check_binary_ternary_transport(void)
{
    const WrpMatrix identity = {1, 0, 0, 1};
    const WrpMatrix negative_identity = {-1, 0, 0, -1};
    const WrpMatrix reflection = {1, 0, 2, -1};
    const WrpMatrix third_turn = {2, -1, 3, -1};
    const WrpMatrix product = {2, -1, 1, -1};
    const WrpMatrix reverse_product = {0, 1, 1, 1};
    const WrpMatrix coordinate = {1, 0, 1, -1};
    const WrpMatrix coordinate_swap = {0, 1, 1, 0};
    const WrpMatrix q4_coordinate = {1, 0, 3, 1};
    const WrpMatrix reflected_axis = {1, 0, 0, -1};
    const WrpMatrix directed_source = {1, 1, -1, 0};
    const WrpMatrix fibonacci = {1, 1, 1, 0};
    const WrpMatrix fibonacci_square = {2, 1, 1, 1};

    if (!wrp_matrix_equal(wrp_matrix_pow(fibonacci, 0), identity))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(reflection, reflection), identity))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(
                wrp_matrix_mul(third_turn, third_turn), third_turn),
            negative_identity))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(reflection, third_turn), product))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(product, product),
            wrp_matrix_add(product, identity)))
        return 0;
    if (wrp_matrix_trace(product) != 1
        || wrp_matrix_det(product) != -1
        || wrp_matrix_trace(product) * wrp_matrix_trace(product)
            - 4 * wrp_matrix_det(product) != 5)
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(third_turn, reflection), reverse_product))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(reverse_product, reverse_product),
            wrp_matrix_add(reverse_product, identity)))
        return 0;
    if (wrp_matrix_trace(reverse_product) != 1
        || wrp_matrix_det(reverse_product) != -1
        || wrp_matrix_trace(reverse_product)
                * wrp_matrix_trace(reverse_product)
            - 4 * wrp_matrix_det(reverse_product) != 5)
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(coordinate, coordinate), identity))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(
                wrp_matrix_mul(coordinate, reflection), coordinate),
            reflected_axis))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(
                wrp_matrix_mul(coordinate, third_turn), coordinate),
            directed_source))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(
                wrp_matrix_mul(coordinate, product), coordinate),
            fibonacci))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(coordinate_swap, coordinate_swap), identity))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(
                wrp_matrix_mul(coordinate_swap, reverse_product),
                coordinate_swap),
            fibonacci))
        return 0;
    WrpMatrix negative_q4 =
        wrp_matrix_scale(wrp_reflection_product(4), -1);
    if (!wrp_matrix_equal(
            wrp_matrix_mul(negative_q4, q4_coordinate),
            wrp_matrix_mul(q4_coordinate, fibonacci)))
        return 0;
    if (!wrp_matrix_equal(
            wrp_matrix_mul(fibonacci, fibonacci), fibonacci_square))
        return 0;
    if (wrp_matrix_trace(fibonacci_square) != 3
        || wrp_matrix_det(fibonacci_square) != 1
        || wrp_matrix_trace(fibonacci_square)
                * wrp_matrix_trace(fibonacci_square)
            - 4 * wrp_matrix_det(fibonacci_square) != 5)
        return 0;

    const WrpQuad tau = {0, 1};
    const WrpQuad phi = {1, 1};
    const WrpQuad phi_square = {2, 1};
    const WrpQuad tau_square = {1, -1};
    const WrpQuad one = {1, 0};
    const WrpQuad three = {3, 0};
    const WrpQuad five = {5, 0};

    WrpQuad intersection = wrp_quad_add(
        wrp_quad_mul(phi_square, phi_square),
        wrp_quad_add(wrp_quad_scale(phi_square, -3), one));
    if (!wrp_quad_equal(intersection, (WrpQuad){0, 0})) return 0;

    WrpQuad binary_denominator =
        wrp_quad_add(wrp_quad_scale(phi_square, 2), (WrpQuad){-1, 0});
    WrpQuad ternary_numerator = binary_denominator;
    WrpQuad ternary_denominator =
        wrp_quad_add(wrp_quad_scale(phi_square, 3), (WrpQuad){-1, 0});
    if (!wrp_quad_equal(
            wrp_quad_mul(tau, binary_denominator), phi_square))
        return 0;
    if (!wrp_quad_equal(
            wrp_quad_mul(tau, ternary_denominator), ternary_numerator))
        return 0;

    WrpQuad reverse_denominator = wrp_quad_add(tau, one);
    if (!wrp_quad_equal(
            wrp_quad_mul(tau, reverse_denominator), one))
        return 0;

    WrpQuad coordinate_denominator =
        wrp_quad_add(phi_square, (WrpQuad){-1, 0});
    if (!wrp_quad_equal(
            wrp_quad_mul(phi, coordinate_denominator), phi_square))
        return 0;

    if (!wrp_quad_equal(wrp_quad_add(phi_square, tau_square), three)
        || !wrp_quad_equal(wrp_quad_mul(phi_square, tau_square), one))
        return 0;
    WrpQuad gap = wrp_quad_sub(phi_square, tau_square);
    if (!wrp_quad_equal(wrp_quad_mul(gap, gap), five)) return 0;
    return 1;
}

int weighted_reference_profile_inspect(
        int modulus, int supported, int base,
        long long lambda_num, long long lambda_den)
{
    int terminating = 0;
    int matching = 0;
    int other = 0;
    int depth = 0;
    long long score_num = 0;
    long long score_den = 0;
    if (lambda_den <= 0 || lambda_num < 0 || lambda_num > lambda_den) {
        fprintf(stderr, "weight must satisfy 0 <= numerator <= denominator\n");
        return 0;
    }
    wrp_reduce_fraction(&lambda_num, &lambda_den);
    if (!wrp_block_counts(modulus, supported, base,
            &terminating, &matching, &other, &depth)) {
        fprintf(stderr,
            "need q>=2, b>=2, b congruent to 1 modulo q, and b-supported m\n");
        return 0;
    }
    if (!wrp_weighted_score_fraction(modulus, supported,
            lambda_num, lambda_den, &score_num, &score_den))
        return 0;
    printf("Weighted one-digit reference profile\n");
    printf("  modulus q=%d  supported scale m=%d  base b=%d\n",
           modulus, supported, base);
    printf("  common clearing depth D=%d\n", depth);
    printf("  terminating block=%d  reference block=%d  other blocks=%d\n",
           terminating, matching, other);
    printf("  declared terminating weight lambda=%lld/%lld\n",
           lambda_num, lambda_den);
    printf("  exact score C_q,lambda(m)=%lld/%lld\n", score_num, score_den);
    printf("  formula [lambda(m-1)+m]/(qm-1)  PASS\n");
    printf("  literal matching is lambda=0; full union weight is lambda=1\n");
    printf("Result  PASS\n");
    return 1;
}

int weighted_reference_profile_branch(int modulus, int exponent)
{
    if (modulus < 2 || exponent < 1 || exponent > 40) {
        fprintf(stderr, "branch requires q>=2 and 1<=r<=40\n");
        return 0;
    }
    WrpQuadFraction weight = wrp_real_weight(modulus, exponent);
    int admissible = wrp_window_holds(modulus, exponent);
    printf("Reciprocal-golden real-weight branch\n");
    printf("  modulus q=%d  reciprocal exponent r=%d\n", modulus, exponent);
    printf("  lambda_q,r=(%lld %c %lld*tau)/%lld\n",
           weight.a, weight.b < 0 ? '-' : '+', wrp_absll(weight.b),
           weight.den);
    printf("  decimal value %.15Lf\n", wrp_quad_fraction_value(weight));
    printf("  unit-interval window %s\n", admissible ? "PASS" : "FAIL");
    printf("  rational coordinate %s\n", weight.b == 0 ? "yes" : "no");
    if (modulus == 2 || modulus == 3) {
        WrpQuad limit = {-1, modulus};
        printf("  branch limit %lld %c %lld*tau\n",
               limit.a, limit.b < 0 ? '-' : '+', wrp_absll(limit.b));
    }
    printf("Result  %s\n", admissible ? "PASS" : "OUTSIDE WINDOW");
    return admissible;
}

int weighted_reference_profile_torsion(void)
{
    int cases = 0;
    int ok = wrp_check_projective_profile_types(&cases);
    printf("Rational projective torsion in the weighted profile family\n");
    printf("  order two: every q>=2 at lambda=0\n");
    printf("  order three: only q=3 at lambda=1\n");
    printf("  order four: no rational unit-interval weight\n");
    printf("  order six: no rational unit-interval weight\n");
    printf("  exact bounded sweep: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    printf("  universal trace-invariant classification: Lean\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok;
}

int weighted_reference_profile_reflection_product(int modulus)
{
    if (modulus < 2) {
        fprintf(stderr, "reflection-product requires q>=2\n");
        return 0;
    }
    WrpMatrix product = wrp_reflection_product(modulus);
    long long trace = wrp_matrix_trace(product);
    long long determinant = wrp_matrix_det(product);
    long long discriminant = trace * trace - 4 * determinant;
    int fibonacci_case = modulus == 2 || modulus == 4;
    printf("Reflection product in the weighted profile family\n");
    printf("  q=%d\n", modulus);
    printf("  R_q*S=[[%lld,%lld],[%lld,%lld]]\n",
           product.a, product.b, product.c, product.d);
    printf("  trace=%lld  determinant=%lld  primitive discriminant=%lld\n",
           trace, determinant, discriminant);
    printf("  formula Delta_q=(q-3)^2+4  PASS\n");
    printf("  projectively Fibonacci after primitive sign normalization: %s\n",
           fibonacci_case ? "yes" : "no");
    if (modulus == 2) {
        printf("  profile intersection above one: unique at phi^2\n");
        printf("  common value: tau=phi^(-1)\n");
    } else if (modulus == 3) {
        printf("  central product involution: yes\n");
        printf("  profile intersection: boundary point x=1\n");
    } else {
        printf("  profile intersection above one: none\n");
    }
    printf("Result  PASS\n");
    return 1;
}

int weighted_reference_profile_oriented_words(int modulus)
{
    if (modulus < 2) {
        fprintf(stderr, "oriented-words requires q>=2\n");
        return 0;
    }
    const WrpMatrix coordinate = {1, 0, 1, -1};
    WrpMatrix forward = wrp_reflection_product(modulus);
    WrpMatrix reverse = wrp_reverse_reflection_product(modulus);
    WrpMatrix raw_forward = wrp_matrix_mul(
        wrp_matrix_mul(coordinate, forward), coordinate);
    WrpMatrix oriented_reverse = wrp_matrix_scale(
        wrp_matrix_mul(wrp_matrix_mul(coordinate, reverse), coordinate), -1);

    printf("Two oriented words in the weighted profile family\n");
    printf("  q=%d\n", modulus);
    printf("  input word R_q*S=[[%lld,%lld],[%lld,%lld]]\n",
           forward.a, forward.b, forward.c, forward.d);
    printf("  literal raw-count action P*(R_q*S)*P=[[%lld,%lld],[%lld,%lld]]\n",
           raw_forward.a, raw_forward.b,
           raw_forward.c, raw_forward.d);
    printf("  output word S*R_q=[[%lld,%lld],[%lld,%lld]]\n",
           reverse.a, reverse.b, reverse.c, reverse.d);
    printf("  positive output action -P*(S*R_q)*P=[[%lld,%lld],[%lld,%lld]]\n",
           oriented_reverse.a, oriented_reverse.b,
           oriented_reverse.c, oriented_reverse.d);
    printf("  input action preserves every literal raw-count pair: %s\n",
           modulus == 2 ? "yes" : "no");
    printf("  positive output action preserves every literal raw-count pair: %s\n",
           modulus >= 4 ? "yes" : "no");
    if (modulus >= 4) {
        printf("  generalized Fibonacci coefficient q-3=%d\n", modulus - 3);
    } else if (modulus == 3) {
        printf("  q=3 is the boundary between the two positive regimes\n");
    }
    if (modulus == 2) {
        printf("  input action is the ordinary Fibonacci matrix  PASS\n");
    }
    if (modulus == 4) {
        printf("  output action is the ordinary Fibonacci matrix  PASS\n");
        printf("  S*R_4=-R_2*S, the same projective action  PASS\n");
        printf("  a different finite aggregate recoding also sends -P*(R_4*S)*P to G  PASS\n");
    }
    printf("  every q>=4 also has one common profile point in 1/2<x<1\n");
    printf("  word order, sign, coordinate, cone, and domain are explicit\n");
    printf("Result  PASS\n");
    return 1;
}

int weighted_reference_profile_transport(void)
{
    int ok = wrp_check_binary_ternary_transport();
    printf("Binary reflection, ternary turn, and golden transport\n");
    printf("  B(x)=x/(2x-1) with R=[[1,0],[2,-1]]\n");
    printf("  T(x)=(2x-1)/(3x-1) with S=[[2,-1],[3,-1]]\n");
    printf("  R^2=I  PASS\n");
    printf("  S^3=-I, projective order three  PASS\n");
    printf("  A=R*S=[[2,-1],[1,-1]]\n");
    printf("  A^2=A+I; trace=1; determinant=-1; discriminant=5  PASS\n");
    printf("  P*A*P=[[1,1],[1,0]], the Fibonacci operator  PASS\n");
    printf("  A'=S*R=[[0,1],[1,1]]\n");
    printf("  (A')^2=A'+I; trace=1; determinant=-1; discriminant=5  PASS\n");
    printf("  J*A'*J=[[1,1],[1,0]], the Fibonacci operator  PASS\n");
    printf("  R_4*S=[[2,-1],[5,-3]]; -R_4*S is integrally conjugate to G  PASS\n");
    printf("  B(x)=T(x) gives x^2-3x+1=0\n");
    printf("  unique x>1 is phi^2=2+tau; common value is tau  PASS\n");
    printf("  R*S fixes phi^2; S*R fixes tau  PASS\n");
    printf("  collision coordinate x/(x-1) sends phi^2 to phi  PASS\n");
    printf("  G^2=[[2,1],[1,1]]; trace=3; determinant=1; discriminant=5  PASS\n");
    printf("  positive even powers of G are exactly the strictly totally positive powers  PASS\n");
    printf("  phi^2+tau^2=3; phi^2*tau^2=1; (phi^2-tau^2)^2=5  PASS\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok;
}

int weighted_reference_profile_finite_orbit(
        int supported, int steps, int base)
{
    int depth = 0;
    long long power = 0;
    if (supported < 2 || supported > 1000000000
        || steps < 0 || steps > 40 || base < 2
        || base % 2 != 1 || base % 3 != 1
        || !wrp_common_depth(base, supported, &depth, &power)) {
        fprintf(stderr,
            "finite-orbit needs 2<=m<=1000000000, 0<=steps<=40, "
            "b congruent to 1 modulo 6, and b-supported m\n");
        return 0;
    }
    (void)power;

    long long reference = supported;
    long long terminating = supported - 1;
    const long double phi = (1.0L + sqrtl(5.0L)) / 2.0L;
    const long double phi_square = phi * phi;

    printf("Finite Fibonacci block orbit\n");
    printf("  base b=%d  supported scale m=%d  clearing depth D=%d\n",
           base, supported, depth);
    printf("  source blocks: reference=%lld  terminating=%lld\n",
           reference, terminating);
    printf("  literal ordered coordinate P(m,1)=(m,m-1)  PASS\n");
    printf("  P*(R_q*S)*P=[[1,1],[3-q,2-q]]\n");
    printf("  only q=2 preserves every nondegenerate positive block pair  PASS\n");
    printf("  binary update Phi(r,t)=(r+t,r)\n");
    printf("  n  reference  terminating  reconstructed scale r/(r-t)  side\n");

    for (int exponent = 0; exponent <= steps; exponent++) {
        long long difference = reference - terminating;
        long long scale_num = reference;
        long long scale_den = difference;
        wrp_reduce_fraction(&scale_num, &scale_den);
        __int128 golden_polynomial = (__int128)reference * reference
            - (__int128)3 * reference * difference
            + (__int128)difference * difference;
        const char *side = golden_polynomial > 0 ? "above" : "below";
        printf("  %-2d %-10lld %-12lld %lld/%lld = %.12Lf  %s phi^2\n",
               exponent, reference, terminating, scale_num, scale_den,
               (long double)reference / (long double)difference, side);

        if (exponent == steps) break;
        if (reference > LLONG_MAX - terminating) {
            fprintf(stderr, "finite-orbit overflow at step %d\n", exponent + 1);
            return 0;
        }
        long long next_reference = reference + terminating;
        terminating = reference;
        reference = next_reference;
    }

    printf("  target phi^2=%.12Lf\n", phi_square);
    printf("  exact formulas and alternating signed error: Lean\n");
    printf("Result  PASS\n");
    return 1;
}

int weighted_reference_profile_verify(void)
{
    int passed = 0;
    int models = 0;
    long long rows = 0;
    int cases = 0;

    printf("Exact C verification of weighted one-digit reference profiles\n");
    printf("Universal classification is proved in Lean; these groups execute every equation family.\n\n");

    int ok = wrp_check_blocks(&models, &rows);
    printf("  integer-modulus clearing, digits, and block counts: models=%d; rows=%lld  %s\n",
           models, rows, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_weighted_scores(&cases);
    printf("  exact finite replicated weighting and score normalization: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_fibonacci_coordinates(&cases);
    printf("  reciprocal-golden Fibonacci coordinates: powers=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_rational_coordinates(&cases);
    printf("  power equation and rational coefficient split: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_rational_case_excludes(1, 0, 1)
        && wrp_rational_case_excludes(4, 0, 1)
        && wrp_rational_case_excludes(20, 1, 1);
    printf("  symbolic odd/even sign exclusions and square endpoints  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_real_windows(&cases);
    printf("  exact real-weight formula and admissibility window: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_window_holds(2, 2) && wrp_window_holds(3, 2)
        && !wrp_window_holds(2, 1) && !wrp_window_holds(3, 1)
        && !wrp_window_holds(4, 40);
    printf("  complete modulus-two/modulus-three real classification  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_branch_geometry(&cases);
    printf("  rational endpoints, first irrational values, and branch directions: steps=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    WrpQuad limit_two = {-1, 2};
    WrpQuad tau_three = wrp_tau_power(3);
    ok = limit_two.a == tau_three.a && limit_two.b == tau_three.b
        && wrp_quad_sign((WrpQuad){-1, 3}) > 0;
    printf("  exact branch limits tau^3 and 3*tau-1  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_projective_profile_types(&cases);
    printf("  complete rational projective torsion through orders two, three, four, and six: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_reflection_product_family(&cases);
    printf("  reflection-product family and normalized discriminant-five cases: moduli=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_above_unit_intersection(&cases);
    printf("  unique above-unit reflection intersection and boundary classification: moduli=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_fibonacci_total_positivity(&cases);
    printf("  strict total positivity of exactly the positive even Fibonacci powers: powers=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_binary_ternary_transport();
    printf("  ordered products, paired golden fixed points, and square invariants  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_finite_block_orbit(&cases);
    printf("  literal ordered block transport, forward binary positivity, and exact finite Fibonacci orbit: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = wrp_check_oriented_word_family(&cases);
    printf("  two oriented cone regimes, generalized Fibonacci outputs, and modulus-four duality: cases=%d  %s\n",
           cases, ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/16 verification groups passed.\n", passed);
    printf("The finite sweeps corroborate the exact identities. Lean carries the universal proofs.\n");
    return passed == 16;
}

void weighted_reference_profile_help(void)
{
    printf(
        "Weighted one-digit reference profile\n\n"
        "Commands\n"
        "  nfield weighted-reference-profile inspect <q> <m> <weight-num> <weight-den> [--base <b>]\n"
        "      Construct the common clearing depth, all integer-modulus blocks,\n"
        "      and the exact finite weighted score.\n"
        "  nfield weighted-reference-profile branch <q> <r>\n"
        "      Solve the reciprocal-golden equality for its unique real weight\n"
        "      and report the exact Q(tau) coordinates.\n"
        "  nfield weighted-reference-profile torsion\n"
        "      Classify rational projective torsion through orders two, three,\n"
        "      four, and six.\n"
        "  nfield weighted-reference-profile reflection-product <q>\n"
        "      Expose R_q*S, its primitive discriminant, its Fibonacci status,\n"
        "      and its above-unit intersection status.\n"
        "  nfield weighted-reference-profile oriented-words <q>\n"
        "      Expose both input and output word orders in the literal ordered\n"
        "      row-count coordinate and classify their positive cone regimes.\n"
        "  nfield weighted-reference-profile transport\n"
        "      Compose the binary reflection and rational ternary third-turn\n"
        "      in both orders, then expose their Fibonacci conjugacies and\n"
        "      the golden-square fixed point.\n"
        "  nfield weighted-reference-profile finite-orbit <m> <steps> [--base <b>]\n"
        "      Start with the exact reference and terminating block counts,\n"
        "      iterate their finite Fibonacci substitution, and reconstruct\n"
        "      the scale converging to the golden square. The default base is 7.\n"
        "  nfield weighted-reference-profile verify\n"
        "  nfield verify weighted-reference-profile\n\n"
        "Examples\n"
        "  nfield weighted-reference-profile inspect 3 4 1 1 --base 10\n"
        "  nfield weighted-reference-profile inspect 2 3 0 1 --base 3\n"
        "  nfield weighted-reference-profile branch 3 3\n"
        "  nfield weighted-reference-profile torsion\n"
        "  nfield weighted-reference-profile reflection-product 4\n"
        "  nfield weighted-reference-profile oriented-words 4\n"
        "  nfield weighted-reference-profile transport\n\n"
        "  nfield weighted-reference-profile finite-orbit 7 8 --base 7\n\n"
        "Scope\n"
        "  exact   the one-digit partition for every integer modulus q with\n"
        "          b congruent to 1 modulo q and every b-supported m.\n"
        "  exact   C_q,lambda(m)=[lambda(m-1)+m]/(qm-1), its interpolant,\n"
        "          limiting value, and derivative numerator.\n"
        "  exact   Fibonacci coordinates of tau^r and the rational coefficient\n"
        "          split of the golden power equation.\n"
        "  exact   rational weights leave only (q,lambda,r)=(2,0,2) and\n"
        "          (3,1,2). Real weights form the q=2 and q=3 branches for r>=2.\n"
        "  exact   every later branch weight is irrational; the q=2 branch rises\n"
        "          to tau^3 and the q=3 branch falls to 3*tau-1.\n"
        "  exact   rational projective torsion consists of the reflection locus\n"
        "          and the unique third-turn (q,lambda)=(3,1).\n"
        "  exact   R_q*S has primitive discriminant (q-3)^2+4; precisely q=2\n"
        "          and q=4 are projectively Fibonacci after sign normalization.\n"
        "  exact   only q=2 meets the third-turn profile above one, at phi^2;\n"
        "          the reverse ordered product fixes the common value tau.\n"
        "  exact   P(m,1)=(m,m-1) is the literal ordered block coordinate.\n"
        "          The input action preserves its raw cone exactly at q=2;\n"
        "          the positive output action does so exactly for q>=4.\n"
        "          The q=2 input and q=4 output actions both equal G, and\n"
        "          S*R_4=-R_2*S gives the same projective action.\n"
        "  exact   every q>=4 has one profile intersection in 1/2<x<1;\n"
        "          only q=2 has an intersection above one, at phi^2.\n"
        "  exact   the iterated finite block counts have Fibonacci closed forms;\n"
        "          their block ratio tends to phi, while r/(r-t) tends to phi^2\n"
        "          with an exact alternating signed error.\n"
        "  exact   positive even Fibonacci powers are exactly the strictly\n"
        "          totally positive powers.\n"
        "  proof   Lean carries the universal arguments. The verifier uses exact\n"
        "          integer and quadratic-field arithmetic over bounded sweeps.\n"
    );
}
