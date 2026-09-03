/* Left collision recovery and the separately Gauss-twisted right boundary. */

#include <complex.h>
#include <math.h>
#include <stdio.h>

#include "nfield.h"
#include "periodic_zeta_core.h"

static long double scaled_error(long double complex left,
                                long double complex right)
{
    return cabsl(left - right) /
           fmaxl(1.0L, fmaxl(cabsl(left), cabsl(right)));
}

static void print_complex_value(const char *label,
                                long double complex value)
{
    printf("  %-26s %+.12Lf %+.12Lfi\n",
           label, creall(value), cimagl(value));
}

int collision_boundary_recovery_inspect(
    int base, int lag, int character_index)
{
    PeriodicZetaContext context;
    char error[160];
    long double complex left_direct;
    long double complex left_factorized;
    long double complex right_direct;
    long double complex right_factorized;
    long double complex right_l_value;
    int passed;

    if (!periodic_zeta_context_build(
            base, lag, &context, error, sizeof(error))) {
        fprintf(stderr, "%s\n", error);
        return 1;
    }
    if (!periodic_zeta_boundary_values(
            &context, character_index, &left_direct, &left_factorized,
            &right_direct, &right_factorized, &right_l_value)) {
        fprintf(stderr,
                "character index must identify a primitive odd character\n");
        periodic_zeta_context_free(&context);
        return 1;
    }
    passed = scaled_error(left_direct, left_factorized) <= 5.0e-11L &&
             scaled_error(right_direct, right_factorized) <= 5.0e-11L &&
             scaled_error(right_l_value, right_factorized) <= 5.0e-11L;

    printf("Collision-boundary recovery\n\n");
    printf("  base=%d lag=%d modulus=%d character-index=%d\n\n",
           context.base, context.lag, context.modulus, character_index);
    print_complex_value("left boundary direct", left_direct);
    print_complex_value("left Bernoulli value", left_factorized);
    printf("  left relative error          %.3Le\n",
           scaled_error(left_direct, left_factorized));
    print_complex_value("right boundary direct", right_direct);
    print_complex_value("right Gauss value", right_factorized);
    print_complex_value("right cotangent L value", right_l_value);
    printf("  right relative error         %.3Le\n",
           scaled_error(right_direct, right_factorized));

    if (context.base != 2 && context.lag == 1) {
        long double complex collision_direct;
        long double complex collision_factorized;
        long double complex recovered;
        periodic_zeta_finite_collision_coefficient(
            &context, character_index,
            &collision_direct, &collision_factorized);
        recovered = I * acosl(-1.0L) * collision_direct;
        print_complex_value("finite collision direct", collision_direct);
        print_complex_value("finite collision factored", collision_factorized);
        print_complex_value("i*pi collision value", recovered);
        printf("  exact-recovery numerical error %.3Le\n",
               scaled_error(left_direct, recovered));
        if (scaled_error(collision_direct, collision_factorized) > 5.0e-11L ||
            scaled_error(left_direct, recovered) > 5.0e-11L)
            passed = 0;
    } else {
        printf("\n  finite collision recovery applies only at lag one in an odd prime base.\n");
    }
    printf("\nClassification  exact finite formulas with long-double roots-of-unity,\n");
    printf("logarithm, and cotangent evaluation.\n");
    printf("Result  %s\n", passed ? "PASS" : "FAIL");
    periodic_zeta_context_free(&context);
    return passed ? 0 : 1;
}

int collision_boundary_recovery_verify(void)
{
    static const int contexts[][2] = {
        {2, 1}, {2, 2}, {2, 3},
        {3, 1}, {3, 2}, {5, 1}, {7, 1}, {11, 1}
    };
    int failures = 0;
    int characters = 0;
    int finite_recoveries = 0;
    long double maximum_boundary_error = 0.0L;
    long double maximum_collision_error = 0.0L;

    for (size_t context_index = 0;
         context_index < sizeof(contexts) / sizeof(contexts[0]);
         context_index++) {
        PeriodicZetaContext context;
        char error[160];
        if (!periodic_zeta_context_build(
                contexts[context_index][0], contexts[context_index][1],
                &context, error, sizeof(error))) {
            failures++;
            continue;
        }
        int limit = context.base != 2 ? context.phi :
                    (context.exponent == 2 ? 2 : context.cyclic_order);
        for (int character = 1; character < limit; character++) {
            long double complex left_direct;
            long double complex left_factorized;
            long double complex right_direct;
            long double complex right_factorized;
            long double complex right_l_value;
            if (!periodic_zeta_character_valid(&context, character)) continue;
            characters++;
            if (!periodic_zeta_boundary_values(
                    &context, character,
                    &left_direct, &left_factorized,
                    &right_direct, &right_factorized, &right_l_value)) {
                failures++;
                continue;
            }
            long double left_error =
                scaled_error(left_direct, left_factorized);
            long double right_error =
                scaled_error(right_direct, right_factorized);
            long double l_error =
                scaled_error(right_l_value, right_factorized);
            if (left_error > maximum_boundary_error)
                maximum_boundary_error = left_error;
            if (right_error > maximum_boundary_error)
                maximum_boundary_error = right_error;
            if (l_error > maximum_boundary_error)
                maximum_boundary_error = l_error;
            if (left_error > 5.0e-11L || right_error > 5.0e-11L ||
                l_error > 5.0e-11L)
                failures++;

            if (context.base != 2 && context.lag == 1) {
                long double complex collision_direct;
                long double complex collision_factorized;
                long double collision_error;
                long double recovery_error;
                if (!periodic_zeta_finite_collision_coefficient(
                        &context, character,
                        &collision_direct, &collision_factorized)) {
                    failures++;
                    continue;
                }
                finite_recoveries++;
                collision_error = scaled_error(
                    collision_direct, collision_factorized);
                recovery_error = scaled_error(
                    left_direct,
                    I * acosl(-1.0L) * collision_direct);
                if (collision_error > maximum_collision_error)
                    maximum_collision_error = collision_error;
                if (recovery_error > maximum_collision_error)
                    maximum_collision_error = recovery_error;
                if (collision_error > 5.0e-11L || recovery_error > 5.0e-11L)
                    failures++;
            }
        }
        periodic_zeta_context_free(&context);
    }

    printf("Collision-boundary recovery verification\n\n");
    printf("  general left and Gauss-twisted right boundaries  %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  characters=%d; lag-one finite recoveries=%d\n",
           characters, finite_recoveries);
    printf("  maximum boundary error %.3Le                    %s\n",
           maximum_boundary_error,
           maximum_boundary_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("  maximum finite-recovery error %.3Le              %s\n",
           maximum_collision_error,
           maximum_collision_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("\n4/4 verification groups %s.\n",
           failures == 0 ? "passed" : "did not pass");
    printf("Identity  the left boundary is i*pi times the lag-one finite\n");
    printf("coefficient; the opposite boundary carries the Gauss twist.\n");
    printf("Finite boundary  direct logarithm and cotangent transforms are evaluated\n");
    printf("for eight declared prime-power contexts.\n");
    return failures == 0;
}

void collision_boundary_recovery_help(void)
{
    printf(
        "Collision-boundary recovery\n\n"
        "Commands\n"
        "  nfield collision-boundary-recovery inspect <base> <lag> <character-index>\n"
        "      Compare direct left and right boundary transforms with their\n"
        "      Bernoulli and Gauss-twisted values. At odd-prime lag one, also\n"
        "      recover the centered finite collision coefficient.\n"
        "  nfield collision-boundary-recovery verify\n"
        "  nfield verify collision-boundary-recovery\n\n"
        "Scope\n"
        "  analytic identity  general left boundary, universal i*pi lag-one recovery,\n"
        "                     and the separate Gauss-twisted right boundary.\n"
        "  exact computation finite collision values and character tables.\n"
        "  numerical check   complex logarithm, cotangent, and roots of unity.\n"
        "  limit              base^(lag+1) must not exceed 4096.\n"
    );
}
