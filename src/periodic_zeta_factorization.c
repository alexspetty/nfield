/* Direct periodic-zeta model sums and analytic-transform factorization. */

#include <complex.h>
#include <stdio.h>

#include "nfield.h"
#include "periodic_zeta_core.h"

static void print_complex_value(const char *label,
                                long double complex value)
{
    printf("  %-24s %+.12Lf %+.12Lfi\n",
           label, creall(value), cimagl(value));
}

static int integer_power(int base, int exponent)
{
    int result = 1;
    for (int index = 0; index < exponent; index++) result *= base;
    return result;
}

static int diagonal_structure_exact(const PeriodicZetaContext *context)
{
    int expected;
    if (!context || context->base < 2 || context->lag < 1) return 0;
    expected = integer_power(context->base, context->lag);
    if (context->modulus != expected * context->base ||
        context->phi != context->modulus - context->modulus / context->base ||
        context->diagonal_count != expected ||
        context->diagonal[0] != 0 ||
        context->diagonal[context->diagonal_count - 1] !=
            context->modulus - 1)
        return 0;
    for (int index = 0; index < context->diagonal_count; index++) {
        int residue = context->diagonal[index];
        if (residue / expected != residue % context->base) return 0;
        if (context->lag == 1 &&
            residue != index * (context->base + 1))
            return 0;
    }
    return 1;
}

int periodic_zeta_factorization_inspect(
    int base, int lag, int character_index, long double sigma,
    long double tau)
{
    PeriodicZetaContext context;
    PeriodicZetaComparison unit_model;
    PeriodicZetaComparison nonunit_model;
    PeriodicZetaComparison transform;
    char error[160];
    long double complex s = sigma + I * tau;
    int diagonal_exact;

    if (!periodic_zeta_context_build(
            base, lag, &context, error, sizeof(error))) {
        fprintf(stderr, "%s\n", error);
        return 1;
    }
    if (!periodic_zeta_character_valid(&context, character_index)) {
        fprintf(stderr,
                "character index must identify a primitive odd character\n");
        periodic_zeta_context_free(&context);
        return 1;
    }
    if (sigma <= 0.0L || sigma >= 1.0L) {
        fprintf(stderr, "sigma must lie strictly between zero and one\n");
        periodic_zeta_context_free(&context);
        return 1;
    }
    if (!periodic_zeta_model_comparison(
            &context, character_index, 1, s, &unit_model) ||
        !periodic_zeta_model_comparison(
            &context, character_index, base, s, &nonunit_model) ||
        !periodic_zeta_transform_comparison(
            &context, character_index, s, &transform)) {
        fprintf(stderr, "unable to evaluate the periodic-zeta comparison\n");
        periodic_zeta_context_free(&context);
        return 1;
    }
    diagonal_exact = diagonal_structure_exact(&context);

    printf("Periodic-zeta factorization\n");
    printf("One primitive odd channel\n\n");
    printf("  base=%d lag=%d modulus=%d phi=%d character-index=%d\n",
           context.base, context.lag, context.modulus,
           context.phi, character_index);
    printf("  diagonal slices=%d; expected=%d\n",
           context.diagonal_count, integer_power(context.base, context.lag));
    printf("  exact diagonal definition, cardinality, and endpoints  %s\n",
           diagonal_exact ? "PASS" : "FAIL");
    printf("  s=%.8Lf%+.8Lfi\n\n", sigma, tau);
    print_complex_value("diagonal boundary", transform.diagonal);
    print_complex_value("L(s, conjugate chi)", transform.l_value);
    print_complex_value("unit model direct", unit_model.left);
    print_complex_value("unit model factored", unit_model.right);
    printf("  unit model relative error      %.3Le\n",
           unit_model.relative_error);
    print_complex_value("nonunit model direct", nonunit_model.left);
    print_complex_value("nonunit model target", nonunit_model.right);
    printf("  nonunit cancellation error     %.3Le\n",
           nonunit_model.relative_error);
    print_complex_value("transform direct", transform.left);
    print_complex_value("transform factored", transform.right);
    printf("  transform relative error       %.3Le\n",
           transform.relative_error);
    int passed = diagonal_exact &&
                 unit_model.relative_error <= 5.0e-11L &&
                 nonunit_model.relative_error <= 5.0e-11L &&
                 transform.relative_error <= 5.0e-11L;
    printf("\nClassification  long-double numerical corroboration of exact\n");
    printf("fixed-conductor identities; this is not interval-certified arithmetic.\n");
    printf("Result  %s\n", passed ? "PASS" : "FAIL");
    periodic_zeta_context_free(&context);
    return passed ? 0 : 1;
}

int periodic_zeta_factorization_verify(void)
{
    static const int contexts[][2] = {
        {2, 1}, {2, 2}, {2, 3}, {3, 1}, {3, 2}, {5, 1}, {7, 1}
    };
    static const long double complex samples[] = {
        0.25L, 0.50L + 0.20L * I, 0.75L - 0.15L * I
    };
    int failures = 0;
    int diagonal_failures = 0;
    int characters = 0;
    int comparisons = 0;
    long double maximum_model_error = 0.0L;
    long double maximum_transform_error = 0.0L;

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
        if (!diagonal_structure_exact(&context)) {
            diagonal_failures++;
            failures++;
        }
        int limit = context.base != 2 ? context.phi :
                    (context.exponent == 2 ? 2 : context.cyclic_order);
        for (int character = 1; character < limit; character++) {
            if (!periodic_zeta_character_valid(&context, character)) continue;
            characters++;
            for (size_t sample = 0;
                 sample < sizeof(samples) / sizeof(samples[0]); sample++) {
                PeriodicZetaComparison unit_model;
                PeriodicZetaComparison nonunit_model;
                PeriodicZetaComparison transform;
                if (!periodic_zeta_model_comparison(
                        &context, character, 1, samples[sample], &unit_model) ||
                    !periodic_zeta_model_comparison(
                        &context, character, context.base, samples[sample],
                        &nonunit_model) ||
                    !periodic_zeta_transform_comparison(
                        &context, character, samples[sample], &transform)) {
                    failures++;
                    continue;
                }
                comparisons += 3;
                if (unit_model.relative_error > maximum_model_error)
                    maximum_model_error = unit_model.relative_error;
                if (nonunit_model.relative_error > maximum_model_error)
                    maximum_model_error = nonunit_model.relative_error;
                if (transform.relative_error > maximum_transform_error)
                    maximum_transform_error = transform.relative_error;
                if (unit_model.relative_error > 5.0e-11L ||
                    nonunit_model.relative_error > 5.0e-11L ||
                    transform.relative_error > 5.0e-11L)
                    failures++;
            }
        }
        periodic_zeta_context_free(&context);
    }

    printf("Periodic-zeta factorization verification\n\n");
    printf("  exact diagonal definition, cardinality, and endpoints  %s\n",
           diagonal_failures == 0 ? "PASS" : "FAIL");
    printf("  odd-prime and noncyclic two-power character models  %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  primitive odd characters=%d; comparisons=%d\n",
           characters, comparisons);
    printf("  maximum model-sum error %.3Le                      %s\n",
           maximum_model_error,
           maximum_model_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("  maximum full-transform error %.3Le                 %s\n",
           maximum_transform_error,
           maximum_transform_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("\n5/5 verification groups %s.\n",
           failures == 0 && maximum_model_error <= 5.0e-11L &&
                   maximum_transform_error <= 5.0e-11L
               ? "passed" : "did not pass");
    printf("Analytic identity  the model sum and transform factorization hold\n");
    printf("throughout the open critical strip.\n");
    printf("Numerical boundary  this verifier samples three complex points in\n");
    printf("seven fixed prime-power contexts; it does not prove analytic continuation.\n");
    return failures == 0 && maximum_model_error <= 5.0e-11L &&
           maximum_transform_error <= 5.0e-11L;
}

void periodic_zeta_factorization_help(void)
{
    printf(
        "Periodic-zeta factorization\n\n"
        "Commands\n"
        "  nfield periodic-zeta-factorization inspect <base> <lag> <character-index> [--sigma <x>] [--tau <y>]\n"
        "      Compare a unit model sum, a nonunit cancellation sum, and the\n"
        "      complete centered transform with their factorized values.\n"
        "  nfield periodic-zeta-factorization verify\n"
        "  nfield verify periodic-zeta-factorization\n\n"
        "Scope\n"
        "  exact structure    diagonal definition, cardinality, endpoints, modulus, and totient.\n"
        "  analytic identity  exact periodic-zeta model sum and transform factorization.\n"
        "  finite numerical  selected primitive odd channels and complex strip points.\n"
        "  method             long-double Lanczos gamma and Euler-Maclaurin Hurwitz zeta.\n"
        "  limit              base^(lag+1) must not exceed 4096.\n"
        "  open               no zero location, positivity, or conductor-uniform estimate.\n"
    );
}
