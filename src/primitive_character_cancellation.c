/* Exact prime-power fibers with numerical roots-of-unity cancellation. */

#include <complex.h>
#include <math.h>
#include <stdio.h>

#include "nfield.h"
#include "periodic_zeta_core.h"

typedef struct {
    int characters;
    int fibers;
    int failures;
    long double maximum_sum;
    long double maximum_odd_error;
} FiberCancellationSummary;

static int integer_power(int base, int exponent)
{
    int result = 1;
    for (int index = 0; index < exponent; index++) result *= base;
    return result;
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

static int audit_context(int base, int lag, int requested_character,
                         int report, FiberCancellationSummary *summary)
{
    PeriodicZetaContext context;
    char error[160];
    int limit;

    if (!summary) return 0;
    *summary = (FiberCancellationSummary){0};
    if (!periodic_zeta_context_build(
            base, lag, &context, error, sizeof(error))) {
        if (report) fprintf(stderr, "%s\n", error);
        return 0;
    }
    if (context.base != 2) limit = context.phi;
    else if (context.exponent == 2) limit = 2;
    else limit = context.cyclic_order;

    for (int character = 1; character < limit; character++) {
        if (!periodic_zeta_character_valid(&context, character)) continue;
        if (requested_character > 0 && character != requested_character)
            continue;
        summary->characters++;
        long double odd_error = cabsl(
            periodic_zeta_character_value(
                &context, character, context.modulus - 1) + 1.0L);
        if (odd_error > summary->maximum_odd_error)
            summary->maximum_odd_error = odd_error;
        if (odd_error > 2.0e-15L) summary->failures++;

        int conductor_witness;
        if (context.base != 2)
            conductor_witness = modular_power(
                context.generator, context.phi / context.base,
                context.modulus);
        else if (context.exponent == 2)
            conductor_witness = 3;
        else
            conductor_witness = 1 + context.modulus / 2;
        if (cabsl(periodic_zeta_character_value(
                      &context, character, conductor_witness) - 1.0L) <
            1.0e-12L)
            summary->failures++;

        for (int depth = 1; depth <= context.lag; depth++) {
            int modulus = integer_power(context.base, depth);
            int expected_count = context.modulus / modulus;
            for (int residue = 1; residue < modulus; residue++) {
                if (residue % context.base == 0) continue;
                long double complex sum = 0.0L;
                int count = 0;
                for (int index = 0; index < context.unit_count; index++) {
                    int unit = context.units[index];
                    if (unit % modulus != residue) continue;
                    sum += conjl(periodic_zeta_character_value(
                        &context, character, unit));
                    count++;
                }
                summary->fibers++;
                if (cabsl(sum) > summary->maximum_sum)
                    summary->maximum_sum = cabsl(sum);
                if (count != expected_count || cabsl(sum) > 2.0e-12L)
                    summary->failures++;
            }
        }
    }
    if (requested_character > 0 && summary->characters != 1) {
        if (report)
            fprintf(stderr,
                    "character index must identify a primitive odd character\n");
        periodic_zeta_context_free(&context);
        return 0;
    }
    if (report) {
        printf("Primitive-character fiber cancellation\n\n");
        printf("  base=%d lag=%d modulus=%d phi=%d\n",
               context.base, context.lag, context.modulus, context.phi);
        printf("  primitive odd characters checked = %d\n",
               summary->characters);
        printf("  congruence fibers checked = %d\n", summary->fibers);
        printf("  maximum fiber-sum magnitude = %.3Le\n",
               summary->maximum_sum);
        printf("  maximum odd-character error = %.3Le\n",
               summary->maximum_odd_error);
        printf("  conductor witnesses and exact fiber sizes  %s\n",
               summary->failures == 0 ? "PASS" : "FAIL");
        printf("\nClassification  exact residue enumeration with long-double\n");
        printf("roots-of-unity evaluation of the character sums.\n");
        printf("Result  %s\n", summary->failures == 0 ? "PASS" : "FAIL");
    }
    periodic_zeta_context_free(&context);
    return 1;
}

int primitive_character_cancellation_inspect(
    int base, int lag, int character_index)
{
    FiberCancellationSummary summary;
    return audit_context(base, lag, character_index, 1, &summary) &&
           summary.failures == 0 ? 0 : 1;
}

int primitive_character_cancellation_verify(void)
{
    static const int contexts[][2] = {
        {2, 1}, {2, 2}, {2, 3}, {2, 4},
        {3, 1}, {3, 2}, {3, 3},
        {5, 1}, {5, 2}, {7, 1}
    };
    int failures = 0;
    int characters = 0;
    int fibers = 0;
    long double maximum_sum = 0.0L;

    for (size_t index = 0; index < sizeof(contexts) / sizeof(contexts[0]);
         index++) {
        FiberCancellationSummary summary;
        if (!audit_context(contexts[index][0], contexts[index][1],
                           0, 0, &summary)) {
            failures++;
            continue;
        }
        failures += summary.failures;
        characters += summary.characters;
        fibers += summary.fibers;
        if (summary.maximum_sum > maximum_sum)
            maximum_sum = summary.maximum_sum;
    }
    printf("Primitive-character fiber cancellation verification\n\n");
    printf("  odd-prime cyclic and two-power product characters  %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  checked characters=%d and congruence fibers=%d\n",
           characters, fibers);
    printf("  maximum fiber-sum magnitude %.3Le                 %s\n",
           maximum_sum, maximum_sum <= 2.0e-12L ? "PASS" : "FAIL");
    printf("\n3/3 verification groups %s.\n",
           failures == 0 && maximum_sum <= 2.0e-12L
               ? "passed" : "did not pass");
    printf("Identity  conductor primitivity forces cancellation on every base\n");
    printf("and lower congruence fiber.\n");
    printf("Finite boundary  this verifier exhausts ten declared prime-power\n");
    printf("contexts, including noncyclic unit groups at powers of two.\n");
    return failures == 0 && maximum_sum <= 2.0e-12L;
}

void primitive_character_cancellation_help(void)
{
    printf(
        "Primitive-character fiber cancellation\n\n"
        "Commands\n"
        "  nfield primitive-character-cancellation inspect <base> <lag> <character-index>\n"
        "      Enumerate every base^j congruence fiber for one primitive odd\n"
        "      character and check its conductor witness and zero sum.\n"
        "  nfield primitive-character-cancellation verify\n"
        "  nfield verify primitive-character-cancellation\n\n"
        "Character indices\n"
        "  odd prime powers  chi_k(g^j)=exp(2*pi*i*k*j/phi); k odd and base does not divide k.\n"
        "  powers of two     chi(-1)=-1 and chi(5)=exp(2*pi*i*k/2^(e-2)); k odd.\n\n"
        "Scope\n"
        "  exact identity     base-fiber and every lower congruence-fiber cancellation.\n"
        "  exact computation residue membership, fiber sizes, and conductor witnesses.\n"
        "  numerical check   long-double roots of unity for each finite sum.\n"
    );
}
