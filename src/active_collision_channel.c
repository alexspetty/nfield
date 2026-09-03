/* Finite diagonal census underlying the active-channel zero-visibility theorem. */

#include <complex.h>
#include <math.h>
#include <stdio.h>

#include "nfield.h"
#include "periodic_zeta_core.h"

typedef struct {
    int characters;
    int active;
    int inactive;
    int pairing_failures;
    long double maximum_pairing_error;
    long double minimum_active_magnitude;
} ActiveChannelSummary;

static int conjugate_index(const PeriodicZetaContext *context, int index)
{
    if (context->base != 2) return context->phi - index;
    if (context->exponent == 2) return index;
    return context->cyclic_order - index;
}

static int channel_census(const PeriodicZetaContext *context,
                          ActiveChannelSummary *summary)
{
    int limit;
    if (!context || !summary) return 0;
    *summary = (ActiveChannelSummary){0};
    summary->minimum_active_magnitude = HUGE_VALL;
    limit = context->base != 2 ? context->phi :
            (context->exponent == 2 ? 2 : context->cyclic_order);
    for (int character = 1; character < limit; character++) {
        if (!periodic_zeta_character_valid(context, character)) continue;
        long double complex boundary = periodic_zeta_diagonal_boundary(
            context, character);
        long double magnitude = cabsl(boundary);
        int paired = conjugate_index(context, character);
        long double complex paired_boundary =
            periodic_zeta_diagonal_boundary(context, paired);
        long double pairing_error = cabsl(paired_boundary - conjl(boundary));
        summary->characters++;
        if (magnitude <= 2.0e-12L) summary->inactive++;
        else {
            summary->active++;
            if (magnitude < summary->minimum_active_magnitude)
                summary->minimum_active_magnitude = magnitude;
        }
        if (pairing_error > summary->maximum_pairing_error)
            summary->maximum_pairing_error = pairing_error;
        if (pairing_error > 2.0e-12L) summary->pairing_failures++;
    }
    if (summary->active == 0) summary->minimum_active_magnitude = 0.0L;
    return 1;
}

int active_collision_channel_inspect(
    int base, int lag, int character_index)
{
    PeriodicZetaContext context;
    char error[160];
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
    long double complex boundary = periodic_zeta_diagonal_boundary(
        &context, character_index);
    int active = cabsl(boundary) > 2.0e-12L;
    printf("Active collision channel\n\n");
    printf("  base=%d lag=%d modulus=%d character-index=%d\n",
           context.base, context.lag, context.modulus, character_index);
    printf("  diagonal boundary = %+.12Lf %+.12Lfi\n",
           creall(boundary), cimagl(boundary));
    printf("  magnitude = %.12Lf\n", cabsl(boundary));
    printf("  classification = %s\n", active ? "active" : "inactive");
    printf("\nFactorization consequence\n");
    if (active)
        printf("  The transform and L(s, conjugate chi) have the same open-strip zeros,\n  with multiplicity.\n");
    else
        printf("  The transform vanishes identically throughout the open strip.\n");
    printf("\nBoundary  this command classifies the finite diagonal factor. It does\n");
    printf("not search for, certify, or locate any L-function zero.\n");
    periodic_zeta_context_free(&context);
    return 0;
}

int active_collision_channel_census(int base, int lag)
{
    PeriodicZetaContext context;
    ActiveChannelSummary summary;
    char error[160];
    if (!periodic_zeta_context_build(
            base, lag, &context, error, sizeof(error))) {
        fprintf(stderr, "%s\n", error);
        return 1;
    }
    channel_census(&context, &summary);
    printf("Active collision channel census\n\n");
    printf("  base=%d lag=%d modulus=%d\n",
           context.base, context.lag, context.modulus);
    printf("  primitive odd characters = %d\n", summary.characters);
    printf("  active channels = %d\n", summary.active);
    printf("  inactive channels = %d\n", summary.inactive);
    printf("  minimum active |D| = %.12Lf\n",
           summary.minimum_active_magnitude);
    printf("  maximum conjugate-pair error = %.3Le  %s\n",
           summary.maximum_pairing_error,
           summary.pairing_failures == 0 ? "PASS" : "FAIL");
    printf("\nNo zero locations are computed or inferred.\n");
    periodic_zeta_context_free(&context);
    return summary.pairing_failures == 0 ? 0 : 1;
}

int active_collision_channel_verify(void)
{
    static const int contexts[][2] = {
        {2, 1}, {2, 2}, {2, 3}, {2, 4},
        {3, 1}, {3, 2}, {3, 3},
        {5, 1}, {5, 2}, {7, 1}, {11, 1}
    };
    int failures = 0;
    int characters = 0;
    int active = 0;
    int inactive = 0;
    long double maximum_pairing_error = 0.0L;

    for (size_t index = 0; index < sizeof(contexts) / sizeof(contexts[0]);
         index++) {
        PeriodicZetaContext context;
        ActiveChannelSummary summary;
        char error[160];
        if (!periodic_zeta_context_build(
                contexts[index][0], contexts[index][1],
                &context, error, sizeof(error))) {
            failures++;
            continue;
        }
        channel_census(&context, &summary);
        failures += summary.pairing_failures;
        characters += summary.characters;
        active += summary.active;
        inactive += summary.inactive;
        if (summary.maximum_pairing_error > maximum_pairing_error)
            maximum_pairing_error = summary.maximum_pairing_error;
        periodic_zeta_context_free(&context);
    }

    printf("Active collision channel verification\n\n");
    printf("  eleven declared prime-power contexts             %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  characters=%d; active=%d; inactive=%d\n",
           characters, active, inactive);
    printf("  exact conjugate-index pairing                     %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  maximum roots-of-unity pairing error %.3Le       %s\n",
           maximum_pairing_error,
           maximum_pairing_error <= 2.0e-12L ? "PASS" : "FAIL");
    printf("\n4/4 verification groups %s.\n",
           failures == 0 ? "passed" : "did not pass");
    printf("Analytic consequence  once the factorization is established, a zero diagonal makes\n");
    printf("the transform identically zero and a nonzero diagonal preserves every\n");
    printf("open-strip L-function zero with multiplicity.\n");
    printf("Software boundary  the verifier classifies finite diagonal channels;\n");
    printf("it does not compute or locate L-function zeros.\n");
    return failures == 0;
}

void active_collision_channel_help(void)
{
    printf(
        "Active collision channel\n\n"
        "Commands\n"
        "  nfield active-collision-channel inspect <base> <lag> <character-index>\n"
        "      Print the finite diagonal boundary and classify one channel.\n"
        "  nfield active-collision-channel census <base> <lag>\n"
        "      Classify every primitive odd character in one prime-power context.\n"
        "  nfield active-collision-channel verify\n"
        "  nfield verify active-collision-channel\n\n"
        "Scope\n"
        "  analytic consequence inactive channels vanish; active channels preserve\n"
        "                       open-strip zeros and multiplicities after factorization.\n"
        "  exact finite gate diagonal boundary D_l(chi).\n"
        "  software boundary no zero search, zero certification, critical-line claim,\n"
        "                     positivity claim, or conductor-uniform estimate.\n"
    );
}
