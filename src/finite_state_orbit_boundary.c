/* Exact finite-state lifts and dynamical boundaries of remainder orbits. */

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "nfield.h"
#include "orbit_boundary_core.h"

#define FSOB_MAX_BASE 64
#define FSOB_MAX_STATES 32
#define FSOB_MAX_ABS_WEIGHT 1000

static int fsob_parse_exact_list(
        const char *text, int *values, int expected,
        int minimum, int maximum)
{
    if (!text || !*text || !values || expected < 1) return 0;
    const char *cursor = text;
    for (int index = 0; index < expected; index++) {
        char *end = NULL;
        long value = strtol(cursor, &end, 10);
        if (end == cursor || value < minimum || value > maximum)
            return 0;
        values[index] = (int)value;
        if (index + 1 == expected) return *end == '\0';
        if (*end != ',') return 0;
        cursor = end + 1;
        if (*cursor == '\0') return 0;
    }
    return 0;
}

static int fsob_parse_accepting(
        const char *text, int state_count, int *accepted)
{
    if (!text || !*text || !accepted) return 0;
    const char *cursor = text;
    int count = 0;
    while (*cursor != '\0') {
        char *end = NULL;
        long state = strtol(cursor, &end, 10);
        if (end == cursor || state < 0 || state >= state_count ||
            accepted[state])
            return 0;
        accepted[state] = 1;
        count++;
        if (*end == '\0') break;
        if (*end != ',') return 0;
        cursor = end + 1;
        if (*cursor == '\0') return 0;
    }
    return count > 0;
}

int finite_state_orbit_boundary_compute(
        int base, int modulus, int state_count,
        int start_remainder, int start_state,
        const int *transition, int transition_count,
        const int *weights, int weight_count,
        FiniteStateOrbitBoundarySummary *summary)
{
    int carrier_size = 0;
    int *first_seen = NULL;
    int *path_remainder = NULL;
    int *path_state = NULL;
    int *path_digit = NULL;
    int *path_weight = NULL;
    int ok = 0;

    if (!summary || !transition || !weights ||
        base < 2 || base > FSOB_MAX_BASE || modulus < 2 ||
        state_count < 1 || state_count > FSOB_MAX_STATES ||
        modulus > NFIELD_FINITE_STATE_MAX_CYCLE ||
        modulus > NFIELD_FINITE_STATE_MAX_CYCLE / state_count ||
        orbit_boundary_gcd(base, modulus) != 1 ||
        start_remainder < 1 || start_remainder >= modulus ||
        orbit_boundary_gcd(start_remainder, modulus) != 1 ||
        start_state < 0 || start_state >= state_count ||
        transition_count != base * state_count ||
        weight_count != modulus * state_count)
        return 0;

    carrier_size = modulus * state_count;
    for (int index = 0; index < transition_count; index++)
        if (transition[index] < 0 || transition[index] >= state_count)
            return 0;
    for (int index = 0; index < weight_count; index++)
        if (weights[index] < -FSOB_MAX_ABS_WEIGHT ||
            weights[index] > FSOB_MAX_ABS_WEIGHT)
            return 0;

    *summary = (FiniteStateOrbitBoundarySummary){
        .base = base,
        .modulus = modulus,
        .state_count = state_count,
        .start_remainder = start_remainder,
        .start_state = start_state,
        .boolean_weight = 1
    };
    int unit_count = 0;
    for (int remainder = 1; remainder < modulus; remainder++)
        if (orbit_boundary_gcd(remainder, modulus) == 1)
            unit_count++;
    summary->state_space_size = unit_count * state_count;
    summary->remainder_period =
        orbit_boundary_multiplicative_order(base, modulus);
    if (summary->remainder_period < 1) return 0;

    first_seen = malloc((size_t)carrier_size * sizeof(*first_seen));
    path_remainder = malloc(
        NFIELD_FINITE_STATE_MAX_CYCLE * sizeof(*path_remainder));
    path_state = malloc(
        NFIELD_FINITE_STATE_MAX_CYCLE * sizeof(*path_state));
    path_digit = malloc(
        NFIELD_FINITE_STATE_MAX_CYCLE * sizeof(*path_digit));
    path_weight = malloc(
        NFIELD_FINITE_STATE_MAX_CYCLE * sizeof(*path_weight));
    if (!first_seen || !path_remainder || !path_state ||
        !path_digit || !path_weight)
        goto cleanup;
    for (int index = 0; index < carrier_size; index++) first_seen[index] = -1;

    int remainder = start_remainder;
    int state = start_state;
    int path_length = 0;
    while (1) {
        int carrier_index = remainder * state_count + state;
        if (first_seen[carrier_index] >= 0) {
            summary->transient_length = first_seen[carrier_index];
            summary->cycle_length =
                path_length - summary->transient_length;
            break;
        }
        if (path_length >= NFIELD_FINITE_STATE_MAX_CYCLE) goto cleanup;
        first_seen[carrier_index] = path_length;
        long long product = (long long)base * remainder;
        int digit = (int)(product / modulus);
        if (digit < 0 || digit >= base) goto cleanup;
        path_remainder[path_length] = remainder;
        path_state[path_length] = state;
        path_digit[path_length] = digit;
        path_weight[path_length] = weights[carrier_index];
        path_length++;
        remainder = (int)(product % modulus);
        state = transition[state * base + digit];
    }

    if (summary->cycle_length < 1 ||
        summary->cycle_length % summary->remainder_period != 0)
        goto cleanup;
    for (int index = 0; index < summary->cycle_length; index++) {
        int path_index = summary->transient_length + index;
        summary->cycle_remainder[index] = path_remainder[path_index];
        summary->cycle_state[index] = path_state[path_index];
        summary->cycle_digit[index] = path_digit[path_index];
        summary->cycle_weight[index] = path_weight[path_index];
        summary->cycle_weight_sum += path_weight[path_index];
        if (path_weight[path_index] != 0 && path_weight[path_index] != 1)
            summary->boolean_weight = 0;
    }
    for (int index = 0; index < summary->cycle_length; index++) {
        int predecessor = index == 0 ? summary->cycle_length - 1 : index - 1;
        long long boundary =
            (long long)summary->cycle_weight[predecessor] -
            summary->cycle_weight[index];
        if (boundary < INT_MIN || boundary > INT_MAX) goto cleanup;
        summary->dynamical_boundary[index] = (int)boundary;
        summary->boundary_sum += boundary;
        summary->boundary_squared_norm += boundary * boundary;
        if (boundary != 0) summary->boundary_nonzero++;
    }
    if (summary->boundary_sum != 0) goto cleanup;
    ok = 1;

cleanup:
    free(first_seen);
    free(path_remainder);
    free(path_state);
    free(path_digit);
    free(path_weight);
    return ok;
}

static void fsob_print_summary(
        const FiniteStateOrbitBoundarySummary *summary)
{
    printf("Finite-state remainder-orbit boundary\n\n");
    printf("  base=%d modulus=%d states=%d start=(%d,%d)\n",
           summary->base, summary->modulus, summary->state_count,
           summary->start_remainder, summary->start_state);
    printf("  unit-state carrier=%d; remainder period=%d\n",
           summary->state_space_size, summary->remainder_period);
    printf("  transient length=%d; eventual cycle length=%d\n\n",
           summary->transient_length, summary->cycle_length);
    printf("  k       R   state   digit   weight   predecessor-current\n");
    for (int index = 0; index < summary->cycle_length; index++)
        printf("  %-4d %5d %7d %7d %8d %21d\n",
               index, summary->cycle_remainder[index],
               summary->cycle_state[index], summary->cycle_digit[index],
               summary->cycle_weight[index],
               summary->dynamical_boundary[index]);
    printf("\n  Boolean cycle weight=%s; weight sum=%lld\n",
           summary->boolean_weight ? "yes" : "no",
           summary->cycle_weight_sum);
    printf("  nonzero dynamical-boundary cells=%d; squared norm=%lld\n",
           summary->boundary_nonzero, summary->boundary_squared_norm);
    printf("  dynamical-boundary sum=%lld  %s\n",
           summary->boundary_sum,
           summary->boundary_sum == 0 ? "PASS" : "FAIL");
    printf("\nSeparation  this predecessor boundary belongs to the lifted cycle.\n");
    printf("An additive residue boundary requires a separately specified weight\n");
    printf("on every residue class; none is inferred from the cycle alone.\n");
    printf("\nResult  PASS\n");
}

int finite_state_orbit_boundary_inspect(
        int base, int modulus, int state_count,
        int start_remainder, int start_state,
        const char *transition_text, const char *accepting_text,
        const char *state_weights_text)
{
    if (base < 2 || base > FSOB_MAX_BASE || modulus < 2 ||
        state_count < 1 || state_count > FSOB_MAX_STATES ||
        modulus > NFIELD_FINITE_STATE_MAX_CYCLE / state_count) {
        fprintf(stderr,
                "require 2<=base<=64, 1<=states<=32, and modulus*states<=4096\n");
        return 1;
    }
    if (!transition_text || (!accepting_text && !state_weights_text) ||
        (accepting_text && state_weights_text)) {
        fprintf(stderr,
                "provide --transition and exactly one of --accepting or --state-weights\n");
        return 1;
    }

    int transition_count = base * state_count;
    int weight_count = modulus * state_count;
    int *transition = calloc((size_t)transition_count, sizeof(*transition));
    int *state_weights = calloc((size_t)state_count, sizeof(*state_weights));
    int *weights = calloc((size_t)weight_count, sizeof(*weights));
    if (!transition || !state_weights || !weights) {
        free(transition);
        free(state_weights);
        free(weights);
        return 1;
    }
    int parsed = fsob_parse_exact_list(
        transition_text, transition, transition_count, 0, state_count - 1);
    if (parsed && accepting_text)
        parsed = fsob_parse_accepting(
            accepting_text, state_count, state_weights);
    if (parsed && state_weights_text)
        parsed = fsob_parse_exact_list(
            state_weights_text, state_weights, state_count,
            -FSOB_MAX_ABS_WEIGHT, FSOB_MAX_ABS_WEIGHT);
    if (!parsed) {
        fprintf(stderr,
                "transition needs states*base targets; accepting states or state weights need valid comma-separated entries\n");
        free(transition);
        free(state_weights);
        free(weights);
        return 1;
    }
    for (int remainder = 0; remainder < modulus; remainder++)
        for (int state = 0; state < state_count; state++)
            weights[remainder * state_count + state] = state_weights[state];

    FiniteStateOrbitBoundarySummary summary = {0};
    int ok = finite_state_orbit_boundary_compute(
        base, modulus, state_count, start_remainder, start_state,
        transition, transition_count, weights, weight_count, &summary);
    if (!ok) {
        fprintf(stderr,
                "require coprime base and modulus, a unit start remainder, and valid deterministic transitions\n");
    } else {
        fsob_print_summary(&summary);
    }
    free(transition);
    free(state_weights);
    free(weights);
    return ok ? 0 : 1;
}

int finite_state_orbit_boundary_parity(
        int base, int modulus, int start_remainder)
{
    int state_count = 2;
    if (base < 2 || base > FSOB_MAX_BASE || modulus < 2 ||
        modulus > NFIELD_FINITE_STATE_MAX_CYCLE / state_count) {
        fprintf(stderr,
                "require 2<=base<=64 and 2<=modulus<=2048\n");
        return 1;
    }
    int transition_count = base * state_count;
    int weight_count = modulus * state_count;
    int *transition = calloc((size_t)transition_count, sizeof(*transition));
    int *weights = calloc((size_t)weight_count, sizeof(*weights));
    if (!transition || !weights) {
        free(transition);
        free(weights);
        return 1;
    }
    for (int state = 0; state < state_count; state++)
        for (int digit = 0; digit < base; digit++)
            transition[state * base + digit] = (state + digit) % 2;
    for (int remainder = 0; remainder < modulus; remainder++)
        weights[remainder * state_count + 1] = 1;

    FiniteStateOrbitBoundarySummary summary = {0};
    int ok = finite_state_orbit_boundary_compute(
        base, modulus, state_count, start_remainder, 0,
        transition, transition_count, weights, weight_count, &summary);
    if (!ok) {
        fprintf(stderr,
                "require a modulus coprime to the base and a unit start remainder\n");
    } else {
        fsob_print_summary(&summary);
    }
    free(transition);
    free(weights);
    return ok ? 0 : 1;
}

int finite_state_orbit_boundary_verify(void)
{
    int parity_ok = 1;
    int transient_ok = 1;
    int weighted_ok = 1;
    int family_ok = 1;
    int domain_ok = 1;
    int models = 0;

    {
        int transition[4] = {0, 1, 1, 0};
        int weights[14] = {0};
        for (int remainder = 0; remainder < 7; remainder++)
            weights[2 * remainder + 1] = 1;
        FiniteStateOrbitBoundarySummary summary = {0};
        parity_ok = finite_state_orbit_boundary_compute(
            2, 7, 2, 1, 0, transition, 4, weights, 14, &summary) &&
            summary.remainder_period == 3 &&
            summary.transient_length == 0 && summary.cycle_length == 6 &&
            summary.boolean_weight && summary.cycle_weight_sum == 3 &&
            summary.boundary_nonzero == 2 &&
            summary.boundary_squared_norm == 2 &&
            summary.dynamical_boundary[0] == 1 &&
            summary.dynamical_boundary[3] == -1;
    }

    {
        int transition[4] = {0, 0, 0, 0};
        int weights[10] = {0};
        for (int remainder = 0; remainder < 5; remainder++)
            weights[2 * remainder + 1] = 1;
        FiniteStateOrbitBoundarySummary summary = {0};
        transient_ok = finite_state_orbit_boundary_compute(
            2, 5, 2, 1, 1, transition, 4, weights, 10, &summary) &&
            summary.remainder_period == 4 &&
            summary.transient_length == 1 && summary.cycle_length == 4 &&
            summary.cycle_weight_sum == 0 &&
            summary.boundary_nonzero == 0;
    }

    {
        int transition[4] = {0, 1, 1, 0};
        int weights[14] = {0};
        for (int remainder = 0; remainder < 7; remainder++)
            for (int state = 0; state < 2; state++)
                weights[2 * remainder + state] = remainder - 2 * state;
        FiniteStateOrbitBoundarySummary summary = {0};
        weighted_ok = finite_state_orbit_boundary_compute(
            2, 7, 2, 1, 0, transition, 4, weights, 14, &summary) &&
            !summary.boolean_weight && summary.boundary_sum == 0 &&
            summary.boundary_nonzero > 0 &&
            summary.boundary_squared_norm > 0;
    }

    for (int mask = 0; mask < 16; mask++) {
        int transition[4] = {
            mask & 1,
            (mask >> 1) & 1,
            (mask >> 2) & 1,
            (mask >> 3) & 1
        };
        for (int modulus = 3; modulus <= 21; modulus += 2) {
            int weights[42] = {0};
            for (int remainder = 0; remainder < modulus; remainder++)
                weights[2 * remainder + 1] = 1;
            for (int start = 1; start < modulus; start++) {
                if (orbit_boundary_gcd(start, modulus) != 1) continue;
                for (int state = 0; state < 2; state++) {
                    FiniteStateOrbitBoundarySummary summary = {0};
                    if (!finite_state_orbit_boundary_compute(
                            2, modulus, 2, start, state,
                            transition, 4, weights, 2 * modulus, &summary) ||
                        summary.cycle_length < 1 ||
                        summary.cycle_length % summary.remainder_period != 0 ||
                        summary.boundary_sum != 0)
                        family_ok = 0;
                    models++;
                }
            }
        }
    }

    {
        int transition[4] = {0, 1, 1, 0};
        int bad_transition[4] = {0, 1, 1, 2};
        int weights[14] = {0};
        FiniteStateOrbitBoundarySummary summary = {0};
        domain_ok =
            !finite_state_orbit_boundary_compute(
                2, 6, 2, 1, 0, transition, 4, weights, 12, &summary) &&
            !finite_state_orbit_boundary_compute(
                2, 7, 2, 0, 0, transition, 4, weights, 14, &summary) &&
            !finite_state_orbit_boundary_compute(
                2, 7, 2, 1, 0, transition, 3, weights, 14, &summary) &&
            !finite_state_orbit_boundary_compute(
                2, 7, 2, 1, 0, bad_transition, 4, weights, 14, &summary);
    }

    int passed = parity_ok + transient_ok + weighted_ok + family_ok + domain_ok;
    printf("Finite-state remainder-orbit boundary verification\n\n");
    printf("  parity lift doubles the three-step remainder cycle  %s\n",
           parity_ok ? "PASS" : "FAIL");
    printf("  merging automaton has one transient and cycle four  %s\n",
           transient_ok ? "PASS" : "FAIL");
    printf("  arbitrary integer weights telescope on the cycle   %s\n",
           weighted_ok ? "PASS" : "FAIL");
    printf("  deterministic two-state models=%d                  %s\n",
           models, family_ok ? "PASS" : "FAIL");
    printf("  coprimality, start, table, and target rejection     %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("\n%d/5 verification groups passed.\n", passed);
    printf("Exact  emitted digits, product-state iteration, cycle detection,\n");
    printf("predecessor differences, telescoping sum, and squared norm use\n");
    printf("integer arithmetic.\n");
    printf("Boundary  no additive residue weight or conductor energy is inferred\n");
    printf("from a lifted cycle. That weight remains separate input.\n");
    return passed == 5;
}

void finite_state_orbit_boundary_help(void)
{
    printf(
        "Finite-state remainder-orbit boundary\n\n"
        "Commands\n"
        "  nfield finite-state-orbit-boundary parity <base> <modulus> <start-R>\n"
        "      Track parity of the emitted digit sum from automaton state zero.\n"
        "  nfield finite-state-orbit-boundary inspect <base> <modulus> <states>\n"
        "      <start-R> <start-state> --transition <targets>\n"
        "      (--accepting <states> | --state-weights <weights>)\n"
        "  nfield finite-state-orbit-boundary verify\n"
        "  nfield verify finite-state-orbit-boundary\n\n"
        "Example\n"
        "  nfield finite-state-orbit-boundary inspect 2 7 2 1 0 \\\n"
        "      --transition 0,1,1,0 --accepting 1\n\n"
        "Scope\n"
        "  exact        d(R)=floor(base*R/modulus), the deterministic product\n"
        "               map, transient and cycle, and predecessor boundary.\n"
        "  weights      the CLI accepts Boolean state predicates or integer\n"
        "               state weights; the library accepts a weight on every\n"
        "               remainder-state pair.\n"
        "  separation   the cycle boundary is dynamical. An additive residue\n"
        "               boundary requires an independent full-residue weight.\n"
        "  boundary     coprime base and modulus, base<=64, states<=32, and\n"
        "               modulus*states<=4096.\n"
    );
}
