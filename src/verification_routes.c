#include <stdio.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#include "nfield.h"
#include "verification_routes.h"
#include "../verify/reset_forest_contracts.h"

typedef struct {
    const char *family;
    const char *action;
    const char *legacy_action;
    int (*run)(void);
    int boolean_success;
} VerificationAction;

/* Only fixed assertion/fixture panels belong here. A parameterized calculation
 * remains an ordinary operation even when it also reports a numerical residual. */
static const VerificationAction actions[] = {
    {"reset-forest", "contracts", "contracts", NULL, 0},
    {"cross-alignment", "examples", "examples", cross_alignment_examples, 0},
    {"spectral-structure", "examples", "examples", spectral_structure_examples, 0},
    {"spectral-power", "examples", "examples", spectral_power_examples, 0},
    {"autocorrelation", "examples", "examples", autocorrelation_examples, 0},
    {"phase-gate", "examples", "examples", phase_gate_examples, 0},
    {"bin-derangements", "examples", "examples", bin_derangements_examples, 0},
    {"collision-characters", "examples", "examples", collision_characters_examples, 0},
    {"silent-primes", "examples", "examples", silent_primes_examples, 0},
    {"collision-fluctuation", "examples", "examples", collision_fluctuation_examples, 0},
    {"collision-centering", "examples", "examples", centered_collision_examples, 0},
    {"collision-table", "examples", "examples", collision_periodic_examples, 0},
    {"collision-transform", "examples", "examples", collision_transform_examples, 0},
    {"residue-three-neutrality", "examples", "examples", residue_three_neutrality_examples, 0},
    {"collision-characters", "snapshot", "snapshot", collision_characters_snapshot, 0},
    {"silent-primes", "snapshot", "snapshot", silent_primes_snapshot, 0},
    {"collision-fluctuation", "snapshot", "snapshot", collision_fluctuation_snapshot, 0},
    {"collision-centering", "snapshot", "snapshot", centered_collision_snapshot, 0},
    {"collision-transform", "snapshot", "snapshot", collision_transform_snapshot, 0},
    {"residue-three-neutrality", "snapshot", "snapshot", residue_three_neutrality_snapshot, 0},
    {"compatible-residue-channels", "snapshot", "snapshot", compatible_residue_channels_snapshot, 0},
    {"finite-character-pairing", "cutoff-trend", "cutoff-trend", finite_character_pairing_cutoff_trend, 0},
    {"coprime-base-orthogonality", "audit", "audit", coprime_base_orthogonality_audit, 0},
    {"conjugate-pair-relabeling", "exact-law", "exact-law", conjugate_pair_relabeling_exact_law, 0},
    {"conjugate-pair-relabeling", "ledger", "ledger", conjugate_pair_relabeling_ledger, 0},
    {"conjugate-pair-relabeling", "cutoffs", "cutoffs", conjugate_pair_relabeling_cutoffs, 0},
    {"special-value-moment", "ledger", "ledger", special_value_moment_ledger, 0},
    {"base-five-cyclotomic-identity", "audit", "audit", base_five_cyclotomic_identity_audit, 0},
    {"short-sum-bernoulli-correlation", "ledger", "ledger", short_sum_bernoulli_correlation_ledger, 0},
    {"finite-spectral-quotient", "declared", "declared", finite_spectral_quotient_declared, 0},
    {"weighted-reference-profile", "torsion", "torsion", weighted_reference_profile_torsion, 1},
    {"weighted-reference-profile", "transport", "transport", weighted_reference_profile_transport, 1},
    {"terminal-collision-conductor-ledger", "audit", "audit", terminal_collision_conductor_ledger_audit, 0},
};

typedef struct {
    const char *family;
    const char *action;
    int (*run)(int, int);
    int positional;
} ParameterizedVerification;

/* These operations enumerate assertions for a requested model. The useful
 * table entries remain available through each family's inspect/table actions. */
static const ParameterizedVerification parameterized[] = {
    {"collision-centering", "gate", centered_collision_gate, 0},
    {"collision-transform", "gate", collision_transform_gate, 0},
    {"centered-collision-table", "complete", centered_collision_table_complete, 1}
};

static const char *canonical_family(const char *family)
{
    if (!strcmp(family, "centered-collision")) return "collision-centering";
    if (!strcmp(family, "collision-periodic-table")) return "collision-table";
    if (!strcmp(family, "neutrality-theorem")) return "residue-three-neutrality";
    if (!strcmp(family, "general-neutrality")) return "compatible-residue-channels";
    if (!strcmp(family, "goldbach-obstruction")) return "reflected-prime-pair-sign";
    return family;
}

int nfield_verify_action_is_fixed(const char *family, const char *action)
{
    family = canonical_family(family);
    for (size_t i = 0; i < sizeof(actions) / sizeof(actions[0]); ++i)
        if (!strcmp(family, actions[i].family) &&
            !strcmp(action, actions[i].legacy_action)) return 1;
    for (size_t i = 0; i < sizeof(parameterized) / sizeof(parameterized[0]); ++i)
        if (!strcmp(family, parameterized[i].family) &&
            !strcmp(action, parameterized[i].action)) return 1;
    return 0;
}

void nfield_verify_actions(const char *family)
{
    family = canonical_family(family);
    for (size_t i = 0; i < sizeof(actions) / sizeof(actions[0]); ++i)
        if (!strcmp(family, actions[i].family)) puts(actions[i].action);
    for (size_t i = 0; i < sizeof(parameterized) / sizeof(parameterized[0]); ++i)
        if (!strcmp(family, parameterized[i].family)) puts(parameterized[i].action);
}

const char *nfield_verify_action_name(const char *family, size_t index)
{
    family = canonical_family(family);
    for (size_t i = 0; i < sizeof(actions) / sizeof(actions[0]); ++i)
        if (!strcmp(family, actions[i].family) && index-- == 0)
            return actions[i].action;
    for (size_t i = 0; i < sizeof(parameterized) / sizeof(parameterized[0]); ++i)
        if (!strcmp(family, parameterized[i].family) && index-- == 0)
            return parameterized[i].action;
    return NULL;
}

const char *nfield_verify_action_legacy_name(const char *family, const char *action)
{
    family = canonical_family(family);
    for (size_t i = 0; i < sizeof(actions) / sizeof(actions[0]); ++i)
        if (!strcmp(family, actions[i].family) &&
            (!strcmp(action, actions[i].action) || !strcmp(action, actions[i].legacy_action)))
            return actions[i].legacy_action;
    for (size_t i = 0; i < sizeof(parameterized) / sizeof(parameterized[0]); ++i)
        if (!strcmp(family, parameterized[i].family) && !strcmp(action, parameterized[i].action))
            return parameterized[i].action;
    return NULL;
}

const char *nfield_verify_action_options(const char *family, const char *action)
{
    family = canonical_family(family);
    if (!strcmp(family, "reset-forest") && !strcmp(action, "contracts"))
        return "--json --time --help";
    for (size_t i = 0; i < sizeof(parameterized) / sizeof(parameterized[0]); ++i)
        if (!strcmp(family, parameterized[i].family) && !strcmp(action, parameterized[i].action))
            return parameterized[i].positional ? "--time --help" : "--base --lag --time --help";
    return nfield_verify_action_legacy_name(family, action) ? "--time --help" : NULL;
}

void nfield_verify_routes_help(const char *family)
{
    family = canonical_family(family);
    if (nfield_verify_action_name(family, 0) == NULL) return;
    puts("Implementation checks");
    for (size_t i = 0; ; ++i) {
        const char *action = nfield_verify_action_name(family, i);
        if (!action) break;
        const char *arguments = "";
        for (size_t j = 0; j < sizeof(parameterized) / sizeof(parameterized[0]); ++j)
            if (!strcmp(family, parameterized[j].family) &&
                !strcmp(action, parameterized[j].action))
                arguments = parameterized[j].positional ? " BASE LAG" : " [--base B] [--lag L]";
        printf("  nfield verify %s %s%s\n", family, action, arguments);
    }
    puts("  The older check spellings in the syntax reference remain compatibility routes.\n");
}

static int positive_integer(const char *text, int *out)
{
    if (!text || !*text) return 0;
    for (const char *p = text; *p; ++p)
        if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    long value = strtol(text, &end, 10);
    if (errno || *end || value < 1 || value > INT_MAX) return 0;
    *out = (int)value;
    return 1;
}

int nfield_verify_retired_request(int argc, char **argv)
{
    const char *mode = NULL;
    for (int i = 0; i < argc; ++i) {
        const char *arg = argv[i];
        if (!mode && arg[0] != '-') mode = arg;
        if (!strcmp(arg, "--source-root") || !strncmp(arg, "--source-root=", 14) ||
            !strcmp(arg, "--require-complete") || !strncmp(arg, "--require-complete=", 19)) {
            fprintf(stderr, "Verification option '%s' has been retired.\n"
                    "Use nfield verify families to choose a named C check.\n", arg);
            return 2;
        }
    }
    if (mode && (!strcmp(mode, "all") || !strcmp(mode, "coverage") ||
                 !strcmp(mode, "list") || !strcmp(mode, "theorem") || !strcmp(mode, "work"))) {
        fprintf(stderr, "Verification command '%s' has been removed.\n"
                "Use nfield verify families to choose a named C check.\n", mode);
        return 2;
    }
    return 0;
}

int nfield_verify_route(int argc, char **argv)
{
    if (argc >= 1 && !strcmp(argv[0], "families")) {
        if (argc != 1 && !(argc == 2 && !strcmp(argv[1], "--time"))) {
            fputs("Usage: nfield verify families [--time]\n", stderr);
            return 2;
        }
        verify_help();
        return 0;
    }
    if (argc < 2) return -1;
    const char *family = canonical_family(argv[0]);
    if (!strcmp(family, "reset-forest") && !strcmp(argv[1], "contracts")) {
        int json = 0, seen_time = 0;
        for (int i = 2; i < argc; ++i) {
            if (!strcmp(argv[i], "--json") && !json) json = 1;
            else if (!strcmp(argv[i], "--time") && !seen_time) seen_time = 1;
            else {
                fprintf(stderr, "Invalid verification argument: %s\n"
                        "Usage: nfield verify reset-forest contracts [--json] [--time]\n", argv[i]);
                return 2;
            }
        }
        return reset_forest_contracts_verify(json);
    }
    for (size_t i = 0; i < sizeof(parameterized) / sizeof(parameterized[0]); ++i) {
        const ParameterizedVerification *route = &parameterized[i];
        if (strcmp(family, route->family) || strcmp(argv[1], route->action)) continue;
        int base = 10, lag = 1, seen_base = 0, seen_lag = 0, seen_time = 0;
        int index = 2;
        if (route->positional) {
            if (argc < 4 || !positive_integer(argv[2], &base) ||
                !positive_integer(argv[3], &lag)) goto invalid_parameters;
            index = 4;
        }
        for (; index < argc; ++index) {
            if (!strcmp(argv[index], "--time") && !seen_time) seen_time = 1;
            else if (!route->positional && !strcmp(argv[index], "--base") &&
                     !seen_base && index + 1 < argc &&
                     positive_integer(argv[index + 1], &base)) { seen_base = 1; ++index; }
            else if (!route->positional && !strcmp(argv[index], "--lag") &&
                     !seen_lag && index + 1 < argc &&
                     positive_integer(argv[index + 1], &lag)) { seen_lag = 1; ++index; }
            else goto invalid_parameters;
        }
        return route->run(base, lag);
invalid_parameters:
        fprintf(stderr, "Usage: nfield verify %s %s%s [--time]\n", family, route->action,
                route->positional ? " BASE LAG" : " [--base B] [--lag L]");
        return 2;
    }
    for (size_t i = 0; i < sizeof(actions) / sizeof(actions[0]); ++i) {
        const VerificationAction *action = &actions[i];
        if (strcmp(family, action->family) ||
            (strcmp(argv[1], action->action) && strcmp(argv[1], action->legacy_action)))
            continue;
        if (argc != 2 && !(argc == 3 && !strcmp(argv[2], "--time"))) {
            fprintf(stderr, "Usage: nfield verify %s %s [--time]\n",
                    family, action->action);
            return 2;
        }
        if (action->run) {
            int result = action->run();
            return action->boolean_success ? (result ? 0 : 1) : result;
        }
        return 2;
    }
    return -1;
}
