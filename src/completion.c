#include <stddef.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>

#include "completion.h"
#include "command_guide.h"
#include "verification_routes.h"

enum {
    COMMAND_HELP_TOPIC = 1,
    COMMAND_VERIFIER = 2,
    COMMAND_COMPATIBILITY = 4,
    COMMAND_VERIFICATION_ONLY = 8
};

typedef struct {
    const char *name;
    const char *actions;
    const char *options;
    unsigned flags;
} CommandSpec;

/*
 * Command metadata for shell completion and the help-topic index.
 * Preferred names precede compatibility spellings so both current commands
 * and existing scripts remain discoverable.
 */
static const CommandSpec command_specs[] = {
    {"analyze", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"field", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"reset-forest", "source project", "--returns --divisor --modulus --mask --weights --grid --json --csv --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"native-refinement", "detector transport probe-transport packet copy-cost kernel mask-capture trace collision4 collision-families carry detail polarity stable-correction divisor-family divisor-work parent-credit verify", "--json --output --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"align", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"field-observation", "clocks pulses harmonics segments native-cycle tail-bound work native-boundary native-variation invariants register shells verify", "--matrix --from-prefixes --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"div", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"decompose", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"polar", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"survey", NULL, "--base --csv --time --help", COMMAND_HELP_TOPIC},
    {"range", NULL, "--base --csv --time --help", COMMAND_HELP_TOPIC},
    {"table", NULL, "--base --pairs --time --help", COMMAND_HELP_TOPIC},
    {"spectral", NULL, "--base --time --help", COMMAND_HELP_TOPIC},
    {"equations", NULL, "--time --help", COMMAND_HELP_TOPIC},
    {"tables", "reciprocal-square-selection", "--time --help", 0},
    {"verify", "families", "--time --help", COMMAND_HELP_TOPIC},
    {"daemon", NULL, "--port --threads --help", COMMAND_HELP_TOPIC},
    {"completion", "bash zsh fish", "--help", COMMAND_HELP_TOPIC},
    {"version", NULL, "--help", COMMAND_HELP_TOPIC},
    {"commands", NULL, "--json --examples --help", 0},
    {"help", NULL, NULL, 0},

    {"reciprocal-square-selection", "inspect cubic table scan verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"weighted-reference-profile",
     "inspect branch torsion reflection-product oriented-words transport finite-orbit verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"digit-partition", "inspect primes table verify",
     "--base --depth --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"alignment-limit", "inspect cosets table sharpness verify",
     "--base --depth --max-prime --steps --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"three-tier", "inspect classify scan verify",
     "--base --depth --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"deficit-lattice",
     "inspect ratio pythagorean major-scale chromatic-scale verify",
     "--base --factor --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"coherence-decomposition",
     "inspect prime-core pairs sigma-zero golden-gap verify",
     "--base --depth --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"cross-alignment", "matrix prime fourier block examples verify",
     "--base --depth --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"spectral-structure", "inspect two-coset character examples verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"spectral-power", "inspect overlap examples verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"autocorrelation", "inspect slice orbit harmonics examples verify",
     "--base --coset --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"phase-gate",
     "inspect multipliers bin-word density power-lag prime-sum examples verify",
     "--base --max-prime --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"bin-derangements", "inspect family mean lags examples verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-characters", "prime inspect snapshot examples verify",
     "--base --lag --sigma --tau --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"silent-primes", "recipe prime variance snapshot examples verify",
     "--base --lag --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-fluctuation", "prime table classes sum snapshot examples verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-centering", "inspect table fibers gate sum snapshot examples verify",
     "--base --lag --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-table", "inspect compare table summary examples verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-transform", "inspect table gate spectrum window snapshot examples verify",
     "--base --lag --sigma --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"residue-three-neutrality", "inspect canonical channels split snapshot examples verify",
     "--base --lag --sigma --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"compatible-residue-channels",
     "inspect internal channels simultaneous character-signs magnitude-correlations assignment-null snapshot verify",
     "--base --lag --cutoff --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"centered-collision-table", "inspect complete verify",
     "--time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"finite-character-pairing", "one declared-rows cutoff-trend verify",
     "--cutoff --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"coprime-base-orthogonality", "pair common-quotient audit verify",
     "--time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"natural-prime-sum-window", "base-boundaries common-tail verify",
     "--cutoff --lower --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"primitive-odd-sector", "inspect verify", "--cutoff --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"conjugate-pair-relabeling", "exact-law ledger cutoffs verify",
     "--time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER | COMMAND_VERIFICATION_ONLY},
    {"additive-reflection-well", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"reflected-prime-pair-sign", "sweep verify", "--max-even --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-spectrum-factorization", "inspect transform verify",
     "--time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"special-value-moment", "ledger verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER | COMMAND_VERIFICATION_ONLY},
    {"base-five-cyclotomic-identity", "audit verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER | COMMAND_VERIFICATION_ONLY},
    {"weighted-remainder-state", "inspect conductor boundary ramp floor straighten clock clock-law age-budget finite-weights variance rows increment-covariance increment-recurrence fourier amplitude-refinement expansion-constants harmonic-expansion amplitude-expansion deficit-series deficit-diagnostic spectral-product spectral-mean spectral-energy spectral-tail character-phase character-table character-l mixed-moment cotangent-sums harmonic-polylog harmonic-root harmonic-root-average sine-transform small-amplitudes alignment alignment-local harmonic-local alignment-lcm alignment-growth law-moment law-cdf law-window law-concentration law-characteristic law-recurrence law-tail-bound law-activation clock-difference mass-inverse mass-recovery perturbation cycle cycle-tv covariance amplitude tree tree-node weight budget mass sawtooth dedekind gram sawtooth-mean reset pairing forcing block crt moment haar-moment cylinder position position-weight conductor-full conductor-beta conductor-prime conductor-extrema conductor-minimizers activation verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"capacity-resolution", "constants inspect window sample unit spectrum progression verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"capacity-generation", "source carry measurement ledger refine control current seed profile lattice verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-sampling", "inspect sampled carrier poles collar prefix correlation state switching convolution capacity dedekind transform inverse grid source decomposition descent prefix-word prefix-population stopped-cost fold folded-source rectangle cubic dedekind-mass phase-sum completion kernel shells reciprocal interior verify", "--carriers --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"boundary-spectrum", "inspect channel verify", "--support --weights --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"short-sum-bernoulli-correlation", "ledger moments verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"primitive-character-cancellation", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"periodic-zeta-factorization", "inspect verify",
     "--sigma --tau --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-boundary-recovery", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"active-collision-channel", "inspect census verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-coordinate", "conjugation inspect gate verify",
     "--base --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"finite-determination", "inspect optimal verify",
     "--base --lag --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"reflection-identity", "inspect table verify",
     "--base --lag --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"half-group", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"all-prime-collision-label", "inspect verify",
     "--base --lag --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"finite-spectral-quotient", "inspect declared verify",
     "--lag --prime-count --tau --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"finite-prefix-slice", "inspect all collapse collision verify",
     "--base --depth --support --lag --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"oriented-digit-comparison", "inspect prime trichotomy verify",
     "--height --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"boundary-bernoulli-factorization",
     "inspect terminal spectrum correlation verify",
     "--support --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"boundary-conductor-ledger", "inspect terminal verify",
     "--support --time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"terminal-collision-conductor-ledger", "audit verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER | COMMAND_VERIFICATION_ONLY},
    {"finite-state-orbit-boundary", "parity inspect verify",
     "--transition --accepting --state-weights --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"full-orbit-energy", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"quadratic-orbit-energy", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"subgroup-jacobi-expansion", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"prime-base-collision-energy", "inspect poles verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"arithmetic-boundary-defect", "inspect scan verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"carry-completed-carrier", "inspect seam product verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},

    {"analytic", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"scale", NULL, "--chromatic --alpha --beta --csv --time",
     COMMAND_COMPATIBILITY},
    {"coherence", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"golden-threshold-table", NULL, "--time", COMMAND_COMPATIBILITY},
    {"collision_table", NULL, "--pairs --time", COMMAND_COMPATIBILITY},
    {"spectrum", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"gate", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"derangements", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"silent_primes", NULL, "--base --lag --time", COMMAND_COMPATIBILITY},
    {"gate_width", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"fluctuation_sum", NULL, "--base --lag --primes --time", COMMAND_COMPATIBILITY},
    {"mertens_growth", NULL, "--base --lag --primes --time", COMMAND_COMPATIBILITY},
    {"character_components", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"class_bias", NULL, "--base --primes --time", COMMAND_COMPATIBILITY},
    {"class_means", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"centered_sum", NULL, "--base --primes --time", COMMAND_COMPATIBILITY},
    {"neutrality", NULL, "--base --primes --time", COMMAND_COMPATIBILITY},
    {"neutrality_sweep", NULL, "--time", COMMAND_COMPATIBILITY},
    {"finite_det", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"mod3_means", NULL, "--time", COMMAND_COMPATIBILITY},
    {"polarity_field", NULL, "--base --time", COMMAND_COMPATIBILITY},
    {"centered-collision", "inspect table fibers gate sum snapshot examples verify",
     "--base --lag --time --help", COMMAND_COMPATIBILITY},
    {"collision-periodic-table", "inspect compare table summary examples verify",
     "--base --time --help", COMMAND_COMPATIBILITY},
    {"neutrality-theorem", "inspect canonical channels split snapshot examples verify",
     "--base --lag --sigma --time --help", COMMAND_COMPATIBILITY},
    {"general-neutrality",
     "inspect internal channels simultaneous character-signs magnitude-correlations assignment-null snapshot verify",
     "--base --lag --cutoff --time --help", COMMAND_COMPATIBILITY},
    {"goldbach-obstruction", "sweep verify", "--max-even --time --help",
     COMMAND_COMPATIBILITY}
};

static const size_t command_spec_count =
    sizeof(command_specs) / sizeof(command_specs[0]);

static const char *legacy_verifiers =
    "gate-width mobius-family sum-rule mean-formula finite-det antisymmetry "
    "mean-half palindrome full-range middle-balance inversion "
    "centered-antisym even-killed decomposition general-lag-det";

static void print_word_list(const char *words)
{
    if (words == NULL) return;
    const char *cursor = words;
    while (*cursor != '\0') {
        while (*cursor == ' ') cursor++;
        if (*cursor == '\0') break;
        const char *start = cursor;
        while (*cursor != '\0' && *cursor != ' ') cursor++;
        (void)fwrite(start, 1, (size_t)(cursor - start), stdout);
        putchar('\n');
    }
}

static void print_utility_actions(const CommandSpec *spec)
{
    const char *cursor = spec->actions;
    if (cursor == NULL) return;
    while (*cursor != '\0') {
        char action[128];
        while (*cursor == ' ') ++cursor;
        const char *start = cursor;
        while (*cursor != '\0' && *cursor != ' ') ++cursor;
        size_t length = (size_t)(cursor - start);
        if (length == 0) break;
        if (length >= sizeof(action)) continue;
        memcpy(action, start, length);
        action[length] = '\0';
        if (strcmp(action, "verify") &&
            !nfield_verify_action_is_fixed(spec->name, action)) puts(action);
    }
}

void nfield_command_names(int include_compatibility)
{
    for (size_t i = 0; i < command_spec_count; ++i)
        if (include_compatibility ||
            !(command_specs[i].flags & (COMMAND_COMPATIBILITY | COMMAND_VERIFICATION_ONLY)))
            puts(command_specs[i].name);
}

static void json_string(const char *value)
{
    const unsigned char *p = (const unsigned char *)(value ? value : "");
    putchar('"');
    for (; *p; ++p) {
        if (*p == '"' || *p == '\\') { putchar('\\'); putchar(*p); }
        else if (*p < 32) printf("\\u%04x", (unsigned)*p);
        else putchar(*p);
    }
    putchar('"');
}

static void json_words(const CommandSpec *spec, const char *words, int utility)
{
    int first = 1;
    const char *cursor = words ? words : "";
    putchar('[');
    while (*cursor) {
        char word[128];
        while (*cursor == ' ') ++cursor;
        const char *start = cursor;
        while (*cursor && *cursor != ' ') ++cursor;
        size_t length = (size_t)(cursor - start);
        if (!length) break;
        if (length >= sizeof(word)) continue;
        memcpy(word, start, length);
        word[length] = '\0';
        if (utility && (!strcmp(word, "verify") ||
                        nfield_verify_action_is_fixed(spec->name, word))) continue;
        if (!first) putchar(',');
        json_string(word);
        first = 0;
    }
    putchar(']');
}

static void json_action(const NfieldActionGuide *action, const char *name)
{
    if (!action) { fputs("null", stdout); return; }
    printf("{\"name\":"); json_string(name ? name : action->name);
    printf(",\"kind\":"); json_string(action->kind);
    printf(",\"purpose\":"); json_string(action->purpose);
    printf(",\"syntax\":"); json_string(action->syntax);
    printf(",\"inputs\":"); json_string(action->inputs);
    printf(",\"outputs\":"); json_string(action->outputs);
    printf(",\"example\":"); json_string(action->example);
    printf(",\"limits\":"); json_string(action->limits);
    printf(",\"formatOptions\":[");
    int separator = 0;
    const char *formats[] = {"--json", "--csv"};
    for (size_t i = 0; i < 2; ++i)
        if (nfield_command_format_supported(action->family, action->name, formats[i])) {
            if (separator++) putchar(',');
            json_string(formats[i]);
        }
    putchar(']');
    putchar('}');
}

static void json_action_details(const CommandSpec *spec)
{
    int first = 1;
    const char *cursor = spec->actions ? spec->actions : "";
    putchar('[');
    while (*cursor) {
        char word[128];
        while (*cursor == ' ') ++cursor;
        const char *start = cursor;
        while (*cursor && *cursor != ' ') ++cursor;
        size_t length = (size_t)(cursor - start);
        if (!length) break;
        if (length >= sizeof(word)) continue;
        memcpy(word, start, length); word[length] = '\0';
        if ((spec->flags & COMMAND_VERIFICATION_ONLY) || !strcmp(word, "verify") ||
            nfield_verify_action_is_fixed(spec->name, word)) continue;
        if (!first) putchar(',');
        json_action(nfield_action_guide_lookup(spec->name, word), word);
        first = 0;
    }
    putchar(']');
}

static int contains_casefold(const char *text, const char *query)
{
    if (!text || !query) return 0;
    if (!*query) return 1;
    for (; *text; ++text) {
        size_t n = 0;
        while (text[n] && query[n] &&
               tolower((unsigned char)text[n]) == tolower((unsigned char)query[n])) ++n;
        if (!query[n]) return 1;
    }
    return 0;
}

static int action_matches(const NfieldActionGuide *action, int argc, char **argv)
{
    if (!action) return 0;
    for (int i = 0; i < argc; ++i) {
        if (argv[i][0] == '-') continue;
        if (!contains_casefold(action->family, argv[i]) &&
            !contains_casefold(action->name, argv[i]) &&
            !contains_casefold(action->purpose, argv[i]) &&
            !contains_casefold(action->inputs, argv[i]) &&
            !contains_casefold(action->outputs, argv[i])) return 0;
    }
    return 1;
}

static int command_matches(const CommandSpec *spec, int argc, char **argv)
{
    const NfieldCommandGuide *guide = nfield_command_guide_lookup(spec->name);
    if (!guide) return 0;
    for (int i = 0; i < argc; ++i) {
        if (argv[i][0] == '-') continue;
        int found = contains_casefold(spec->name, argv[i]) ||
                    contains_casefold(guide->purpose, argv[i]) ||
                    contains_casefold(guide->inputs, argv[i]) ||
                    contains_casefold(guide->outputs, argv[i]);
        for (size_t a = 0; !found; ++a) {
            const NfieldActionGuide *action = nfield_action_guide_at(spec->name, a);
            if (!action) break;
            found = contains_casefold(action->name, argv[i]) ||
                    contains_casefold(action->purpose, argv[i]) ||
                    contains_casefold(action->inputs, argv[i]) ||
                    contains_casefold(action->outputs, argv[i]);
        }
        if (!found) return 0;
    }
    return 1;
}

static int selected_command(const CommandSpec *spec, int argc, char **argv, int terms)
{
    if (!terms) return 1;
    const char *canonical = nfield_command_canonical_name(spec->name);
    if (canonical && strcmp(canonical, spec->name)) {
        int named = 0;
        for (int i = 0; i < argc; ++i)
            if (argv[i][0] != '-' && contains_casefold(spec->name, argv[i])) named = 1;
        if (!named) return 0;
    }
    return command_matches(spec, argc, argv);
}

static void commands_json_filtered(int argc, char **argv, int terms)
{
    puts("{\"schema\":\"nfield.commands.v1\",\"commands\":[");
    int emitted = 0;
    for (size_t i = 0; i < command_spec_count; ++i) {
        const CommandSpec *spec = &command_specs[i];
        if (!selected_command(spec, argc, argv, terms)) continue;
        const NfieldCommandGuide *guide = nfield_command_guide_lookup(spec->name);
        const char *kind = (spec->flags & COMMAND_COMPATIBILITY) ? "compatibility" :
            (spec->flags & COMMAND_VERIFICATION_ONLY) || !strcmp(spec->name, "verify") ? "verification" :
            guide && (!strcmp(guide->kind, "service") || !strcmp(guide->kind, "navigation")) ? "service" :
            guide ? "utility" : "unknown";
        if (emitted++) puts(",");
        printf("{\"name\":"); json_string(spec->name);
        printf(",\"canonical\":"); json_string(nfield_command_canonical_name(spec->name));
        printf(",\"kind\":"); json_string(kind);
        printf(",\"purpose\":"); json_string(guide ? guide->purpose : "");
        printf(",\"inputs\":"); json_string(guide ? guide->inputs : "");
        printf(",\"outputs\":"); json_string(guide ? guide->outputs : "");
        printf(",\"example\":"); json_string(guide ? guide->example : "");
        printf(",\"workflow\":"); json_string(guide ? guide->workflow : "");
        printf(",\"limits\":"); json_string(guide ? guide->limits : "");
        printf(",\"actions\":");
        json_words(spec, (spec->flags & COMMAND_VERIFICATION_ONLY) ? NULL : spec->actions, 1);
        printf(",\"options\":"); json_words(spec, spec->options, 0);
        printf(",\"hasFamilyVerifier\":%s,\"verificationActions\":[",
               spec->flags & COMMAND_VERIFIER ? "true" : "false");
        for (size_t a = 0; ; ++a) {
            const char *name = nfield_verify_action_name(spec->name, a);
            if (!name) break;
            if (a) putchar(',');
            json_string(name);
        }
        printf("],\"defaultAction\":");
        json_action(nfield_action_guide_lookup(spec->name, "(default)"), NULL);
        printf(",\"actionDetails\":"); json_action_details(spec);
        printf(",\"verificationDetails\":[");
        for (size_t a = 0; ; ++a) {
            const char *name = nfield_verify_action_name(spec->name, a);
            if (!name) break;
            if (a) putchar(',');
            json_action(nfield_verify_action_guide_lookup(spec->name, name), name);
        }
        printf("]}");
    }
    puts("\n]}");
}

void nfield_commands_json(void)
{
    commands_json_filtered(0, NULL, 0);
}

int nfield_commands_command(int argc, char **argv)
{
    int json = 0, examples = 0, terms = 0;
    for (int i = 0; i < argc; ++i) {
        if (!strcmp(argv[i], "--json") && !json) json = 1;
        else if (!strcmp(argv[i], "--examples") && !examples) examples = 1;
        else if (argv[i][0] == '-') {
            fprintf(stderr, "Usage: nfield commands [terms ...] [--examples] [--json]\n");
            return 1;
        } else if (*argv[i]) ++terms;
    }
    if (json) { commands_json_filtered(argc, argv, terms); return 0; }
    if (!terms && !examples) { nfield_commands_help(); return 0; }
    size_t matches = 0;
    for (size_t i = 0; i < command_spec_count; ++i) {
        const CommandSpec *spec = &command_specs[i];
        const NfieldCommandGuide *guide = nfield_command_guide_lookup(spec->name);
        const char *canonical = nfield_command_canonical_name(spec->name);
        if (!guide || !selected_command(spec, argc, argv, terms)) continue;
        if (!terms && ((canonical && strcmp(canonical, spec->name)) ||
                       !strcmp(guide->kind, "verification"))) continue;
        printf("%s%s\n  %s\n", spec->name,
               !strcmp(guide->kind, "verification") ? " (implementation checks)" : "",
               guide->purpose);
        if (examples) {
            size_t shown = 0, total = 0;
            for (size_t a = 0; terms; ++a) {
                const NfieldActionGuide *action = nfield_action_guide_at(spec->name, a);
                if (!action) break;
                if (!action_matches(action, argc, argv) ||
                    !strcmp(action->kind, "verification") ||
                    !action->example || !*action->example) continue;
                if (shown < 3) { printf("  %s\n", action->example); ++shown; }
                ++total;
            }
            if (!shown && guide->example && *guide->example) printf("  %s\n", guide->example);
            if (total > shown) printf("  More matching actions: nfield help %s\n", spec->name);
        }
        putchar('\n');
        ++matches;
    }
    if (!matches) puts("No matching commands. Try a shorter term, such as digits, spectrum or covariance.");
    else puts("Use nfield help <command> <action> for inputs, outputs and limits.");
    return 0;
}

static const CommandSpec *find_command_spec(const char *name)
{
    for (size_t index = 0; index < command_spec_count; index++)
        if (strcmp(command_specs[index].name, name) == 0)
            return &command_specs[index];
    return NULL;
}

static void print_commands_with_flag(unsigned flag)
{
    for (size_t index = 0; index < command_spec_count; index++)
        if ((command_specs[index].flags & flag) != 0)
            puts(command_specs[index].name);
}

static int option_takes_value(const char *option)
{
    static const char *value_options[] = {
        "--accepting", "--alpha", "--base", "--beta", "--coset",
        "--cutoff", "--block-length", "--depth", "--factor", "--height", "--lag", "--lower",
        "--max-even", "--max-prime", "--port", "--prime-count", "--primes", "--radial",
        "--sigma", "--state-weights", "--steps", "--support", "--tau",
        "--threads", "--transition", "--output", "--divisor", "--returns",
        "--modulus", "--mask", "--weights", "--grid", "-N"
    };
    const size_t count = sizeof(value_options) / sizeof(value_options[0]);
    for (size_t index = 0; index < count; index++)
        if (strcmp(option, value_options[index]) == 0) return 1;
    return 0;
}

int nfield_completion_candidates(int argc, char **argv)
{
    if (argc == 0) {
        nfield_command_names(0);
        puts("--help");
        puts("--version");
        return 0;
    }

    const char *command = argv[0];
    if (strcmp(command, "--legacy") == 0) {
        if (argc == 1) print_commands_with_flag(COMMAND_COMPATIBILITY | COMMAND_VERIFICATION_ONLY);
        return 0;
    }
    if (strcmp(command, "help") == 0) {
        if (argc == 1) {
            print_word_list(
                "explore commands legacy reading-map verification-map tables");
            print_commands_with_flag(COMMAND_HELP_TOPIC);
        } else if (argc == 2) {
            const CommandSpec *spec = find_command_spec(argv[1]);
            if (spec) print_utility_actions(spec);
        }
        return 0;
    }
    if (strcmp(command, "verify") == 0) {
        if (argc == 1) {
            puts("families");
            print_commands_with_flag(COMMAND_VERIFIER);
            print_word_list(legacy_verifiers);
        } else if (option_takes_value(argv[argc - 1])) {
            return 0;
        } else if (argc == 2 && !strcmp(argv[1], "families")) {
            puts("--time");
        } else if (argc == 2) {
            nfield_verify_actions(argv[1]);
        } else if (argc >= 3) {
            print_word_list(nfield_verify_action_options(argv[1], argv[2]));
        }
        return 0;
    }
    if (strcmp(command, "completion") == 0) {
        if (argc == 1) print_word_list("bash zsh fish");
        return 0;
    }

    const CommandSpec *spec = find_command_spec(command);
    if (spec == NULL) return 0;
    if (argc > 1 && option_takes_value(argv[argc - 1])) return 0;
    if (argc == 1) print_utility_actions(spec);
    print_word_list(spec->options);
    return 0;
}

static void emit_bash_completion(void)
{
    puts("# bash completion for nfield");
    puts("_nfield_complete()");
    puts("{");
    puts("    local current candidate");
    puts("    local -a prior");
    puts("    current=\"${COMP_WORDS[COMP_CWORD]}\"");
    puts("    prior=(\"${COMP_WORDS[@]:1:$((COMP_CWORD - 1))}\")");
    puts("    COMPREPLY=()");
    puts("    while IFS= read -r candidate; do");
    puts("        [[ $candidate == \"$current\"* ]] && COMPREPLY+=(\"$candidate\")");
    puts("    done < <(\"${COMP_WORDS[0]}\" __complete \"${prior[@]}\" 2>/dev/null)");
    puts("    return 0");
    puts("}");
    puts("complete -o bashdefault -o default -F _nfield_complete nfield");
}

static void emit_zsh_completion(void)
{
    puts("#compdef nfield");
    puts("_nfield_complete()");
    puts("{");
    puts("    local -a prior");
    puts("    local output");
    puts("    if (( CURRENT > 2 )); then");
    puts("        prior=(\"${words[2,$((CURRENT - 1))]}\")");
    puts("    fi");
    puts("    output=$(\"${words[1]}\" __complete \"${prior[@]}\" 2>/dev/null)");
    puts("    [[ -n $output ]] && compadd -- ${(f)output}");
    puts("    return 0");
    puts("}");
    puts("compdef _nfield_complete nfield");
}

static void emit_fish_completion(void)
{
    puts("function __nfield_complete");
    puts("    set -l tokens (commandline -opc)");
    puts("    set -l executable $tokens[1]");
    puts("    set -e tokens[1]");
    puts("    $executable __complete $tokens 2>/dev/null");
    puts("end");
    puts("complete -c nfield -f -a '(__nfield_complete)'");
}

void nfield_completion_help(void)
{
    printf(
        "nfield shell completion\n\n"
        "Enable Tab completion in the current shell:\n"
        "  Bash  source <(nfield completion bash)\n"
        "  Zsh   source <(nfield completion zsh)\n"
        "  Fish  nfield completion fish | source\n\n"
        "Then type, for example, `nfield fi` and press Tab to complete or list\n"
        "matching commands. Save the generated script in your shell's completion\n"
        "directory to enable it permanently. Candidates come from the current\n"
        "nfield executable, including actions, help topics, verifiers, and options.\n"
    );
}

int nfield_completion_command(int argc, char **argv)
{
    if (argc == 0 || strcmp(argv[0], "help") == 0 ||
        strcmp(argv[0], "--help") == 0 || strcmp(argv[0], "-h") == 0) {
        nfield_completion_help();
        return 0;
    }
    if (argc != 1) {
        fprintf(stderr, "Usage: nfield completion <bash|zsh|fish>\n");
        return 1;
    }
    if (strcmp(argv[0], "bash") == 0) emit_bash_completion();
    else if (strcmp(argv[0], "zsh") == 0) emit_zsh_completion();
    else if (strcmp(argv[0], "fish") == 0) emit_fish_completion();
    else {
        fprintf(stderr, "Unsupported shell: %s\n", argv[0]);
        fprintf(stderr, "Choose bash, zsh, or fish.\n");
        return 1;
    }
    return 0;
}

void nfield_commands_help(void)
{
    puts("nfield command catalog\n");
    puts("Research operations and services");
    for (size_t i = 0; i < command_spec_count; ++i) {
        const CommandSpec *spec = &command_specs[i];
        if (spec->flags & (COMMAND_COMPATIBILITY | COMMAND_VERIFICATION_ONLY)) continue;
        if (!strcmp(spec->name, "verify")) continue;
        const char *purpose = nfield_command_purpose(spec->name);
        printf("  %s\n", spec->name);
        if (purpose && *purpose) printf("    %s\n", purpose);
    }
    puts("\nVerification");
    puts("  verify <family> [check]    Run an implementation check or fixed fixture.");
    puts("  verify families            List named C checks without running them.");
    puts("  verify reset-forest contracts [--json]  Run finite source and forest checks.");
    puts("\nFixed verification families");
    for (size_t i = 0; i < command_spec_count; ++i)
        if (command_specs[i].flags & COMMAND_VERIFICATION_ONLY)
            printf("  nfield verify %s\n", command_specs[i].name);
    puts("\nUse nfield help <command> for the research purpose, inputs, results and examples.");
    puts("Use nfield help <command> <action> for one operation's inputs and returned quantities.");
    puts("Legacy spellings remain executable; use nfield help legacy to find them.");
}
