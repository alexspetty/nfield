#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "completion.h"

enum {
    COMMAND_HELP_TOPIC = 1,
    COMMAND_VERIFIER = 2,
    COMMAND_COMPATIBILITY = 4
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
    {"verify", NULL, "--time --help", COMMAND_HELP_TOPIC},
    {"daemon", NULL, "--port --threads --help", COMMAND_HELP_TOPIC},
    {"completion", "bash zsh fish", "--help", COMMAND_HELP_TOPIC},
    {"version", NULL, "--help", COMMAND_HELP_TOPIC},
    {"commands", NULL, "--help", 0},
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
     "--time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"additive-reflection-well", "inspect verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"reflected-prime-pair-sign", "sweep verify", "--max-even --time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"collision-spectrum-factorization", "inspect transform verify",
     "--time --help", COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"special-value-moment", "ledger verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
    {"base-five-cyclotomic-identity", "audit verify", "--time --help",
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
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
     COMMAND_HELP_TOPIC | COMMAND_VERIFIER},
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
        "--threads", "--transition", "--output", "-N"
    };
    const size_t count = sizeof(value_options) / sizeof(value_options[0]);
    for (size_t index = 0; index < count; index++)
        if (strcmp(option, value_options[index]) == 0) return 1;
    return 0;
}

int nfield_completion_candidates(int argc, char **argv)
{
    if (argc == 0) {
        for (size_t index = 0; index < command_spec_count; index++) {
            if ((command_specs[index].flags & COMMAND_COMPATIBILITY) == 0)
                puts(command_specs[index].name);
        }
        puts("--help");
        puts("--version");
        return 0;
    }

    const char *command = argv[0];
    if (strcmp(command, "--legacy") == 0) {
        if (argc == 1) print_commands_with_flag(COMMAND_COMPATIBILITY);
        return 0;
    }
    if (strcmp(command, "help") == 0) {
        if (argc == 1) {
            print_word_list(
                "explore commands legacy reading-map verification-map tables");
            print_commands_with_flag(COMMAND_HELP_TOPIC);
        }
        return 0;
    }
    if (strcmp(command, "verify") == 0) {
        if (argc == 1) {
            puts("all");
            print_commands_with_flag(COMMAND_VERIFIER);
            print_word_list(legacy_verifiers);
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
    if (argc == 1) print_word_list(spec->actions);
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
    printf(
        "nfield command catalog\n\n"
        "Field exploration\n"
        "  analyze  field  align  div  decompose  polar  survey  range\n"
        "  table  spectral  equations\n"
        "\n"
        "Digit structure and alignment\n"
        "  reciprocal-square-selection  weighted-reference-profile\n"
        "  digit-partition  alignment-limit  three-tier  deficit-lattice\n"
        "  coherence-decomposition  cross-alignment\n\n"
        "Spectra and collision structure\n"
        "  spectral-structure  spectral-power  autocorrelation  phase-gate\n"
        "  bin-derangements  collision-characters  silent-primes\n"
        "  collision-fluctuation  collision-centering  collision-table\n"
        "  collision-transform  centered-collision-table\n\n"
        "Residue and character channels\n"
        "  residue-three-neutrality  compatible-residue-channels\n"
        "  finite-character-pairing  coprime-base-orthogonality\n"
        "  natural-prime-sum-window  primitive-odd-sector\n"
        "  conjugate-pair-relabeling  additive-reflection-well\n"
        "  reflected-prime-pair-sign\n\n"
        "Transforms and analytic interfaces\n"
        "  collision-spectrum-factorization  special-value-moment\n"
        "  base-five-cyclotomic-identity  short-sum-bernoulli-correlation\n"
        "  primitive-character-cancellation  periodic-zeta-factorization\n"
        "  collision-boundary-recovery  active-collision-channel\n\n"
        "Finite geometry, boundaries, and energy\n"
        "  collision-coordinate  finite-determination  reflection-identity\n"
        "  half-group  all-prime-collision-label  finite-spectral-quotient\n"
        "  finite-prefix-slice  oriented-digit-comparison\n"
        "  boundary-bernoulli-factorization  boundary-conductor-ledger\n"
        "  terminal-collision-conductor-ledger  finite-state-orbit-boundary\n"
        "  full-orbit-energy  quadratic-orbit-energy\n"
        "  subgroup-jacobi-expansion  prime-base-collision-energy\n"
        "  arithmetic-boundary-defect  carry-completed-carrier\n"
        "  capacity-resolution  capacity-generation\n\n"
        "Clocks, sampling, and native energy\n"
        "  weighted-remainder-state  collision-sampling  boundary-spectrum\n"
        "  field-observation  native-refinement\n\n"
        "Operations\n"
        "  commands  verify  tables  daemon  completion  version  help\n\n"
        "Use `nfield help <tool>` for actions and scope.\n"
        "Use `nfield help legacy` for compatibility spellings.\n"
    );
}
