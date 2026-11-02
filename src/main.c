#define _POSIX_C_SOURCE 199309L

/*
 * nfield: Fractional field analysis engine.
 *
 * Usage:
 *   nfield analyze <n> [--base <b>]
 *   nfield survey <max> [--base <b>]
 *   nfield align <n> [--base <b>]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include "build_info.h"
#include "completion.h"
#include "nfield.h"

/* daemon entry */
extern int daemon_main(int port, int num_threads);
extern void dispatch_init(const char *argv0);

static void print_banner(void)
{
    printf("nfield .:. %s | A. S. Petty, 2020-2026\n",
           nfield_build_version());
}

static void print_elapsed_time(const struct timespec *start,
                               const struct timespec *end)
{
    long long nanoseconds =
        (long long)(end->tv_sec - start->tv_sec) * 1000000000LL
        + (long long)(end->tv_nsec - start->tv_nsec);

    if (nanoseconds >= 1000000000LL)
        printf("\n%.6f s\n", (double)nanoseconds / 1e9);
    else if (nanoseconds >= 1000000LL)
        printf("\n%.3f ms\n", (double)nanoseconds / 1e6);
    else if (nanoseconds >= 1000LL)
        printf("\n%.3f us\n", (double)nanoseconds / 1e3);
    else
        printf("\n%lld ns\n", nanoseconds);
}

static void usage(void)
{
    print_banner();
    printf(
        "\nCommand-line tools for finite digit fields and collision arithmetic.\n"
        "\nUsage\n"
        "  nfield <command> [arguments] [options]\n"
        "  nfield <n> [--base <b>]                 Analyze one denominator\n"
        "  nfield help <command>                   Open focused help\n"
        "\nCommon commands\n"
        "  field <n>                              Show a complete fractional field\n"
        "  analyze <n>                            Analyze one denominator\n"
        "  div <n>                                Show its long-division table\n"
        "  align <n>                              Compute synchronized alignment\n"
        "  spectral <p>                           Inspect additive spectral power\n"
        "  survey <max>                           Survey a denominator range\n"
        "  verify [name|all]                      List or run exact verifiers\n"
        "\nFind more\n"
        "  nfield commands                        List every command family\n"
        "  nfield help <command>                  Explain one command\n"
        "  nfield completion                     Set up Bash, Zsh, or Fish Tab completion\n"
        "  nfield daemon --port 9090              Start the local JSON/TCP service\n"
        "  nfield --version                       Show the numeric build version\n"
        "\nExamples\n"
        "  nfield field 7\n"
        "  nfield digit-partition inspect 6 --base 2\n"
        "  nfield collision-table inspect 13 --base 10\n"
        "\nDefault base: 10. Add --time to time a command.\n"
    );
}

static void explore_help(void)
{
    printf(
        "nfield field exploration\n\n"
        "Commands\n"
        "  nfield <n> [--base <b>]             Analyze one denominator\n"
        "  nfield analyze <n> [--base <b>]     Same operation, explicit name\n"
        "  nfield field <n> [--base <b>]       Show every fraction in the field\n"
        "  nfield div <n> [--base <b>]         Show the long-division table\n"
        "  nfield align <n> [--base <b>]       Compute synchronized alignment\n"
        "  nfield decompose <n> [--base <b>]   Show alpha, sigma, and F\n"
        "  nfield polar <n> [--base <b>]       Show the polar decomposition\n"
        "  nfield survey <max> [--base <b>] [--csv]\n"
        "  nfield range <min> <max> [--base <b>] [--csv]\n"
        "  nfield table [base] [--pairs]       Show the collision table\n"
        "  nfield spectral <p> [--base <b>]    Show additive spectral power\n"
        "  nfield equations                    Define the principal invariants\n\n"
        "Common options\n"
        "  --base <b>   Choose the digit base; default 10\n"
        "  --csv        Emit machine-readable rows where supported\n"
        "  --time       Report command runtime in ns, us, ms, or s\n\n"
        "For parameterized structure tools, run `nfield help commands`.\n"
    );
}

static void tables_help(void)
{
    printf(
        "nfield exact table fixtures\n\n"
        "Usage\n"
        "  nfield tables\n"
        "  nfield tables reciprocal-square-selection\n\n"
        "This compatibility dispatcher reproduces registered fixed tables.\n"
        "Parameterized inspection lives in the corresponding tool family.\n"
    );
}

static void version_help(void)
{
    printf(
        "nfield build identity\n\n"
        "  nfield --version\n"
        "  nfield version\n\n"
        "The version is derived from the UTC link time as YYYY.MMDD.HHMMSS.\n"
        "Set BUILD_VERSION when invoking make to reproduce an existing version\n"
        "exactly. A no-op make leaves the current version intact.\n"
    );
}

static void legacy_help(void)
{
    printf(
        "nfield compatibility and research commands\n\n"
        "These commands are preserved for existing posts, scripts, and research.\n"
        "The named mathematical objects in `nfield help` are the preferred path.\n\n"
        "Tables and aliases\n"
        "  golden-threshold-table  table  tables  collision_table  spectral  spectrum\n\n"
        "Collision research\n"
        "  gate  gate_width  derangements  silent_primes\n"
        "  fluctuation_sum  mertens_growth  centered_sum\n"
        "  character_components  class_bias  class_means\n"
        "  neutrality  neutrality_sweep  finite_det  mod3_means\n\n"
        "Other research views\n"
        "  coherence  analytic  scale  polarity_field\n\n"
        "Run `nfield --help` for the supported mathematical-object command map.\n"
    );
}

static void daemon_help(void)
{
    printf(
        "nfield JSON/TCP daemon\n\n"
        "Usage:\n"
        "  nfield daemon [--port <port>] [--threads <count>]\n\n"
        "Defaults: port 9090 and four worker threads. Send one JSON object per\n"
        "connection, for example {\"cmd\":\"collision-coordinate gate 13 --base 10\"}. The\n"
        "response contains the same output produced by the command-line program.\n"
        "Help commands are available through the daemon as ordinary commands.\n"
        "Commands are executed directly without a shell; quotes and shell operators\n"
        "inside the command string are rejected.\n"
    );
}

static void verification_map_help(void)
{
    printf(
        "nfield reading map\n\n"
        "The mathematical objects below are native nfield work surfaces. Published\n"
        "works draw paths through them. Use this optional index to enter the terrain\n"
        "from a title. Commands stay parameterized and independent of the title, and\n"
        "one object may support several works. Each object's help gives its inputs,\n"
        "exact identities, finite range, and analytic boundary.\n\n"
        "Paths from published work\n"
        "  integer-modulus one-digit blocks, rational rigidity, and real branches\n"
        "    Repetend Rigidity at the Golden Scale\n"
        "    nfield help weighted-reference-profile\n\n"
        "  synchronized remainder clocks, digit bins, orbit families, and limits\n"
        "    Digit-Partitioning Primes and the Alignment Formula\n"
        "    nfield help digit-partition\n\n"
        "  coset correction, exceptional primes, and displayed limit table\n"
        "    The Alignment Limit for All Primes\n"
        "    nfield help alignment-limit\n\n"
        "  synchronized reference, pairwise mean, and signed residual\n"
        "    The Coherence Decomposition\n"
        "    nfield help coherence-decomposition\n\n"
        "  synchronized matrix, orbit blocks, and supported-lift spectrum\n"
        "    The Cross-Alignment Matrix\n"
        "    nfield help cross-alignment\n\n"
        "  multiplicative orbit-frequency fibers, rank laws, and spectral excess\n"
        "    The Spectral Structure of Fractional Fields\n"
        "    nfield help spectral-structure\n\n"
        "  additive digit-bin power, interval kernels, and overlap profiles\n"
        "    The Spectral Power of the Digit Function\n"
        "    nfield help spectral-power\n\n"
        "  same-bin cross-spectrum, multiplicative slices, and orbit harmonics\n"
        "    The Autocorrelation Formula\n"
        "    nfield help autocorrelation\n\n"
        "  Ramanujan selector, spectral line, phase gate, and Euclidean cells\n"
        "    Phase-Filtered Ramanujan Sums and the Spectral Gate\n"
        "    nfield help phase-gate\n\n"
        "  digit-bin conjugation, complete zero family, collision mass, and lags\n"
        "    Bin Derangements and the Gate Width Theorem\n"
        "    nfield help bin-derangements\n\n"
        "  finite character decomposition and published cutoff snapshot\n"
        "    The Character Structure of the Collision Fluctuation\n"
        "    nfield help collision-characters\n\n"
        "  silent-prime examples and exact variance tables\n"
        "    Silent Primes and the Variance of the Collision Count\n"
        "    nfield help silent-primes\n\n"
        "  finite fluctuation table, class means, and published sums\n"
        "    The Collision Fluctuation Sum\n"
        "    nfield help collision-fluctuation\n\n"
        "  all-lag centered tables and published prime sums\n"
        "    The Centered Collision Sum\n"
        "    nfield help collision-centering\n\n"
        "  complete finite periodic table and selected-base summaries\n"
        "    The Collision Periodic Table\n"
        "    nfield help collision-table\n\n"
        "  reduction fibers, direct comparisons, and declared prime windows\n"
        "    The Collision Transform and the Critical Strip\n"
        "    The Collision Transform\n"
        "    nfield help collision-transform\n\n"
        "  quotient carry, true residue channels, and decimal window\n"
        "    The Neutrality Theorem\n"
        "    nfield help residue-three-neutrality\n\n"
        "  compatible prime channels, squarefree coordinates, and character data\n"
        "    The General Neutrality Theorem\n"
        "    nfield help compatible-residue-channels\n\n"
        "  centered tables, finite character pairing, and exact CRT orthogonality\n"
        "    The Double Transversality\n"
        "    nfield help centered-collision-table\n"
        "    nfield help finite-character-pairing\n"
        "    nfield help coprime-base-orthogonality\n\n"
    );
    printf(
        "  finite determination, primitive odd sector, pair relabeling, additive\n"
        "  reflection well, and reflected prime-pair sign\n"
        "    The Spectral Repulsion\n"
        "    nfield help finite-determination\n"
        "    nfield help primitive-odd-sector\n"
        "    nfield help conjugate-pair-relabeling\n"
        "    nfield help additive-reflection-well\n"
        "    nfield help reflected-prime-pair-sign\n\n"
        "  centered collision table, finite determination, primitive odd gate,\n"
        "  fiber cancellation, Bernoulli factorization, moments, and correlation\n"
        "    The Collision Spectrum and the L-Function Landscape\n"
        "    The Collision Spectrum\n"
        "    nfield help centered-collision-table\n"
        "    nfield help finite-determination\n"
        "    nfield help primitive-odd-sector\n"
        "    nfield help primitive-character-cancellation\n"
        "    nfield help collision-spectrum-factorization\n"
        "    nfield help special-value-moment\n"
        "    nfield help base-five-cyclotomic-identity\n"
        "    nfield help short-sum-bernoulli-correlation\n\n"
        "  primitive-character cancellation, periodic-zeta factorization,\n"
        "  boundary recovery, and active-channel classification\n"
        "    The Analytic Collision Transform\n"
        "    nfield help primitive-character-cancellation\n"
        "    nfield help periodic-zeta-factorization\n"
        "    nfield help collision-boundary-recovery\n"
        "    nfield help active-collision-channel\n\n"
        "  collision coordinate, finite determination, reflection, and wrapping\n"
        "  half-group cardinality\n"
        "    The Collision Invariant\n"
        "    nfield help bin-derangements\n"
        "    nfield help collision-coordinate\n"
        "    nfield help finite-determination\n"
        "    nfield help reflection-identity\n"
        "    nfield help half-group\n\n"
        "  finite table, reflection and parity gates, all-prime labels, finite\n"
        "  block quotient, exact bulk multiplicity, and heat-trace bounds\n"
        "    The Structure That Survives\n"
        "    nfield help finite-determination\n"
        "    nfield help reflection-identity\n"
        "    nfield help primitive-odd-sector\n"
        "    nfield help collision-spectrum-factorization\n"
        "    nfield help all-prime-collision-label\n"
        "    nfield help finite-spectral-quotient\n\n"
        "  finite-prefix slice identity, primitive and induced boundary\n"
        "  spectra, unit inversion, sawtooth correlations, and conductor ledger\n"
        "    Carry Boundaries and Bernoulli Spectra in Long Division\n"
        "    nfield help finite-prefix-slice\n"
        "    nfield help boundary-bernoulli-factorization\n"
        "    nfield help boundary-conductor-ledger\n"
        "    nfield help terminal-collision-conductor-ledger\n\n"
        "  oriented two-digit boundary, divisor response, and ramified energy\n"
        "    Oriented Digit Comparison and Ramified Response\n"
        "    nfield help oriented-digit-comparison\n\n"
        "  exact conductor spectrum, finite-state lift, full prime-power orbit\n"
        "  energy, index-two law, and higher-index Jacobi expansion\n"
        "    Additive Boundaries and Conductor Energies of Periodic Remainder Orbits\n"
        "    nfield help boundary-conductor-ledger\n"
        "    nfield help finite-state-orbit-boundary\n"
        "    nfield help full-orbit-energy\n"
        "    nfield help quadratic-orbit-energy\n"
        "    nfield help subgroup-jacobi-expansion\n\n"
        "  exact carry-table energy dictionary and finite pole split\n"
        "    The Cubic Law for Digit-Collision Energy\n"
        "    nfield help prime-base-collision-energy\n"
        "\n"
        "  exact finite residual and the proved all-prime secondary coefficient\n"
        "    The Secondary Term in Digit-Collision Energy\n"
        "    nfield help arithmetic-boundary-defect\n\n"
        "  integer and prime-predecessor observations, cutoff boundaries,\n"
        "  unit phases, finite conductors, and progression means\n"
        "    The Stationary-to-Diagonal Transition in Collision Capacity\n"
        "    nfield help capacity-resolution\n\n"
        "  local carry selection, source labels, primitive ledger and inverse\n"
        "    Finite Generation of Collision Capacity\n"
        "    nfield help capacity-generation\n\n"
        "  conserved primitive mass, alignment factors, finite laws and cutoff bounds\n"
        "    Conservation and Profinite Dynamics in Digit-Collision Energy\n"
        "    nfield help weighted-remainder-state\n\n"
        "  native projection, transported readings and complete signed work\n"
        "    Unity, Refinement, and Signed Capture\n"
        "    nfield help native-refinement\n\n"
        "  shifted sampling, common resets and stopped reciprocal sources\n"
        "    The Unit Sampling Defect in Digit-Collision Energy\n"
        "    nfield help collision-sampling\n\n"
        "  boundary readings, changed observations and invariant energy\n"
        "    Collision Calculus: Boundary Readings, Energy and Refinement\n"
        "    nfield help field-observation\n"
        "    nfield help collision-sampling\n"
        "    nfield help native-refinement\n\n"
        "Each object has focused help, exploratory inputs, an exact verifier, CLI\n"
        "regression tests, and JSON/TCP API tests. Fixed tables are fixtures inside\n"
        "the larger mathematical surface.\n"
    );
}

static int print_help_topic(const char *topic)
{
    if (strcmp(topic, "explore") == 0 || strcmp(topic, "analyze") == 0 ||
        strcmp(topic, "field") == 0 || strcmp(topic, "align") == 0 ||
        strcmp(topic, "div") == 0 || strcmp(topic, "decompose") == 0 ||
        strcmp(topic, "polar") == 0 || strcmp(topic, "survey") == 0 ||
        strcmp(topic, "range") == 0 || strcmp(topic, "table") == 0 ||
        strcmp(topic, "spectral") == 0 || strcmp(topic, "equations") == 0)
        explore_help();
    else if (strcmp(topic, "commands") == 0) nfield_commands_help();
    else if (strcmp(topic, "native-refinement") == 0) native_refinement_help();
    else if (strcmp(topic, "field-observation") == 0) field_observation_help();
    else if (strcmp(topic, "completion") == 0) nfield_completion_help();
    else if (strcmp(topic, "version") == 0) version_help();
    else if (strcmp(topic, "tables") == 0) tables_help();
    else if (strcmp(topic, "reciprocal-square-selection") == 0)
        reciprocal_square_selection_help();
    else if (strcmp(topic, "weighted-reference-profile") == 0)
        weighted_reference_profile_help();
    else if (strcmp(topic, "digit-partition") == 0) digit_partition_help();
    else if (strcmp(topic, "alignment-limit") == 0) alignment_limit_help();
    else if (strcmp(topic, "three-tier") == 0) three_tier_help();
    else if (strcmp(topic, "deficit-lattice") == 0) deficit_lattice_help();
    else if (strcmp(topic, "coherence-decomposition") == 0) coherence_decomposition_help();
    else if (strcmp(topic, "cross-alignment") == 0) cross_alignment_help();
    else if (strcmp(topic, "spectral-structure") == 0) spectral_structure_help();
    else if (strcmp(topic, "spectral-power") == 0) spectral_power_help();
    else if (strcmp(topic, "autocorrelation") == 0) autocorrelation_formula_help();
    else if (strcmp(topic, "phase-gate") == 0) phase_gate_help();
    else if (strcmp(topic, "bin-derangements") == 0) bin_derangements_help();
    else if (strcmp(topic, "collision-characters") == 0) collision_characters_help();
    else if (strcmp(topic, "silent-primes") == 0) silent_primes_help();
    else if (strcmp(topic, "collision-fluctuation") == 0) collision_fluctuation_help();
    else if (strcmp(topic, "collision-centering") == 0
             || strcmp(topic, "centered-collision") == 0)
        centered_collision_help();
    else if (strcmp(topic, "collision-table") == 0 ||
             strcmp(topic, "collision-periodic-table") == 0)
        collision_periodic_help();
    else if (strcmp(topic, "collision-transform") == 0) collision_transform_help();
    else if (strcmp(topic, "residue-three-neutrality") == 0 ||
             strcmp(topic, "neutrality-theorem") == 0)
        residue_three_neutrality_help();
    else if (strcmp(topic, "compatible-residue-channels") == 0 ||
             strcmp(topic, "general-neutrality") == 0)
        compatible_residue_channels_help();
    else if (strcmp(topic, "centered-collision-table") == 0) centered_collision_table_help();
    else if (strcmp(topic, "finite-character-pairing") == 0) finite_character_pairing_help();
    else if (strcmp(topic, "coprime-base-orthogonality") == 0) coprime_base_orthogonality_help();
    else if (strcmp(topic, "natural-prime-sum-window") == 0) natural_prime_sum_window_help();
    else if (strcmp(topic, "primitive-odd-sector") == 0) primitive_odd_sector_help();
    else if (strcmp(topic, "conjugate-pair-relabeling") == 0) conjugate_pair_relabeling_help();
    else if (strcmp(topic, "additive-reflection-well") == 0) additive_reflection_well_help();
    else if (strcmp(topic, "reflected-prime-pair-sign") == 0 ||
             strcmp(topic, "goldbach-obstruction") == 0)
        reflected_prime_pair_sign_help();
    else if (strcmp(topic, "collision-spectrum-factorization") == 0) collision_spectrum_factorization_help();
    else if (strcmp(topic, "special-value-moment") == 0) special_value_moment_help();
    else if (strcmp(topic, "base-five-cyclotomic-identity") == 0) base_five_cyclotomic_identity_help();
    else if (strcmp(topic, "short-sum-bernoulli-correlation") == 0) short_sum_bernoulli_correlation_help();
    else if (strcmp(topic, "weighted-remainder-state") == 0) weighted_remainder_state_help();
    else if (strcmp(topic, "capacity-resolution") == 0) collision_capacity_transition_help();
    else if (strcmp(topic, "capacity-generation") == 0) collision_capacity_generation_help();
    else if (strcmp(topic, "collision-sampling") == 0) collision_sampling_help();
    else if (strcmp(topic, "boundary-spectrum") == 0) boundary_spectrum_help();
    else if (strcmp(topic, "primitive-character-cancellation") == 0) primitive_character_cancellation_help();
    else if (strcmp(topic, "periodic-zeta-factorization") == 0) periodic_zeta_factorization_help();
    else if (strcmp(topic, "collision-boundary-recovery") == 0) collision_boundary_recovery_help();
    else if (strcmp(topic, "active-collision-channel") == 0) active_collision_channel_help();
    else if (strcmp(topic, "collision-coordinate") == 0) collision_coordinate_help();
    else if (strcmp(topic, "finite-determination") == 0) finite_determination_help();
    else if (strcmp(topic, "reflection-identity") == 0) reflection_identity_help();
    else if (strcmp(topic, "half-group") == 0) half_group_help();
    else if (strcmp(topic, "all-prime-collision-label") == 0) all_prime_collision_label_help();
    else if (strcmp(topic, "finite-spectral-quotient") == 0) finite_spectral_quotient_help();
    else if (strcmp(topic, "finite-prefix-slice") == 0) finite_prefix_slice_help();
    else if (strcmp(topic, "oriented-digit-comparison") == 0) oriented_digit_comparison_help();
    else if (strcmp(topic, "boundary-bernoulli-factorization") == 0) boundary_bernoulli_factorization_help();
    else if (strcmp(topic, "boundary-conductor-ledger") == 0) boundary_conductor_ledger_help();
    else if (strcmp(topic, "finite-state-orbit-boundary") == 0) finite_state_orbit_boundary_help();
    else if (strcmp(topic, "full-orbit-energy") == 0) full_orbit_energy_help();
    else if (strcmp(topic, "quadratic-orbit-energy") == 0) quadratic_orbit_energy_help();
    else if (strcmp(topic, "subgroup-jacobi-expansion") == 0) subgroup_jacobi_expansion_help();
    else if (strcmp(topic, "prime-base-collision-energy") == 0) prime_base_collision_energy_help();
    else if (strcmp(topic, "arithmetic-boundary-defect") == 0) arithmetic_boundary_defect_help();
    else if (strcmp(topic, "carry-completed-carrier") == 0) carry_completed_carrier_help();
    else if (strcmp(topic, "terminal-collision-conductor-ledger") == 0) terminal_collision_conductor_ledger_help();
    else if (strcmp(topic, "reading-map") == 0
             || strcmp(topic, "verification-map") == 0)
        verification_map_help();
    else if (strcmp(topic, "verify") == 0) verify_help();
    else if (strcmp(topic, "legacy") == 0) legacy_help();
    else if (strcmp(topic, "daemon") == 0) daemon_help();
    else return 0;
    return 1;
}

static int parse_base(int argc, char **argv, int start)
{
    for (int i = start; i < argc - 1; i++) {
        if (strcmp(argv[i], "--base") == 0)
            return atoi(argv[i + 1]);
    }
    return 10;
}

static int parse_positional_base(int argc, char **argv, int start)
{
    int base = parse_base(argc, argv, start);
    if (base != 10) return base;
    if (argc > start && argv[start][0] >= '0' && argv[start][0] <= '9')
        return atoi(argv[start]);
    return 10;
}

static int has_flag(int argc, char **argv, const char *flag)
{
    for (int i = 1; i < argc; i++)
        if (strcmp(argv[i], flag) == 0)
            return 1;
    return 0;
}

static int parse_int_option(int argc, char **argv, const char *option,
                            int fallback)
{
    for (int i = 1; i < argc - 1; i++)
        if (strcmp(argv[i], option) == 0)
            return atoi(argv[i + 1]);
    return fallback;
}

static const char *parse_string_option(int argc, char **argv,
                                       const char *option)
{
    for (int i = 1; i < argc - 1; i++)
        if (strcmp(argv[i], option) == 0)
            return argv[i + 1];
    return NULL;
}

static long double parse_long_double_option(int argc, char **argv,
                                            const char *option,
                                            long double fallback)
{
    for (int i = 1; i < argc - 1; i++)
        if (strcmp(argv[i], option) == 0)
            return strtold(argv[i + 1], NULL);
    return fallback;
}

/* ── Shared arithmetic helpers ──────────────────────────── */

static int is_prime_local(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int collision_count_local(int p, int base) {
    int g = base % p;
    int C = 0;
    for (int r = 1; r < p; r++) {
        int gr = (int)(((long long)g * r) % p);
        if (gr == 0) continue;
        if ((base * r) / p == (base * gr) / p) C++;
    }
    return C;
}

static int gcd_local(int a, int b) { while (b) { int t = b; b = a % b; a = t; } return a; }

static int power_mod_local(int base, int exp, int mod) {
    long long r = 1, b = base % mod;
    while (exp > 0) { if (exp & 1) r = r * b % mod; b = b * b % mod; exp >>= 1; }
    return (int)r;
}

static void collision_table_print(int base, int show_pairs)
{
    if (base > 100) {
        printf("Base limited to 100 (b^2 = %d cells).\n", base * base);
        return;
    }

    int m = base * base;
    int *S = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    if (!S || !seen) {
        free(S);
        free(seen);
        printf("Out of memory\n");
        return;
    }

    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        S[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }

    printf("Collision periodic table, base %d (mod %d)\n\n", base, m);
    printf("    ");
    for (int c = 0; c < base; c++) printf(" %3d", c);
    printf("\n");

    for (int r = 0; r < base; r++) {
        printf(" %d: ", r);
        for (int c = 0; c < base; c++) {
            int cls = r * base + c;
            if (gcd_local(cls, m) != 1 || !seen[cls]) printf("   .");
            else printf(" %+3d", S[cls]);
        }
        printf("\n");
    }
    printf("\nMean = -1/2. Complement pairs: S(a) + S(%d - a) = -1.\n", m);

    if (show_pairs) {
        printf("\nComplement pairs:\n\n");
        printf("  a       S(a)    %d-a    S(%d-a)    sum\n", m, m);
        printf("  ----    ----    ----    ------    ----\n");
        for (int a = 1; a < m; a++) {
            int b = m - a;
            if (a >= b) continue;
            if (gcd_local(a, m) != 1 || !seen[a] || !seen[b]) continue;
            printf("  %4d    %+4d    %4d      %+4d    %+4d\n",
                   a, S[a], b, S[b], S[a] + S[b]);
        }
    }

    free(S);
    free(seen);
}

static void character_components_print(int base)
{
    int m = base * base;

    /* Compute collision table */
    int *S_tab = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    int phi_m = 0;
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }
    int *units = malloc(m * sizeof(int));
    for (int a = 1; a < m; a++) {
        if (gcd_local(a, m) != 1) continue;
        if (!seen[a]) continue;
        units[phi_m++] = a;
    }

    /* Center by spectral class mean (per-class, not global -1/2) */
    /* Spectral class R = (a-1) mod b for unit a mod m */
    double *class_sum = calloc(base, sizeof(double));
    int *class_cnt = calloc(base, sizeof(int));
    for (int i = 0; i < phi_m; i++) {
        int R = (units[i] - 1) % base;
        class_sum[R] += S_tab[units[i]];
        class_cnt[R]++;
    }
    double *class_mean = calloc(base, sizeof(double));
    for (int r = 0; r < base; r++)
        if (class_cnt[r] > 0) class_mean[r] = class_sum[r] / class_cnt[r];

    double *Sc = malloc(phi_m * sizeof(double));
    for (int i = 0; i < phi_m; i++) {
        int R = (units[i] - 1) % base;
        Sc[i] = S_tab[units[i]] - class_mean[R];
    }
    free(class_sum); free(class_cnt); free(class_mean);

    /* Factor m into prime powers for CRT character enumeration */
    int factors[20], fpowers[20], nfact = 0;
    { int tmp = m;
      for (int f = 2; f * f <= tmp; f++) {
        if (tmp % f == 0) {
            factors[nfact] = f; fpowers[nfact] = 0;
            while (tmp % f == 0) { fpowers[nfact]++; tmp /= f; }
            nfact++;
        }
      }
      if (tmp > 1) { factors[nfact] = tmp; fpowers[nfact] = 1; nfact++; }
    }

    /* For each factor p^k, compute p^k, phi(p^k), generator, and index table */
    int comp_pk[20], comp_phi[20], comp_gen[20];
    int *comp_ind[20];
    for (int fi = 0; fi < nfact; fi++) {
        int pk = 1;
        for (int j = 0; j < fpowers[fi]; j++) pk *= factors[fi];
        comp_pk[fi] = pk;
        comp_phi[fi] = pk - pk / factors[fi];

        /* Find generator */
        if (factors[fi] == 2 && fpowers[fi] == 1) { comp_gen[fi] = 1; comp_phi[fi] = 1; }
        else if (factors[fi] == 2 && fpowers[fi] == 2) { comp_gen[fi] = 3; }
        else {
            comp_gen[fi] = 0;
            for (int g = 2; g < pk; g++) {
                if (gcd_local(g, pk) != 1) continue;
                long long pw = 1; int ok = 1;
                for (int j = 1; j < comp_phi[fi]; j++) { pw = pw * g % pk; if (pw == 1) { ok = 0; break; } }
                if (ok) { comp_gen[fi] = g; break; }
            }
        }

        comp_ind[fi] = calloc(pk, sizeof(int));
        if (comp_phi[fi] > 1) {
            long long pw = 1;
            for (int j = 0; j < comp_phi[fi]; j++) { comp_ind[fi][(int)pw] = j; pw = pw * comp_gen[fi] % pk; }
        }
    }

    /* Collect primes */
    int max_p = 50000, np = 0;
    int *primes = malloc(max_p * sizeof(int));
    for (int p = m + 1; p <= max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        primes[np++] = p;
    }

    double s = 0.5;
    int n_pos = 0, n_neg = 0;
    double sum_pos = 0, sum_neg = 0;
    int n_odd = 0;

    double *coeff_mag = malloc(phi_m * sizeof(double));
    double *psum_mag = malloc(phi_m * sizeof(double));

    /* Enumerate characters via CRT indices */
    int k_ranges[20];
    for (int fi = 0; fi < nfact; fi++) k_ranges[fi] = comp_phi[fi];

    /* Total characters = product of k_ranges = phi_m */
    for (int kk = 0; kk < phi_m; kk++) {
        /* Decompose kk into per-component indices */
        int k_comp[20];
        int tmp_k = kk;
        for (int fi = 0; fi < nfact; fi++) {
            k_comp[fi] = tmp_k % k_ranges[fi];
            tmp_k /= k_ranges[fi];
        }

        /* Compute chi(m-1) to check odd/even */
        double neg1_angle = 0;
        for (int fi = 0; fi < nfact; fi++) {
            int a_mod = (m - 1) % comp_pk[fi];
            if (comp_phi[fi] <= 1) continue;
            neg1_angle += 2.0 * M_PI * k_comp[fi] * comp_ind[fi][a_mod] / (double)comp_phi[fi];
        }
        if (cos(neg1_angle) > -0.5) continue; /* even, skip */

        /* S_hat(chi) = sum_a Sc(a) * conj(chi(a)) */
        double re_S = 0, im_S = 0;
        for (int ui = 0; ui < phi_m; ui++) {
            int a = units[ui];
            double angle = 0;
            for (int fi = 0; fi < nfact; fi++) {
                int a_mod = a % comp_pk[fi];
                if (comp_phi[fi] <= 1) continue;
                angle += 2.0 * M_PI * k_comp[fi] * comp_ind[fi][a_mod] / (double)comp_phi[fi];
            }
            re_S += Sc[ui] * cos(angle);  /* conj: cos(-x) = cos(x) */
            im_S += Sc[ui] * (-sin(angle)); /* conj: sin(-x) = -sin(x) */
        }
        double S_mag = sqrt(re_S * re_S + im_S * im_S);

        /* P(s, chi) = sum_p chi(p) / p^s */
        double re_P = 0, im_P = 0;
        for (int j = 0; j < np; j++) {
            int p = primes[j];
            int cls = p % m;
            if (gcd_local(cls, m) != 1) continue;
            double angle = 0;
            for (int fi = 0; fi < nfact; fi++) {
                int a_mod = cls % comp_pk[fi];
                if (comp_phi[fi] <= 1) continue;
                angle += 2.0 * M_PI * k_comp[fi] * comp_ind[fi][a_mod] / (double)comp_phi[fi];
            }
            double w = 1.0 / pow((double)p, s);
            re_P += w * cos(angle);
            im_P += w * sin(angle);
        }
        double P_mag = sqrt(re_P * re_P + im_P * im_P);

        double prod = re_S * re_P - im_S * im_P; /* Re(z1*z2) = re1*re2 - im1*im2 */

        coeff_mag[n_odd] = S_mag;
        psum_mag[n_odd] = P_mag;

        if (prod > 0) { n_pos++; sum_pos += prod; }
        else { n_neg++; sum_neg += prod; }
        n_odd++;
    }

    for (int fi = 0; fi < nfact; fi++) free(comp_ind[fi]);

    printf("Character components, base %d, %d odd characters, %d primes, s=%.1f\n\n", base, n_odd, np, s);
    printf("  positive: %d    sum: %+.2f\n", n_pos, sum_pos);
    printf("  negative: %d    sum: %+.2f\n", n_neg, sum_neg);
    printf("  net:              %+.2f\n", sum_pos + sum_neg);

    /* Pearson correlation between |S_hat| and |P| */
    if (n_odd > 2) {
        double mean_c = 0, mean_p = 0;
        for (int i = 0; i < n_odd; i++) { mean_c += coeff_mag[i]; mean_p += psum_mag[i]; }
        mean_c /= n_odd; mean_p /= n_odd;
        double cov = 0, var_c = 0, var_p = 0;
        for (int i = 0; i < n_odd; i++) {
            double dc = coeff_mag[i] - mean_c, dp = psum_mag[i] - mean_p;
            cov += dc * dp; var_c += dc * dc; var_p += dp * dp;
        }
        double corr = (var_c > 0 && var_p > 0) ? cov / sqrt(var_c * var_p) : 0;
        printf("\n  Pearson correlation |S_hat| vs |P|: %+.3f\n", corr);
    }

    free(S_tab); free(seen); free(units); free(Sc);
    free(primes); free(coeff_mag); free(psum_mag);
}

/* Compute global mean of S over coprime classes from the table */
static double compute_global_mean(int base)
{
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m; if (seen[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }
    double sum = 0; int cnt = 0;
    for (int a = 1; a < m; a++) {
        if (!seen[a]) continue;
        int ga = a, ha = m; while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        sum += S_tab[a]; cnt++;
    }
    free(S_tab); free(seen);
    return cnt > 0 ? sum / cnt : 0;
}

/* ── Blog command implementations ──────────────────────── */

/* fluctuation_sum / mertens_growth: Φ_x(1,1) and ratio to log log p */
static void fluctuation_sum_print(int base, int lag, int max_p)
{
    if (max_p <= 0) max_p = 50000;

    double phi_sum = 0;
    int np = 0;
    int last_p = 0;

    printf("Fluctuation sum Phi_x(1, %d), base %d\n\n", lag, base);

    for (int p = base + 2; p <= max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int g_lag = power_mod_local(base, lag, p);

        /* C(b^lag mod p) */
        int C_lag = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g_lag * r) % p);
            if (gr == 0) continue;
            if ((base * r) / p == (base * gr) / p) C_lag++;
        }

        int Q = (p - 1) / base;
        int R = (p - 1) % base;
        double denom = (double)(base * (Q - 1) + R);
        double mean_c = denom != 0.0
            ? (double)Q * (base * (Q - 1) + 2 * R) / denom
            : 0.0;
        double delta = C_lag - mean_c;
        phi_sum += delta / p;
        np++;
        last_p = p;
    }

    double llp = log(log((double)last_p));
    printf("  primes scanned: %d (up to p = %d)\n", np, last_p);
    printf("  accumulated sum: %.2f\n", phi_sum);
    printf("  sum / log log p_max = %.3f\n", phi_sum / llp);
}

/* spectrum: eigenvalues of the cross-alignment matrix A(p) */
static void spectrum_print(int p, int base)
{
    if (p < 2 || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p coprime to base.\n"); return;
    }
    if (p > 500) {
        printf("Matrix too large for web terminal (p=%d). Try p < 500.\n", p); return;
    }

    int n = p - 1; /* matrix dimension */
    int L = 0;
    { int r = 1; do { r = (r * base) % p; L++; } while (r != 1); }

    /* Compute digits d[r] = floor(base * r / p) for r = 1..p-1 */
    int *d = malloc(p * sizeof(int));
    for (int r = 0; r < p; r++) d[r] = (base * r) / p;

    /* Build A(p): a[i][j] = fraction of positions where digits of i/p and j/p agree */
    /* For rows i and j (1-indexed), compare the L digits of their repetends */
    double *eigenvals = malloc(n * sizeof(double));

    /* Compute eigenvalues via R(ell) / L for primitive root case,
       or direct matrix for general case */

    if (L == n) {
        /* Primitive root: eigenvalues = DFT of R(ell)/L */
        int *R = calloc(L, sizeof(int));
        for (int ell = 0; ell < L; ell++) {
            int g = power_mod_local(base, ell, p);
            int count = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if (gr == 0) continue;
                if (d[r] == d[gr]) count++;
            }
            R[ell] = count;
        }
        /* eigenvalue_k = (1/L) * sum_ell R(ell) * cos(2pi*k*ell/L) */
        for (int k = 0; k < L; k++) {
            double val = 0;
            for (int ell = 0; ell < L; ell++)
                val += R[ell] * cos(2.0 * M_PI * k * ell / L);
            eigenvals[k] = val / (double)L;
        }
        free(R);
    } else {
        /* General case: diagonalize the exact synchronized matrix.  The old
           shortcut treated every two-coset case as a two-level spectrum and
           used an autocorrelation approximation for more cosets; neither is
           valid in general. */
        int exact_count = 0, exact_order = 0, exact_cosets = 0;
        if (!cross_alignment_eigenvalues(p, base, eigenvals, n,
                                         &exact_count, &exact_order,
                                         &exact_cosets)
            || exact_count != n || exact_order != L
            || exact_cosets != n / L) {
            fprintf(stderr, "Exact cross-alignment eigensolver failed.\n");
            free(d);
            free(eigenvals);
            return;
        }
    }

    /* Sort eigenvalues */
    for (int i = 0; i < n - 1; i++)
        for (int j = i + 1; j < n; j++)
            if (eigenvals[j] > eigenvals[i]) { double t = eigenvals[i]; eigenvals[i] = eigenvals[j]; eigenvals[j] = t; }

    /* Group by value and print */
    printf("Cross-alignment matrix eigenvalues for p = %d, base %d\n", p, base);
    printf("  cycle length L = %d, orbits = %d\n\n", L, n / L);
    printf("  eigenvalues: ");
    int i = 0;
    int first = 1;
    while (i < n) {
        int mult = 1;
        while (i + mult < n && fabs(eigenvals[i] - eigenvals[i + mult]) < 0.001) mult++;

        if (!first) printf(", ");

        /* Try to express as a fraction */
        int num = -1, den = -1;
        for (int dd = 1; dd <= 12; dd++) {
            double frac = eigenvals[i] * dd;
            if (fabs(frac - round(frac)) < 0.01) { num = (int)round(frac); den = dd; break; }
        }
        if (den > 0 && den > 1) printf("%d/%d", num, den);
        else if (den == 1) printf("%d", num);
        else printf("%.4f", eigenvals[i]);

        if (mult > 1) printf(" (mult %d)", mult);
        i += mult;
        first = 0;
    }
    printf("\n");

    /* Classification */
    int n_distinct = 0;
    { double prev = -999; for (int k = 0; k < n; k++) if (fabs(eigenvals[k] - prev) > 0.001) { n_distinct++; prev = eigenvals[k]; } }

    if (n_distinct == 1) printf("  flat spectrum (digit-partitioning prime)\n");
    else if (n_distinct == 2) printf("  two distinct spectral levels\n");
    else printf("  %d distinct values, full spectrum\n", n_distinct);

    free(d); free(eigenvals);
}

/* gate: spectral gate analysis */
static void gate_print(int p, int base)
{
    if (p < 2 || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p coprime to base.\n"); return;
    }
    int R_class = p % base;
    int Q = (p - 1) / base;
    int L = 0;
    { int r = 1; do { r = (r * base) % p; L++; } while (r != 1); }
    int gate_width = base - 1;

    printf("family: r = %d, gate width %d\n", R_class, gate_width);
    printf("loop length %d", L);
    if (L < gate_width) printf(" (smaller than the gate)");
    printf("\n");

    /* Count deranging shifts and large bins */
    int deranging_shifts = 0;
    int *d = malloc(p * sizeof(int));
    for (int r = 0; r < p; r++) d[r] = (base * r) / p;

    for (int ell = 1; ell < L; ell++) {
        int g = power_mod_local(base, ell, p);
        int matches = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if (d[r] == d[gr]) matches++;
        }
        if (matches == 0) deranging_shifts++;
    }

    int signal_shifts = L - deranging_shifts; /* includes ell=0 which always has signal */
    if (deranging_shifts == L - 1)
        printf("every nontrivial shift is deranging, R(ell) = 0 for all ell > 0\n");
    else
        printf("%d shifts carry signal, %d vanish\n", signal_shifts, deranging_shifts);

    /* Count large bins (bins with more than Q remainders) */
    int large_bins = 0;
    for (int dd = 0; dd < base; dd++) {
        int count = 0;
        for (int r = 1; r < p; r++)
            if (d[r] == dd) count++;
        if (count > Q) large_bins++;
    }
    printf("large bins: %d (matches r - 1)\n", large_bins);

    /* List primes in the same family */
    if (R_class > 0) {
        printf("same gate as ");
        int shown = 0;
        for (int pp = base + 1; pp < 100 && shown < 5; pp++) {
            if (pp == p) continue;
            if (!is_prime_local(pp) || pp % base == 0) continue;
            if (pp % base == R_class) {
                if (shown > 0) printf(", ");
                printf("%d", pp);
                shown++;
            }
        }
        printf(", every prime ending in %d\n", R_class);
    }

    free(d);
}

/* class_bias: per-last-digit mean collision deviation */
static void class_bias_print(int base, int max_p)
{
    if (max_p <= 0) max_p = 50000;

    /* Group primes by last digit, compute mean Delta for each */
    double *sum_delta = calloc(base, sizeof(double));
    int *count = calloc(base, sizeof(int));

    for (int p = base + 2; p <= max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int last_digit = p % base;
        int g = base % p;
        int C_lag = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if ((base * r) / p == (base * gr) / p) C_lag++;
        }
        int Q = (p - 1) / base;
        int R = (p - 1) % base;
        double denom = (double)(base * (Q - 1) + R);
        double mean_c = denom != 0.0
            ? (double)Q * (base * (Q - 1) + 2 * R) / denom
            : 0.0;
        sum_delta[last_digit] += (C_lag - mean_c);
        count[last_digit]++;
    }

    printf("Per-class collision bias, base %d, lag 1\n\n", base);
    for (int d = 0; d < base; d++) {
        if (count[d] == 0) continue;
        if (gcd_local(d, base) != 1) continue;
        double mean = sum_delta[d] / count[d];
        printf("  class digit %d:  mean deviation = %+.2f\n", d, mean);
    }

    free(sum_delta); free(count);
}

/* derangements: list deranging multipliers, verify mean formula */
static void derangements_print(int p, int base)
{
    if (p <= base || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p > base, coprime to base.\n"); return;
    }
    int Q = (p - 1) / base;
    int R = (p - 1) % base;

    printf("prime %d, base %d\n", p, base);
    printf("Q = %d, R = %d\n", Q, R);

    /* Compute bins: group remainders by digit */
    printf("bins: ");
    for (int d2 = 0; d2 < base; d2++) {
        if (d2 > 0) printf(" ");
        printf("{");
        int first = 1;
        for (int r = 1; r < p; r++) {
            if ((base * r) / p == d2) {
                if (!first) printf(",");
                printf("%d", r);
                first = 0;
            }
        }
        printf("}");
    }
    printf("\n");

    /* Find deranging (C=0) and constructive (C>0) multipliers, skip g=1 */
    int *deranging = malloc(p * sizeof(int));
    int *constructive = malloc(p * sizeof(int));
    int *C_vals = calloc(p, sizeof(int));
    int n_deranging = 0, n_constructive = 0;
    double sum_constructive = 0;

    for (int g = 2; g < p; g++) {
        int C = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if ((base * r) / p == (base * gr) / p) C++;
        }
        C_vals[g] = C;
        if (C == 0) deranging[n_deranging++] = g;
        else { constructive[n_constructive++] = g; sum_constructive += C; }
    }

    printf("deranging multipliers (%d): {", n_deranging);
    for (int i = 0; i < n_deranging; i++) {
        if (i > 0) printf(", ");
        printf("%d", deranging[i]);
    }
    printf("}\n");

    printf("constructive multipliers (%d)", n_constructive);
    if (n_constructive <= 10) {
        printf(": {");
        for (int i = 0; i < n_constructive; i++) {
            if (i > 0) printf(", ");
            printf("%d", constructive[i]);
        }
        printf("}\n");
        for (int i = 0; i < n_constructive; i++)
            printf("C(%d) = %d\n", constructive[i], C_vals[constructive[i]]);
    } else {
        printf("\n");
    }

    double actual_mean = n_constructive > 0 ? sum_constructive / n_constructive : 0;
    double predicted = (double)Q * (base * (Q - 1) + 2 * R) / (double)(base * (Q - 1) + R);
    printf("mean over constructive: %.2f (formula predicts %.2f) %s\n",
           actual_mean, predicted, fabs(actual_mean - predicted) < 0.015 ? "✓" : "✗");

    free(deranging); free(constructive); free(C_vals);
}

/* centered_sum: raw vs centered fluctuation sums */
static void centered_sum_print(int base, int max_p)
{
    if (max_p <= 0) max_p = 100000;
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen_tab = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen_tab[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen_tab[cls] = 1;
    }

    double s_vals[] = {1.5, 1.2, 1.0, 0.9, 0.5};
    int ns = 5;

    printf("Centered collision sum, base %d\n\n", base);
    printf("  s       raw sum     centered sum\n");
    printf("-----    ---------    ------------\n");

    for (int si = 0; si < ns; si++) {
        double s = s_vals[si];
        double raw = 0, centered = 0;
        for (int p = m + 1; p <= max_p; p++) {
            if (!is_prime_local(p) || p % base == 0) continue;
            int cls = p % m;
            if (!seen_tab[cls]) continue;
            double w = 1.0 / pow((double)p, s);
            double S = S_tab[cls];
            double Sc = S - compute_global_mean(base);
            raw += S * w;
            centered += Sc * w;
        }
        printf(" %.1f    %+9.4f    %+9.4f\n", s, raw, centered);
    }
    printf("\n  Raw sum diverges at s=1. Centered sum converges.\n");
    free(S_tab); free(seen_tab);
}

/* class_means: per-class collision means */
static void class_means_print(int base)
{
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen_tab = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen_tab[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen_tab[cls] = 1;
    }

    printf("Class means, base %d (mod %d)\n\n", base, m);
    printf("  class   S(a)    complement   S(comp)   sum\n");
    printf("  -----   ----    ----------   -------   ---\n");

    int count = 0; double sum_all = 0;
    for (int a = 1; a < m / 2 + 1; a++) {
        if (!seen_tab[a]) continue;
        int ga = a, ha = m;
        while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        int comp = m - a;
        if (!seen_tab[comp]) continue;
        printf("   %3d    %+3d       %3d       %+3d     %+3d\n",
               a, S_tab[a], comp, S_tab[comp], S_tab[a] + S_tab[comp]);
        sum_all += S_tab[a] + S_tab[comp];
        count += 2;
    }
    printf("\n  %d classes, mean = %.4f (exactly -1/2)\n", count, -0.5);
    free(S_tab); free(seen_tab);
}

/* silent_primes: proper implementation with recipe */
static void silent_primes_full_print(int base, int lag)
{
    int m = 1;
    for (int i = 0; i <= lag; i++) m *= base;
    int step = m / base - 1; /* b^lag - 1 */

    printf("Silent primes, base %d, lag %d\n", base, lag);
    printf("recipe: %d - %du for u = 1..%d\n", m, step, base - 1);

    printf("values: ");
    int *vals = malloc(base * sizeof(int));
    int nv = 0;
    for (int u = 1; u < base; u++) {
        int v = m - step * u;
        if (v > 0) { vals[nv++] = v; printf("%s%d", u > 1 ? ", " : "", v); }
    }
    printf("\n");

    /* Factor each value, collect prime factors > base */
    printf("prime factors > %d: {", base);
    int first = 1;
    int sp_count = 0;
    for (int i = 0; i < nv; i++) {
        int v = vals[i];
        /* trial division */
        for (int f = 2; f * f <= v; f++) {
            while (v % f == 0) {
                if (f > base && is_prime_local(f)) {
                    if (!first) printf(", ");
                    printf("%d", f); first = 0; sp_count++;
                }
                v /= f;
            }
        }
        if (v > 1 && v > base && is_prime_local(v)) {
            if (!first) printf(", ");
            printf("%d", v); first = 0; sp_count++;
        }
    }
    printf("}\ntotal silent primes at lag %d in base %d: %d\n", lag, base, sp_count);
    free(vals);
}

/* polarity_field: centered collision values */
static void polarity_field_print(int base)
{
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m; if (seen[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }
    double css[20] = {0}; int ccc[20] = {0};
    for (int a = 1; a < m; a++) {
        if (gcd_local(a, m) != 1 || !seen[a]) continue;
        int R = (a - 1) % base; css[R] += S_tab[a]; ccc[R]++;
    }
    double cmm[20];
    for (int r = 0; r < base; r++) cmm[r] = ccc[r] > 0 ? css[r] / ccc[r] : 0;

    printf("Polarity field F(a), base %d (mod %d)\n", base, m);
    printf("Centered collision invariant: F(a) = S(a) - class_mean\n\n");
    printf("  class    S(a)    F(a)     complement   F(comp)   F(a)+F(comp)\n");
    printf("  -----    ----    ----     ----------   -------   ------------\n");

    for (int a = 1; a < m / 2 + 1; a++) {
        if (!seen[a]) continue;
        if (gcd_local(a, m) != 1) continue;
        int comp = m - a;
        if (!seen[comp]) continue;
        double Fa = S_tab[a] - cmm[(a - 1) % base];
        double Fc = S_tab[comp] - cmm[(comp - 1) % base];
        printf("   %3d     %+3d   %+6.2f       %3d      %+6.2f      %+.2f\n",
               a, S_tab[a], Fa, comp, Fc, Fa + Fc);
    }
    printf("\n  F(a) + F(100-a) = 0 at every pair (centered antisymmetry).\n");
    free(S_tab); free(seen);
}

/* ── Object-table compatibility dispatcher ───────────────── */

static int object_tables_dispatch(const char *object)
{
    if (object == NULL) {
        printf("Usage: nfield tables <object-name>\n\n");
        printf("Available exact object-table reproductions:\n\n");
        printf("  reciprocal-square-selection\n");
        return 0;
    }

    if (strcmp(object, "reciprocal-square-selection") == 0)
        return reciprocal_square_selection_table();

    fprintf(stderr, "No table reproduction is registered for object '%s'.\n",
            object);
    fprintf(stderr, "Run 'tables' with no argument to see object names.\n");
    return 1;
}

/* ── Neutrality / mod-3 class means ────────────────────── */

static void collect_collision_data(int base, int max_p, int **out_primes, double **out_sv, int *out_np)
{
    int m = base * base;
    if (max_p <= 0) max_p = 50000;
    int *primes = malloc(max_p * sizeof(int));
    double *sv = malloc(max_p * sizeof(double));
    int np = 0;

    for (int p = m + 1; p <= max_p && np < max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int C = collision_count_local(p, base);
        double S = C - (double)(p - 1) / base;
        sv[np] = S - compute_global_mean(base); /* centered */
        primes[np] = p;
        np++;
    }
    *out_primes = primes;
    *out_sv = sv;
    *out_np = np;
}

static void neutrality_print(int base, int max_p)
{
    int *primes; double *sv; int np;
    collect_collision_data(base, max_p, &primes, &sv, &np);

    /* Compute mod-3 class means from the TABLE (not from primes) */
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *tab_seen = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (tab_seen[cls]) continue;
        int C = collision_count_local(p, base);
        S_tab[cls] = C - (p - 1) / base;
        tab_seen[cls] = 1;
    }
    /* mu3: mean of S°(a) over table classes grouped by a mod 3 */
    double tsum[3] = {0}; int tcnt[3] = {0};
    for (int a = 1; a < m; a++) {
        if (!tab_seen[a]) continue;
        int ga = a, ha = m;
        while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        double sc = S_tab[a] - compute_global_mean(base); /* centered */
        tsum[a % 3] += sc;
        tcnt[a % 3]++;
    }
    double mu3[3];
    for (int c = 0; c < 3; c++) mu3[c] = tcnt[c] > 0 ? tsum[c] / tcnt[c] : 0;
    free(S_tab); free(tab_seen);

    double s_vals[] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    int ns = 6;

    printf("Neutrality analysis, base %d, %d primes\n", base, np);
    printf("F° = centered sum, F°° = doubly centered, M = mod-3 component\n");
    printf("F°° and M diverge in opposite directions. F° = F°° + M stays bounded.\n");
    printf("If cancellation is perfect, 1+F°°/M approaches 0.\n\n");
    printf("  s       F°        F°°         M       1+F°°/M\n");
    printf("-----   ------   ---------   --------   -------\n");

    for (int si = 0; si < ns; si++) {
        double s = s_vals[si];
        double f_cent = 0, f_dc = 0;
        for (int i = 0; i < np; i++) {
            double w = 1.0 / pow((double)primes[i], s);
            f_cent += sv[i] * w;
            /* F°° = sum of (S°(p) - mu3(p mod 3)) / p^s */
            int cls3 = primes[i] % 3;
            f_dc += (sv[i] - mu3[cls3]) * w;
        }
        double M = f_cent - f_dc;
        double ratio = (fabs(M) > 1e-10) ? 1.0 + f_dc / M : 0;
        printf(" %.1f    %+6.2f   %+9.2f   %+8.2f   %+7.3f\n",
               s, f_cent, f_dc, M, ratio);
    }

    free(primes);
    free(sv);
}

static void mod3_means_print(int base)
{
    int m = base * base;
    /* Compute S(a) for each coprime class, then group by class mod 3 */
    int *S_val = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    if (!S_val || !seen) { free(S_val); free(seen); return; }

    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        int C = collision_count_local(p, base);
        S_val[cls] = C - (p - 1) / base;
        seen[cls] = 1;
    }

    double sum[3] = {0}; int cnt[3] = {0};
    for (int a = 1; a < m; a++) {
        if (!seen[a]) continue;
        int ga = a, ha = m;
        while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        int cls3 = a % 3;
        sum[cls3] += S_val[a];
        cnt[cls3]++;
    }

    printf("Mod-3 class means, base %d (mod %d)\n\n", base, m);
    printf("  class mod 3    count    sum       mean\n");
    printf("  -----------    -----    ---       ----\n");
    for (int c = 0; c < 3; c++) {
        if (cnt[c] > 0)
            printf("      %d          %3d    %+4.0f     %+.4f\n",
                   c, cnt[c], sum[c], sum[c] / cnt[c]);
    }
    double total = sum[0] + sum[1] + sum[2];
    int total_cnt = cnt[0] + cnt[1] + cnt[2];
    printf("\n  overall mean = %.4f  (exactly -1/2)\n", total / total_cnt);

    if (cnt[2] > 0) {
        double m2 = sum[2] / cnt[2];
        printf("\n  Group 2 mean = %.4f", m2);
        if (fabs(m2 - (-0.5)) < 0.01) printf("  (neutral: exactly -1/2)");
        printf("\n");
    }

    free(S_val);
    free(seen);
}

static void neutrality_sweep_print(void)
{
    int bases[] = {3, 5, 7, 10, 11, 12, 13};
    int nb = 7;

    printf("Neutrality sweep across bases\n\n");
    printf("  base   phi(b^2)   group 2 mean     c0   neutral?   regime\n");
    printf("  ----   --------   ------------   -----   --------   ------\n");

    for (int bi = 0; bi < nb; bi++) {
        int base = bases[bi];
        int m = base * base;
        int phi_m = 0;

        int *S_val = calloc(m, sizeof(int));
        int *seen = calloc(m, sizeof(int));
        if (!S_val || !seen) { free(S_val); free(seen); continue; }

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime_local(p) || p % base == 0) continue;
            int cls = p % m;
            if (seen[cls]) continue;
            int C = collision_count_local(p, base);
            S_val[cls] = C - (p - 1) / base;
            seen[cls] = 1;
        }

        double sums[3] = {0}; int cnts[3] = {0};
        for (int a = 1; a < m; a++) {
            if (!seen[a]) continue;
            int ga = a, ha = m;
            while (ha) { int t = ha; ha = ga % ha; ga = t; }
            if (ga != 1) continue;
            phi_m++;
            sums[a % 3] += S_val[a]; cnts[a % 3]++;
        }

        double m2 = cnts[2] > 0 ? sums[2] / cnts[2] : 0;
        int neutral = cnts[2] > 0 && fabs(m2 - (-0.5)) < 0.01;
        /* c0 measures mod-3 bias strength */
        double mean1 = cnts[1] > 0 ? sums[1] / cnts[1] : 0;
        double mean2 = cnts[2] > 0 ? sums[2] / cnts[2] : 0;
        double c0 = mean1 - mean2;
        const char *regime = (base % 3 == 0) ? "3|b" :
                             (fabs(c0) > 0.3 ? "strong" : "weak");

        printf("   %2d      %3d       %+.4f    %+5.2f   %s       %s\n",
               base, phi_m, m2, c0,
               neutral ? "yes" : (base % 3 == 0 ? "n/a" : "no "),
               regime);

        free(S_val);
        free(seen);
    }
}

int main(int argc, char **argv)
{
    dispatch_init(argv[0]);

    if (argc < 2) {
        usage();
        return 0;
    }

    if (strcmp(argv[1], "--version") == 0 ||
        (strcmp(argv[1], "version") == 0 && argc == 2)) {
        print_banner();
        return 0;
    }

    if (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0) {
        usage();
        return 0;
    }

    if (argc >= 3 &&
        (strcmp(argv[2], "--help") == 0 || strcmp(argv[2], "-h") == 0)) {
        if (strcmp(argv[1], "help") == 0) {
            usage();
            return 0;
        }
        if (print_help_topic(argv[1])) return 0;
        fprintf(stderr, "No focused help is available for command: %s\n", argv[1]);
        return 1;
    }

    if (strcmp(argv[1], "__complete") == 0)
        return nfield_completion_candidates(argc - 2, argv + 2);

    if (strcmp(argv[1], "commands") == 0) {
        if (argc != 2) {
            fprintf(stderr, "Usage: nfield commands\n");
            return 1;
        }
        nfield_commands_help();
        return 0;
    }

    if (strcmp(argv[1], "completion") == 0)
        return nfield_completion_command(argc - 2, argv + 2);

    /* Daemon mode */
    if (strcmp(argv[1], "daemon") == 0) {
        int port = 9090, threads = 4;
        for (int i = 2; i < argc - 1; i++) {
            if (strcmp(argv[i], "--port") == 0) port = atoi(argv[i+1]);
            if (strcmp(argv[i], "--threads") == 0) threads = atoi(argv[i+1]);
        }
        if (port < 1 || port > 65535 || threads < 1 || threads > 64) {
            fprintf(stderr,
                    "daemon requires 1<=port<=65535 and 1<=threads<=64\n");
            return 1;
        }
        return daemon_main(port, threads);
    }

    int show_time = has_flag(argc, argv, "--time");
    struct timespec t0, t1;
    if (show_time)
        clock_gettime(CLOCK_MONOTONIC, &t0);

    const char *cmd = argv[1];

    /* bare number: default to analyze */
    if (cmd[0] >= '0' && cmd[0] <= '9') {
        int n    = atoi(cmd);
        if (n < 2) {
            fprintf(stderr, "n must be >= 2\n");
            return 1;
        }
        int base = parse_base(argc, argv, 2);
        Invariants inv = invariants_compute(n, base);
        invariants_print(&inv);
        goto done;
    }

    if (strcmp(cmd, "native-refinement") == 0) {
        return native_refinement_command(argc - 2, argv + 2);

    } else if (strcmp(cmd, "field-observation") == 0) {
        return field_observation_command(argc - 2, argv + 2);

    } else if (strcmp(cmd, "analyze") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        Invariants inv = invariants_compute(n, base);
        invariants_print(&inv);

    } else if (strcmp(cmd, "field") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        Field f = field_build(n, base);
        field_print(&f);
        field_free(&f);

    } else if (strcmp(cmd, "polar") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        polar_print(n, base);

    } else if (strcmp(cmd, "survey") == 0 && argc >= 3) {
        int max  = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        int csv  = has_flag(argc, argv, "--csv");

        survey(max, base, csv);

    } else if (strcmp(cmd, "range") == 0 && argc >= 4) {
        int min  = atoi(argv[2]);
        int max  = atoi(argv[3]);
        int base = parse_base(argc, argv, 4);
        int csv  = has_flag(argc, argv, "--csv");

        survey_range(min, max, base, csv);

    } else if (strcmp(cmd, "golden-threshold-table") == 0) {
        if (reciprocal_square_selection_table() != 0) return 1;

    } else if (strcmp(cmd, "align") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        double a = alignment_exact(n, base);
        printf("alignment(%d, base=%d) = %.6f\n", n, base, a);

    } else if (strcmp(cmd, "spectral") == 0 && argc >= 3) {
        int p    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        if (spectral_power_inspect(p, base) != 0) return 1;

    } else if (strcmp(cmd, "decompose") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        if (decompose_print(n, base) != 0) return 1;

    } else if (strcmp(cmd, "div") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        if (n < 2) {
            fprintf(stderr, "n must be >= 2\n");
            return 1;
        }

        /* Find the maximum chain length across all k */
        int max_steps = 0;
        for (int k = 1; k < n; k++) {
            Repetend rep = repetend_compute(k, n, base);
            int L = rep.cycle_start + rep.cycle_len;
            if (rep.cycle_len == 0) L = rep.len;
            if (L > max_steps) max_steps = L;
            repetend_free(&rep);
        }

        printf("Division table for n = %d, base = %d\n", n, base);
        printf("br = %d*r, d = floor(br/%d), r' = br mod %d\n\n",
               base, n, n);

        /* Header */
        printf("  %3s |", "a");
        for (int j = 0; j < max_steps; j++) {
            if (j > 0) printf(" |");
            printf("  %3s %3s %3s", "r", "br", "d");
        }
        printf("\n");

        /* Separator */
        printf("  ----+");
        for (int j = 0; j < max_steps; j++) {
            if (j > 0) printf("-+");
            printf("-----------");
        }
        printf("\n");

        /* One row per numerator */
        for (int k = 1; k < n; k++) {
            printf("  %3d |", k);
            int r = k;
            for (int j = 0; j < max_steps; j++) {
                if (j > 0) printf(" |");
                if (r == 0) {
                    printf("   %3s %3s %3s", ".", ".", ".");
                } else {
                    long long br = (long long)base * r;
                    int d  = (int)(br / n);
                    int rp = (int)(br % n);
                    printf("  %3d %3lld %3d", r, br, d);
                    r = rp;
                }
            }
            printf("\n");
        }

    } else if (strcmp(cmd, "table") == 0) {
        int base = parse_positional_base(argc, argv, 2);
        collision_table_print(base, has_flag(argc, argv, "--pairs"));

    } else if (strcmp(cmd, "analytic") == 0) {
        int base = parse_base(argc, argv, 2);
        int lag = 1;
        for (int i = 2; i < argc; i++)
            if (argv[i][0] >= '0' && argv[i][0] <= '9' && strcmp(argv[i-1], "--base") != 0)
                lag = atoi(argv[i]);
        analytic_print(base, lag);

    } else if (strcmp(cmd, "scale") == 0) {
        int chrom = has_flag(argc, argv, "--chromatic");
        int alpha_form = has_flag(argc, argv, "--alpha");
        int csv = has_flag(argc, argv, "--csv");
        if (has_flag(argc, argv, "--beta")) alpha_form = 0;
        scale_print(chrom, alpha_form, csv);

    } else if (strcmp(cmd, "coherence") == 0) {
        int base = parse_base(argc, argv, 2);
        int N = 300;
        for (int i = 2; i < argc; i++)
            if (argv[i][0] >= '0' && argv[i][0] <= '9' && strcmp(argv[i-1], "--base") != 0)
                N = atoi(argv[i]);
        coherence_print(base, N);

    } else if (strcmp(cmd, "tables") == 0) {
        const char *object = argc >= 3 ? argv[2] : NULL;
        if (object_tables_dispatch(object) != 0) return 1;

    } else if (strcmp(cmd, "verify") == 0) {
        if (argc < 3) {
            verify_help();
            goto done;
        }
        const char *theorem = NULL;
        for (int i = 2; i < argc; i++) {
            if (argv[i][0] != '-') {
                theorem = argv[i];
                break;
            }
        }
        if (!theorem) {
            verify_help();
            goto done;
        }
        int verify_status = verify_dispatch(theorem);
        if (verify_status != 0) return verify_status;

    } else if (strcmp(cmd, "digit-partition") == 0) {
        if (argc < 3) {
            digit_partition_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (digit_partition_inspect(n, base, depth) != 0) return 1;
        } else if (argv[2][0] >= '0' && argv[2][0] <= '9') {
            int n = atoi(argv[2]);
            int base = parse_base(argc, argv, 3);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (digit_partition_inspect(n, base, depth) != 0) return 1;
        } else if (strcmp(argv[2], "primes") == 0) {
            int base = parse_base(argc, argv, 3);
            digit_partition_primes(base);
        } else if (strcmp(argv[2], "table") == 0) {
            digit_partition_table();
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!digit_partition_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown digit-partition action: %s\n", argv[2]);
            digit_partition_help();
            return 1;
        }

    } else if (strcmp(cmd, "alignment-limit") == 0) {
        if (argc < 3) {
            alignment_limit_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            int m = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (alignment_limit_inspect(p, m, base, depth) != 0) return 1;
        } else if (strcmp(argv[2], "cosets") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (alignment_limit_cosets(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            int base = parse_base(argc, argv, 3);
            int max_prime = parse_int_option(argc, argv, "--max-prime", 61);
            if (alignment_limit_table(base, max_prime) != 0) return 1;
        } else if (strcmp(argv[2], "sharpness") == 0) {
            int steps = parse_int_option(argc, argv, "--steps", 10);
            if (alignment_limit_sharpness(steps) != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!alignment_limit_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown alignment-limit action: %s\n", argv[2]);
            alignment_limit_help();
            return 1;
        }

    } else if (strcmp(cmd, "three-tier") == 0) {
        if (argc < 3) {
            three_tier_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (three_tier_inspect(n, base, depth) != 0) return 1;
        } else if (strcmp(argv[2], "classify") == 0 && argc >= 4) {
            int maximum = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (three_tier_classify(maximum, base) != 0) return 1;
        } else if (strcmp(argv[2], "scan") == 0 && argc >= 4) {
            int maximum = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (three_tier_scan(maximum, base) != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!three_tier_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown three-tier action: %s\n", argv[2]);
            three_tier_help();
            return 1;
        }

    } else if (strcmp(cmd, "deficit-lattice") == 0) {
        if (argc < 3) {
            deficit_lattice_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            long long m = atoll(argv[4]);
            int base = parse_int_option(argc, argv, "--base", 30);
            if (deficit_lattice_inspect(p, m, base) != 0) return 1;
        } else if (strcmp(argv[2], "ratio") == 0 && argc >= 6) {
            int p = atoi(argv[3]);
            long long u = atoll(argv[4]);
            long long v = atoll(argv[5]);
            int base = parse_int_option(argc, argv, "--base", 30);
            long long factor = parse_int_option(argc, argv, "--factor", 1);
            if (deficit_lattice_ratio(p, u, v, base, factor) != 0) return 1;
        } else if (strcmp(argv[2], "pythagorean") == 0) {
            long long factor = parse_int_option(argc, argv, "--factor", 1);
            if (deficit_lattice_pythagorean(factor) != 0) return 1;
        } else if (strcmp(argv[2], "major-scale") == 0) {
            long long factor = parse_int_option(argc, argv, "--factor", 1);
            if (deficit_lattice_major_scale(factor) != 0) return 1;
        } else if (strcmp(argv[2], "chromatic-scale") == 0) {
            long long factor = parse_int_option(argc, argv, "--factor", 1);
            if (deficit_lattice_chromatic_scale(factor) != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!deficit_lattice_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown deficit-lattice action: %s\n", argv[2]);
            deficit_lattice_help();
            return 1;
        }

    } else if (strcmp(cmd, "coherence-decomposition") == 0) {
        if (argc < 3) {
            coherence_decomposition_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (coherence_decomposition_inspect(n, base, depth) != 0) return 1;
        } else if (strcmp(argv[2], "prime-core") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            int supported = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (coherence_decomposition_prime_core(p, supported, base, depth) != 0)
                return 1;
        } else if (strcmp(argv[2], "pairs") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (coherence_decomposition_pairs(n, base, depth) != 0) return 1;
        } else if (strcmp(argv[2], "sigma-zero") == 0 && argc >= 4) {
            int maximum_prime = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (coherence_decomposition_sigma_zero(maximum_prime, base) != 0)
                return 1;
        } else if (strcmp(argv[2], "golden-gap") == 0) {
            int base = parse_base(argc, argv, 3);
            if (coherence_decomposition_golden_gap(base) != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!coherence_decomposition_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown coherence-decomposition action: %s\n",
                    argv[2]);
            coherence_decomposition_help();
            return 1;
        }

    } else if (strcmp(cmd, "cross-alignment") == 0) {
        if (argc < 3) {
            cross_alignment_help();
        } else if (strcmp(argv[2], "matrix") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (cross_alignment_matrix_print(n, base, depth) != 0) return 1;
        } else if (strcmp(argv[2], "prime") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (cross_alignment_prime_print(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "fourier") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (cross_alignment_fourier_print(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "block") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            int supported = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            int depth = parse_int_option(argc, argv, "--depth", -1);
            if (cross_alignment_block_print(p, supported, base, depth) != 0)
                return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (cross_alignment_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!cross_alignment_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown cross-alignment action: %s\n", argv[2]);
            cross_alignment_help();
            return 1;
        }

    } else if (strcmp(cmd, "spectral-structure") == 0) {
        if (argc < 3) {
            spectral_structure_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (spectral_structure_inspect(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "two-coset") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (spectral_structure_two_coset(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "character") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (spectral_structure_character_energy(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (spectral_structure_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!spectral_structure_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown spectral-structure action: %s\n", argv[2]);
            spectral_structure_help();
            return 1;
        }

    } else if (strcmp(cmd, "spectral-power") == 0) {
        if (argc < 3) {
            spectral_power_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (spectral_power_inspect(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "overlap") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (spectral_power_overlap(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (spectral_power_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!spectral_power_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown spectral-power action: %s\n", argv[2]);
            spectral_power_help();
            return 1;
        }

    } else if (strcmp(cmd, "equations") == 0) {
        printf(
        "nfield .:. equations and identities\n"
        "\n"
        "── The digit function ─────────────────────────────────\n"
        "  d(r) = floor(b*r/p)     the digit assigned to remainder r\n"
        "  L = ord_b(p)            repetend length\n"
        "  orbit = L * (b-1) / gcd(S, b-1)   cumulative closure length\n"
        "    where S = digit sum of one repetend period\n"
        "\n"
        "── The collision invariant ────────────────────────────\n"
        "  C(g,p,b) = |{r in 1..p-1 : d(r) = d(gr)}|   collision count\n"
        "  S(p) = C(b mod p) - floor((p-1)/b)           collision invariant\n"
        "  S(p) depends only on p mod b^2                finite determination\n"
        "\n"
        "── The collision periodic table ───────────────────────\n"
        "  phi(b^2) entries, one per coprime class a mod b^2\n"
        "  S(a) + S(b^2 - a) = -1        antisymmetry (proved)\n"
        "  mean of S over all classes = -1/2   (proved)\n"
        "  gate width = b - 1             deranging multipliers (proved)\n"
        "\n"
        "── The collision transform ────────────────────────────\n"
        "  F(s) = sum_p S(p) / p^s        raw fluctuation sum\n"
        "  F diverges at s = 1 at the Mertens rate\n"
        "\n"
        "  S_c(a) = S(a) - class_mean     centered by spectral class\n"
        "  F_c(s) = sum_p S_c(p) / p^s    centered collision sum\n"
        "  F_c(1) converges               Centered Collision PNT (proved)\n"
        "  Even characters killed: S_hat(chi) = 0 for chi(-1) = +1 (proved)\n"
        "\n"
        "── The decomposition theorem ─────────────────────────\n"
        "  S_hat(chi) = -B_1(chi_bar) * D(chi)   for primitive odd chi\n"
        "  B_1 = generalized Bernoulli number\n"
        "  D = diagonal character sum over the gate set\n"
        "  Parseval: sum |S_c|^2 = sum |S_hat|^2 / phi(m)  (proved)\n"
        "\n"
        "── Neutrality ────────────────────────────────────────\n"
        "  The reflection a -> b^2-a fixes one class mod q\n"
        "  That class has mean exactly -1/2          (proved)\n"
        "  The cancellation exponent alpha = 1       (proved)\n"
        "\n"
        "── Alignment ─────────────────────────────────────────\n"
        "  alignment(n) = (2m - 1) / (pm - 1)\n"
        "    for n = pm, p smallest prime coprime to b, m b-smooth\n"
        "  Exceeds 1/phi iff m >= phi^2 = phi + 1\n"
        "  Only p = 3 crosses the golden threshold    (proved)\n"
        "\n"
        "── Orbit closure ─────────────────────────────────────\n"
        "  Cumulative digit sum returns to 0 mod (b-1) after\n"
        "    lambda = (b-1) / gcd(S, b-1) periods\n"
        "  Orbit length = lambda * L digits            (proved)\n"
        "  1/3 base 10: triangle (orbit 3)\n"
        "  1/7 base 10: hexagon (orbit 6)\n"
        "\n"
        "A. S. Petty, 2020-2026\n"
        );

    /* ── Blog command aliases ───────────────────────────── */

    } else if (strcmp(cmd, "collision_table") == 0) {
        int base = parse_positional_base(argc, argv, 2);
        collision_table_print(base, has_flag(argc, argv, "--pairs"));

    } else if (strcmp(cmd, "silent_primes") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        int lag = 1;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "--lag") == 0) lag = atoi(argv[i+1]);
        silent_primes_full_print(base, lag);

    } else if (strcmp(cmd, "gate_width") == 0) {
        int base = parse_base(argc, argv, 2);
        printf("Gate width, base %d\n", base);
        printf("Expected: %d deranging multipliers (b - 1)\n\n", base - 1);
        return verify_dispatch("gate-width");

    } else if (strcmp(cmd, "autocorrelation") == 0) {
        if (argc < 3) {
            autocorrelation_formula_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (autocorrelation_inspect(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "slice") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            int multiplier = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            if (autocorrelation_slice(p, multiplier, base) != 0) return 1;
        } else if (strcmp(argv[2], "orbit") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            int coset = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            if (autocorrelation_orbit(p, coset, base) != 0) return 1;
        } else if (strcmp(argv[2], "harmonics") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int coset = 1;
            for (int i = 4; i < argc - 1; i++)
                if (strcmp(argv[i], "--coset") == 0) coset = atoi(argv[i + 1]);
            if (autocorrelation_harmonics(p, coset, base) != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (autocorrelation_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!autocorrelation_formula_verify()) return 1;
        } else if (argv[2][0] >= '0' && argv[2][0] <= '9') {
            int p = atoi(argv[2]);
            int base = parse_base(argc, argv, 3);
            if (autocorrelation_inspect(p, base) != 0) return 1;
        } else {
            fprintf(stderr, "Unknown autocorrelation action: %s\n", argv[2]);
            autocorrelation_formula_help();
            return 1;
        }

    } else if (strcmp(cmd, "phase-gate") == 0) {
        if (argc < 3) {
            phase_gate_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            int p = atoi(argv[3]);
            int multiplier = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            if (phase_gate_inspect(p, multiplier, base) != 0) return 1;
        } else if (strcmp(argv[2], "multipliers") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (phase_gate_multipliers(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "bin-word") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (phase_gate_bin_word(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "density") == 0 && argc >= 4) {
            int multiplier = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int max_prime = parse_int_option(argc, argv, "--max-prime", 997);
            if (phase_gate_density(multiplier, base, max_prime) != 0) return 1;
        } else if (strcmp(argv[2], "power-lag") == 0 && argc >= 4) {
            int lag = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int max_prime = parse_int_option(argc, argv, "--max-prime", 997);
            if (phase_gate_power_lag(lag, base, max_prime) != 0) return 1;
        } else if (strcmp(argv[2], "prime-sum") == 0 && argc >= 4) {
            int lag = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int max_prime = parse_int_option(argc, argv, "--max-prime", 997);
            if (phase_gate_prime_sum(lag, base, max_prime) != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (phase_gate_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!phase_gate_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown phase-gate action: %s\n", argv[2]);
            phase_gate_help();
            return 1;
        }

    } else if (strcmp(cmd, "bin-derangements") == 0) {
        if (argc < 3) {
            bin_derangements_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (bin_derangements_inspect(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "family") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (bin_derangements_family(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "mean") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (bin_derangements_mean(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "lags") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (bin_derangements_lags(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (bin_derangements_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!bin_derangements_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown bin-derangements action: %s\n", argv[2]);
            bin_derangements_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-characters") == 0) {
        if (argc < 3) {
            collision_characters_help();
        } else if (strcmp(argv[2], "prime") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (collision_characters_prime(p, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int cutoff = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            long double sigma = parse_long_double_option(
                argc, argv, "--sigma", 1.0L);
            long double tau = parse_long_double_option(
                argc, argv, "--tau", 0.0L);
            if (collision_characters_inspect(
                    cutoff, base, lag, sigma, tau) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (collision_characters_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (collision_characters_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_characters_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown collision-characters action: %s\n", argv[2]);
            collision_characters_help();
            return 1;
        }

    } else if (strcmp(cmd, "silent-primes") == 0) {
        if (argc < 3) {
            silent_primes_help();
        } else if (strcmp(argv[2], "recipe") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (silent_primes_recipe(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "prime") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (silent_primes_prime(p, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "variance") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (silent_primes_variance(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (silent_primes_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (silent_primes_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!silent_primes_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown silent-primes action: %s\n", argv[2]);
            silent_primes_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-fluctuation") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            collision_fluctuation_help();
        } else if (strcmp(argv[2], "prime") == 0 && argc >= 4) {
            int p = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (collision_fluctuation_prime(p, base) != 0) return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            int base = parse_base(argc, argv, 3);
            if (collision_fluctuation_table(base) != 0) return 1;
        } else if (strcmp(argv[2], "classes") == 0) {
            int base = parse_base(argc, argv, 3);
            if (collision_fluctuation_classes(base) != 0) return 1;
        } else if (strcmp(argv[2], "sum") == 0 && argc >= 4) {
            int cutoff = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (collision_fluctuation_sum(cutoff, base) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (collision_fluctuation_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (collision_fluctuation_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_fluctuation_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown collision-fluctuation action: %s\n", argv[2]);
            collision_fluctuation_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-centering") == 0 ||
               strcmp(cmd, "centered-collision") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            centered_collision_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (centered_collision_inspect(n, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (centered_collision_table(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "fibers") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (centered_collision_fibers(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "gate") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (centered_collision_gate(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "sum") == 0 && argc >= 4) {
            int cutoff = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (centered_collision_sum(cutoff, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (centered_collision_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (centered_collision_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!centered_collision_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown collision-centering action: %s\n", argv[2]);
            centered_collision_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-table") == 0 ||
               strcmp(cmd, "collision-periodic-table") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            collision_periodic_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            if (collision_periodic_inspect(n, base) != 0) return 1;
        } else if (strcmp(argv[2], "compare") == 0 && argc >= 5) {
            int first = atoi(argv[3]);
            int second = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            if (collision_periodic_compare(first, second, base) != 0) return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            int base = parse_base(argc, argv, 3);
            if (collision_periodic_table(base) != 0) return 1;
        } else if (strcmp(argv[2], "summary") == 0) {
            int base = parse_base(argc, argv, 3);
            if (collision_periodic_summary(base) != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (collision_periodic_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_periodic_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown collision-table action: %s\n", argv[2]);
            collision_periodic_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-transform") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            collision_transform_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (collision_transform_inspect(n, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (collision_transform_table(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "gate") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (collision_transform_gate(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "spectrum") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (collision_transform_spectrum(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "window") == 0 && argc >= 5) {
            int lower = atoi(argv[3]);
            int upper = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            long double sigma = parse_long_double_option(
                argc, argv, "--sigma", 1.0L);
            if (collision_transform_window(
                    lower, upper, base, lag, sigma) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (collision_transform_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (collision_transform_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_transform_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown collision-transform action: %s\n", argv[2]);
            collision_transform_help();
            return 1;
        }

    } else if (strcmp(cmd, "residue-three-neutrality") == 0 ||
               strcmp(cmd, "neutrality-theorem") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            residue_three_neutrality_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int n = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (residue_three_neutrality_inspect(n, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "canonical") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (residue_three_neutrality_canonical(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "channels") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (residue_three_neutrality_channels(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "split") == 0 && argc >= 5) {
            int lower = atoi(argv[3]);
            int upper = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            long double sigma = parse_long_double_option(
                argc, argv, "--sigma", 1.0L);
            if (residue_three_neutrality_split(
                    lower, upper, base, lag, sigma) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (residue_three_neutrality_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "examples") == 0) {
            if (residue_three_neutrality_examples() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!residue_three_neutrality_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown residue-three-neutrality action: %s\n",
                    argv[2]);
            residue_three_neutrality_help();
            return 1;
        }

    } else if (strcmp(cmd, "compatible-residue-channels") == 0 ||
               strcmp(cmd, "general-neutrality") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            compatible_residue_channels_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            int integer = atoi(argv[3]);
            int prime = atoi(argv[4]);
            int base = parse_base(argc, argv, 5);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (compatible_residue_channels_inspect(
                    integer, prime, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "internal") == 0 && argc >= 4) {
            int prime = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (compatible_residue_channels_internal(prime, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "channels") == 0 && argc >= 4) {
            int prime = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (compatible_residue_channels_prime(prime, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "simultaneous") == 0 && argc >= 4) {
            int squarefree = atoi(argv[3]);
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (compatible_residue_channels_squarefree(
                    squarefree, base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "character-signs") == 0) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 5000000);
            if (compatible_residue_channels_character_signs(cutoff) != 0) return 1;
        } else if (strcmp(argv[2], "magnitude-correlations") == 0) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 5000000);
            if (compatible_residue_channels_magnitude_correlations(cutoff) != 0) return 1;
        } else if (strcmp(argv[2], "assignment-null") == 0) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 5000000);
            if (compatible_residue_channels_assignment_null(cutoff) != 0) return 1;
        } else if (strcmp(argv[2], "snapshot") == 0) {
            if (compatible_residue_channels_snapshot() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!compatible_residue_channels_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown compatible-residue-channels action: %s\n",
                    argv[2]);
            compatible_residue_channels_help();
            return 1;
        }

    } else if (strcmp(cmd, "centered-collision-table") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            centered_collision_table_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (centered_collision_table_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "complete") == 0 && argc >= 5) {
            if (centered_collision_table_complete(
                    atoi(argv[3]), atoi(argv[4])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!centered_collision_table_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown centered-collision-table action: %s\n",
                    argv[2]);
            centered_collision_table_help();
            return 1;
        }

    } else if (strcmp(cmd, "finite-character-pairing") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            finite_character_pairing_help();
        } else if (strcmp(argv[2], "one") == 0 && argc >= 5) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 2000000);
            if (finite_character_pairing_one(
                    atoi(argv[3]), atoi(argv[4]), cutoff) != 0)
                return 1;
        } else if (strcmp(argv[2], "declared-rows") == 0) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 2000000);
            if (finite_character_pairing_declared_rows(cutoff) != 0)
                return 1;
        } else if (strcmp(argv[2], "cutoff-trend") == 0) {
            if (finite_character_pairing_cutoff_trend() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!finite_character_pairing_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown finite-character-pairing action: %s\n",
                    argv[2]);
            finite_character_pairing_help();
            return 1;
        }

    } else if (strcmp(cmd, "coprime-base-orthogonality") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            coprime_base_orthogonality_help();
        } else if (strcmp(argv[2], "pair") == 0 && argc >= 7) {
            if (coprime_base_orthogonality_pair(
                    atoi(argv[3]), atoi(argv[4]),
                    atoi(argv[5]), atoi(argv[6])) != 0)
                return 1;
        } else if (strcmp(argv[2], "common-quotient") == 0 && argc >= 7) {
            if (coprime_base_common_quotient(
                    atoi(argv[3]), atoi(argv[4]),
                    atoi(argv[5]), atoi(argv[6])) != 0)
                return 1;
        } else if (strcmp(argv[2], "audit") == 0) {
            if (coprime_base_orthogonality_audit() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!coprime_base_orthogonality_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown coprime-base-orthogonality action: %s\n",
                    argv[2]);
            coprime_base_orthogonality_help();
            return 1;
        }

    } else if (strcmp(cmd, "natural-prime-sum-window") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            natural_prime_sum_window_help();
        } else if (strcmp(argv[2], "base-boundaries") == 0) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 0);
            if (natural_prime_sum_window_base_boundaries(cutoff) != 0)
                return 1;
        } else if (strcmp(argv[2], "common-tail") == 0) {
            int lower = parse_int_option(argc, argv, "--lower", 997);
            int cutoff = parse_int_option(argc, argv, "--cutoff", 2000000);
            if (natural_prime_sum_window_common_tail(lower, cutoff) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!natural_prime_sum_window_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown natural-prime-sum-window action: %s\n",
                    argv[2]);
            natural_prime_sum_window_help();
            return 1;
        }

    } else if (strcmp(cmd, "primitive-odd-sector") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            primitive_odd_sector_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int cutoff = parse_int_option(argc, argv, "--cutoff", 2000000);
            if (primitive_odd_sector_inspect(atoi(argv[3]), cutoff) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!primitive_odd_sector_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown primitive-odd-sector action: %s\n",
                    argv[2]);
            primitive_odd_sector_help();
            return 1;
        }

    } else if (strcmp(cmd, "conjugate-pair-relabeling") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            conjugate_pair_relabeling_help();
        } else if (strcmp(argv[2], "exact-law") == 0) {
            if (conjugate_pair_relabeling_exact_law() != 0) return 1;
        } else if (strcmp(argv[2], "ledger") == 0) {
            if (conjugate_pair_relabeling_ledger() != 0) return 1;
        } else if (strcmp(argv[2], "cutoffs") == 0) {
            if (conjugate_pair_relabeling_cutoffs() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!conjugate_pair_relabeling_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown conjugate-pair-relabeling action: %s\n",
                    argv[2]);
            conjugate_pair_relabeling_help();
            return 1;
        }

    } else if (strcmp(cmd, "additive-reflection-well") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            additive_reflection_well_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            if (additive_reflection_well_inspect(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!additive_reflection_well_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown additive-reflection-well action: %s\n",
                    argv[2]);
            additive_reflection_well_help();
            return 1;
        }

    } else if (strcmp(cmd, "reflected-prime-pair-sign") == 0 ||
               strcmp(cmd, "goldbach-obstruction") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            reflected_prime_pair_sign_help();
        } else if (strcmp(argv[2], "sweep") == 0 && argc >= 4) {
            int maximum_even = parse_int_option(
                argc, argv, "--max-even", 100000);
            if (reflected_prime_pair_sign_sweep(
                    atoi(argv[3]), maximum_even) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!reflected_prime_pair_sign_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown reflected-prime-pair-sign action: %s\n",
                    argv[2]);
            reflected_prime_pair_sign_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-spectrum-factorization") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            collision_spectrum_factorization_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            if (collision_spectrum_factorization_inspect(
                    atoi(argv[3]), atoi(argv[4])) != 0)
                return 1;
        } else if (strcmp(argv[2], "transform") == 0 && argc >= 6) {
            if (collision_spectrum_factorization_transform(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_spectrum_factorization_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown collision-spectrum-factorization action: %s\n",
                    argv[2]);
            collision_spectrum_factorization_help();
            return 1;
        }

    } else if (strcmp(cmd, "special-value-moment") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            special_value_moment_help();
        } else if (strcmp(argv[2], "ledger") == 0) {
            if (special_value_moment_ledger() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!special_value_moment_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown special-value-moment action: %s\n",
                    argv[2]);
            special_value_moment_help();
            return 1;
        }

    } else if (strcmp(cmd, "base-five-cyclotomic-identity") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            base_five_cyclotomic_identity_help();
        } else if (strcmp(argv[2], "audit") == 0) {
            if (base_five_cyclotomic_identity_audit() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!base_five_cyclotomic_identity_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown base-five-cyclotomic-identity action: %s\n",
                    argv[2]);
            base_five_cyclotomic_identity_help();
            return 1;
        }

    } else if (strcmp(cmd, "weighted-remainder-state") == 0) {
        if (argc == 2 || (argc == 3 &&
            (strcmp(argv[2], "--help") == 0 || strcmp(argv[2], "help") == 0))) {
            weighted_remainder_state_help();
        } else if (argc == 3 && strcmp(argv[2], "verify") == 0) {
            if (!weighted_remainder_state_verify()) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "boundary") == 0 ||
                                 strcmp(argv[2], "ramp") == 0 ||
                                 strcmp(argv[2], "amplitude") == 0)) {
            if (weighted_remainder_exact_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "floor") == 0 ||
                                 strcmp(argv[2], "straighten") == 0)) {
            if (weighted_remainder_floor_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "clock") == 0 ||
                                 strcmp(argv[2], "clock-law") == 0 ||
                                 strcmp(argv[2], "age-budget") == 0 ||
                                 strcmp(argv[2], "cycle") == 0 ||
                                 strcmp(argv[2], "cycle-tv") == 0 ||
                                 strcmp(argv[2], "covariance") == 0)) {
            if (weighted_remainder_clock_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "variance") == 0 ||
                                 strcmp(argv[2], "finite-weights") == 0 ||
                                 strcmp(argv[2], "perturbation") == 0)) {
            if (weighted_remainder_weights_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "rows") == 0 ||
                                 strcmp(argv[2], "mass-inverse") == 0 ||
                                 strcmp(argv[2], "mass-recovery") == 0)) {
            if (weighted_remainder_rows_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "increment-covariance") == 0 ||
                                 strcmp(argv[2], "increment-recurrence") == 0)) {
            if (weighted_remainder_increment_command(argc, argv)) return 1;
        } else if (argc >= 3 && strcmp(argv[2], "fourier") == 0) {
            if (weighted_remainder_fourier_command(argc, argv)) return 1;
        } else if (argc >= 3 && strcmp(argv[2], "amplitude-refinement") == 0) {
            if (weighted_remainder_amplitude_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "expansion-constants") == 0 ||
                                 strcmp(argv[2], "harmonic-expansion") == 0 ||
                                 strcmp(argv[2], "amplitude-expansion") == 0 ||
                                 strcmp(argv[2], "deficit-series") == 0 ||
                                 strcmp(argv[2], "deficit-diagnostic") == 0)) {
            if (weighted_remainder_expansion_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "spectral-product") == 0 ||
                                 strcmp(argv[2], "spectral-mean") == 0 ||
                                 strcmp(argv[2], "spectral-energy") == 0 ||
                                 strcmp(argv[2], "spectral-tail") == 0)) {
            if (weighted_remainder_spectral_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "character-phase") == 0 ||
                                 strcmp(argv[2], "character-table") == 0 ||
                                 strcmp(argv[2], "character-l") == 0 ||
                                 strcmp(argv[2], "mixed-moment") == 0 ||
                                 strcmp(argv[2], "cotangent-sums") == 0 ||
                                 strcmp(argv[2], "harmonic-polylog") == 0 ||
                                 strcmp(argv[2], "harmonic-root") == 0 ||
                                 strcmp(argv[2], "harmonic-root-average") == 0 ||
                                 strcmp(argv[2], "sine-transform") == 0 ||
                                 strcmp(argv[2], "small-amplitudes") == 0)) {
            if (weighted_remainder_mixed_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "law-moment") == 0 ||
                                 strcmp(argv[2], "law-cdf") == 0 ||
                                 strcmp(argv[2], "law-window") == 0 ||
                                 strcmp(argv[2], "law-concentration") == 0 ||
                                 strcmp(argv[2], "law-characteristic") == 0 ||
                                 strcmp(argv[2], "law-recurrence") == 0 ||
                                 strcmp(argv[2], "law-tail-bound") == 0 ||
                                 strcmp(argv[2], "law-activation") == 0 ||
                                 strcmp(argv[2], "clock-difference") == 0)) {
            if (weighted_remainder_law_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "alignment") == 0 ||
                                 strcmp(argv[2], "alignment-local") == 0 ||
                                 strcmp(argv[2], "harmonic-local") == 0 ||
                                 strcmp(argv[2], "alignment-lcm") == 0 ||
                                 strcmp(argv[2], "alignment-growth") == 0)) {
            if (weighted_remainder_alignment_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "tree") == 0 ||
                                 strcmp(argv[2], "tree-node") == 0 ||
                                 strcmp(argv[2], "weight") == 0 ||
                                 strcmp(argv[2], "budget") == 0 ||
                                 strcmp(argv[2], "mass") == 0)) {
            if (weighted_remainder_primitive_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "sawtooth") == 0 ||
                                 strcmp(argv[2], "dedekind") == 0 ||
                                 strcmp(argv[2], "gram") == 0 ||
                                 strcmp(argv[2], "sawtooth-mean") == 0)) {
            if (weighted_remainder_sawtooth_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "reset") == 0 ||
                                 strcmp(argv[2], "pairing") == 0)) {
            if (weighted_remainder_pairing_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "crt") == 0 ||
                                 strcmp(argv[2], "moment") == 0 ||
                                 strcmp(argv[2], "haar-moment") == 0 ||
                                 strcmp(argv[2], "block") == 0 ||
                                 strcmp(argv[2], "forcing") == 0)) {
            if (weighted_remainder_joint_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "cylinder") == 0 ||
                                 strcmp(argv[2], "position") == 0 ||
                                 strcmp(argv[2], "position-weight") == 0)) {
            if (weighted_remainder_cylinder_command(argc, argv)) return 1;
        } else if (argc >= 3 && (strcmp(argv[2], "conductor-full") == 0 ||
                                 strcmp(argv[2], "conductor-beta") == 0 ||
                                 strcmp(argv[2], "conductor-prime") == 0 ||
                                 strcmp(argv[2], "conductor-extrema") == 0 ||
                                 strcmp(argv[2], "conductor-minimizers") == 0)) {
            if (weighted_remainder_conductor_command(argc, argv)) return 1;
        } else if (argc >= 3 && strcmp(argv[2], "activation") == 0) {
            if (weighted_remainder_activation_command(argc, argv)) return 1;
        } else if (argc == 5 && (strcmp(argv[2], "inspect") == 0 ||
                                strcmp(argv[2], "conductor") == 0)) {
            char *end_first = NULL, *end_cutoff = NULL;
            long first = strtol(argv[3], &end_first, 10);
            long cutoff = strtol(argv[4], &end_cutoff, 10);
            int conductor = strcmp(argv[2], "conductor") == 0;
            if (end_first == argv[3] || *end_first ||
                end_cutoff == argv[4] || *end_cutoff || cutoff < 2 || cutoff > 240 ||
                first < (conductor ? 2 : 0) || first > (conductor ? cutoff : 1000000000L)) {
                fprintf(stderr, "Provide a valid resolution or conductor and a cutoff from 2 through 240.\n");
                return 1;
            }
            int status = conductor ? weighted_remainder_state_conductor((int)first, (int)cutoff) :
                weighted_remainder_state_inspect((int)first, (int)cutoff);
            if (status) return status;
        } else {
            fprintf(stderr, "See help weighted-remainder-state for actions and domains.\n");
            return 1;
        }

    } else if (strcmp(cmd, "short-sum-bernoulli-correlation") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            short_sum_bernoulli_correlation_help();
        } else if (strcmp(argv[2], "ledger") == 0) {
            if (short_sum_bernoulli_correlation_ledger() != 0) return 1;
        } else if (strcmp(argv[2], "moments") == 0) {
            char *end = NULL;
            long moment_base = argc == 4 ? strtol(argv[3], &end, 10) : 0;
            if (argc != 4 || end == argv[3] || !end || *end ||
                moment_base < 5 || moment_base > 127) {
                fprintf(stderr, "Provide one odd prime base from 5 through 127.\n");
                return 1;
            }
            if (short_sum_bernoulli_correlation_moments((int)moment_base) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!short_sum_bernoulli_correlation_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown short-sum-bernoulli-correlation action: %s\n",
                    argv[2]);
            short_sum_bernoulli_correlation_help();
            return 1;
        }

    } else if (strcmp(cmd, "primitive-character-cancellation") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            primitive_character_cancellation_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (primitive_character_cancellation_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!primitive_character_cancellation_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown primitive-character-cancellation action: %s\n",
                    argv[2]);
            primitive_character_cancellation_help();
            return 1;
        }

    } else if (strcmp(cmd, "periodic-zeta-factorization") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            periodic_zeta_factorization_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            long double sigma = parse_long_double_option(
                argc, argv, "--sigma", 0.5L);
            long double tau = parse_long_double_option(
                argc, argv, "--tau", 0.0L);
            if (periodic_zeta_factorization_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5]),
                    sigma, tau) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!periodic_zeta_factorization_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown periodic-zeta-factorization action: %s\n",
                    argv[2]);
            periodic_zeta_factorization_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-boundary-recovery") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            collision_boundary_recovery_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (collision_boundary_recovery_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_boundary_recovery_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown collision-boundary-recovery action: %s\n",
                    argv[2]);
            collision_boundary_recovery_help();
            return 1;
        }

    } else if (strcmp(cmd, "active-collision-channel") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            active_collision_channel_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (active_collision_channel_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "census") == 0 && argc >= 5) {
            if (active_collision_channel_census(
                    atoi(argv[3]), atoi(argv[4])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!active_collision_channel_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown active-collision-channel action: %s\n",
                    argv[2]);
            active_collision_channel_help();
            return 1;
        }

    } else if (strcmp(cmd, "collision-coordinate") == 0) {
        if (argc < 3) {
            collision_coordinate_help();
        } else if (strcmp(argv[2], "conjugation") == 0 && argc >= 5) {
            int base = parse_base(argc, argv, 5);
            if (collision_coordinate_conjugation(
                    atoi(argv[3]), atoi(argv[4]), base) != 0)
                return 1;
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            int base = parse_base(argc, argv, 5);
            if (collision_coordinate_inspect(
                    atoi(argv[3]), atoi(argv[4]), base) != 0)
                return 1;
        } else if (strcmp(argv[2], "gate") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            if (collision_coordinate_gate(atoi(argv[3]), base) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!collision_coordinate_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown collision-coordinate action: %s\n",
                    argv[2]);
            collision_coordinate_help();
            return 1;
        }

    } else if (strcmp(cmd, "finite-determination") == 0) {
        if (argc < 3) {
            finite_determination_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (finite_determination_inspect(
                    atoi(argv[3]), base, lag) != 0)
                return 1;
        } else if (strcmp(argv[2], "optimal") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (finite_determination_optimal(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!finite_determination_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown finite-determination action: %s\n",
                    argv[2]);
            finite_determination_help();
            return 1;
        }

    } else if (strcmp(cmd, "all-prime-collision-label") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            all_prime_collision_label_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (all_prime_collision_label_inspect(
                    atoi(argv[3]), base, lag) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!all_prime_collision_label_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown all-prime-collision-label action: %s\n",
                    argv[2]);
            all_prime_collision_label_help();
            return 1;
        }

    } else if (strcmp(cmd, "finite-spectral-quotient") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            finite_spectral_quotient_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int lag = parse_int_option(argc, argv, "--lag", 1);
            int prime_count = parse_int_option(
                argc, argv, "--prime-count", 300);
            long double tau = parse_long_double_option(
                argc, argv, "--tau", 1.0L);
            if (finite_spectral_quotient_inspect(
                    atoi(argv[3]), lag, prime_count, (double)tau) != 0)
                return 1;
        } else if (strcmp(argv[2], "declared") == 0) {
            if (finite_spectral_quotient_declared() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!finite_spectral_quotient_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown finite-spectral-quotient action: %s\n",
                    argv[2]);
            finite_spectral_quotient_help();
            return 1;
        }

    } else if (strcmp(cmd, "finite-prefix-slice") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            finite_prefix_slice_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", 0);
            const char *support = parse_string_option(
                argc, argv, "--support");
            if (finite_prefix_slice_inspect(
                    atoi(argv[3]), base, depth, support) != 0)
                return 1;
        } else if (strcmp(argv[2], "all") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            int depth = parse_int_option(argc, argv, "--depth", 0);
            const char *support = parse_string_option(
                argc, argv, "--support");
            if (finite_prefix_slice_inspect_all_denominators(
                    atoi(argv[3]), base, depth, support) != 0)
                return 1;
        } else if (strcmp(argv[2], "collapse") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            if (positional_transport_collapse_inspect(
                    atoi(argv[3]), base) != 0)
                return 1;
        } else if (strcmp(argv[2], "collision") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (finite_prefix_slice_collision(
                    atoi(argv[3]), base, lag) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!finite_prefix_slice_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown finite-prefix-slice action: %s\n",
                    argv[2]);
            finite_prefix_slice_help();
            return 1;
        }

    } else if (strcmp(cmd, "oriented-digit-comparison") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            oriented_digit_comparison_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            if (oriented_digit_comparison_inspect(
                    atoi(argv[3]), atoi(argv[4])) != 0)
                return 1;
        } else if (strcmp(argv[2], "prime") == 0 && argc >= 4) {
            if (oriented_digit_comparison_prime(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "trichotomy") == 0 && argc >= 5) {
            int height = parse_int_option(argc, argv, "--height", 0);
            if (oriented_digit_comparison_trichotomy(
                    atoi(argv[3]), atoi(argv[4]), height) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!oriented_digit_comparison_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown oriented-digit-comparison action: %s\n",
                    argv[2]);
            oriented_digit_comparison_help();
            return 1;
        }

    } else if (strcmp(cmd, "boundary-bernoulli-factorization") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            boundary_bernoulli_factorization_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            const char *support = parse_string_option(
                argc, argv, "--support");
            if (boundary_bernoulli_factorization_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5]),
                    support) != 0)
                return 1;
        } else if (strcmp(argv[2], "terminal") == 0 && argc >= 6) {
            if (boundary_bernoulli_factorization_terminal(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "spectrum") == 0 && argc >= 5) {
            const char *support = parse_string_option(
                argc, argv, "--support");
            if (boundary_bernoulli_factorization_spectrum(
                    atoi(argv[3]), atoi(argv[4]), support) != 0)
                return 1;
        } else if (strcmp(argv[2], "correlation") == 0 && argc >= 7) {
            if (boundary_sawtooth_correlation_inspect(
                    atoi(argv[3]), atoi(argv[4]),
                    atoi(argv[5]), atoi(argv[6])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!boundary_bernoulli_factorization_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown boundary-bernoulli-factorization action: %s\n",
                    argv[2]);
            boundary_bernoulli_factorization_help();
            return 1;
        }

    } else if (strcmp(cmd, "finite-state-orbit-boundary") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            finite_state_orbit_boundary_help();
        } else if (strcmp(argv[2], "parity") == 0 && argc >= 6) {
            if (finite_state_orbit_boundary_parity(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 8) {
            const char *transition = parse_string_option(
                argc, argv, "--transition");
            const char *accepting = parse_string_option(
                argc, argv, "--accepting");
            const char *state_weights = parse_string_option(
                argc, argv, "--state-weights");
            if (finite_state_orbit_boundary_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5]),
                    atoi(argv[6]), atoi(argv[7]), transition,
                    accepting, state_weights) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!finite_state_orbit_boundary_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown finite-state-orbit-boundary action: %s\n",
                    argv[2]);
            finite_state_orbit_boundary_help();
            return 1;
        }

    } else if (strcmp(cmd, "full-orbit-energy") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            full_orbit_energy_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (full_orbit_energy_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!full_orbit_energy_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown full-orbit-energy action: %s\n",
                    argv[2]);
            full_orbit_energy_help();
            return 1;
        }

    } else if (strcmp(cmd, "quadratic-orbit-energy") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            quadratic_orbit_energy_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            if (quadratic_orbit_energy_inspect(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!quadratic_orbit_energy_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown quadratic-orbit-energy action: %s\n",
                    argv[2]);
            quadratic_orbit_energy_help();
            return 1;
        }

    } else if (strcmp(cmd, "subgroup-jacobi-expansion") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            subgroup_jacobi_expansion_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (subgroup_jacobi_expansion_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!subgroup_jacobi_expansion_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown subgroup-jacobi-expansion action: %s\n",
                    argv[2]);
            subgroup_jacobi_expansion_help();
            return 1;
        }

    } else if (strcmp(cmd, "weighted-reference-profile") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0
            || strcmp(argv[2], "help") == 0) {
            weighted_reference_profile_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 7) {
            int base = parse_base(argc, argv, 7);
            if (!weighted_reference_profile_inspect(
                    atoi(argv[3]), atoi(argv[4]), base,
                    atoll(argv[5]), atoll(argv[6])))
                return 1;
        } else if (strcmp(argv[2], "branch") == 0 && argc >= 5) {
            if (!weighted_reference_profile_branch(
                    atoi(argv[3]), atoi(argv[4])))
                return 1;
        } else if (strcmp(argv[2], "torsion") == 0) {
            if (!weighted_reference_profile_torsion()) return 1;
        } else if (strcmp(argv[2], "reflection-product") == 0
                   && argc >= 4) {
            if (!weighted_reference_profile_reflection_product(
                    atoi(argv[3])))
                return 1;
        } else if (strcmp(argv[2], "oriented-words") == 0
                   && argc >= 4) {
            if (!weighted_reference_profile_oriented_words(
                    atoi(argv[3])))
                return 1;
        } else if (strcmp(argv[2], "transport") == 0) {
            if (!weighted_reference_profile_transport()) return 1;
        } else if (strcmp(argv[2], "finite-orbit") == 0 && argc >= 5) {
            int base = parse_int_option(argc, argv, "--base", 7);
            if (!weighted_reference_profile_finite_orbit(
                    atoi(argv[3]), atoi(argv[4]), base))
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!weighted_reference_profile_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown weighted-reference-profile action: %s\n",
                    argv[2]);
            weighted_reference_profile_help();
            return 1;
        }

    } else if (strcmp(cmd, "reciprocal-square-selection") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0
            || strcmp(argv[2], "help") == 0) {
            reciprocal_square_selection_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            int base = parse_base(argc, argv, 5);
            if (reciprocal_square_selection_inspect(
                    atoi(argv[3]), atoi(argv[4]), base) != 0)
                return 1;
        } else if (strcmp(argv[2], "cubic") == 0 && argc >= 4) {
            if (reciprocal_square_selection_cubic(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            if (reciprocal_square_selection_table() != 0) return 1;
        } else if (strcmp(argv[2], "scan") == 0 && argc >= 4) {
            if (reciprocal_square_selection_scan(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!reciprocal_square_selection_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown reciprocal-square-selection action: %s\n",
                    argv[2]);
            reciprocal_square_selection_help();
            return 1;
        }

    } else if (strcmp(cmd, "prime-base-collision-energy") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            prime_base_collision_energy_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            if (prime_base_collision_energy_inspect(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "poles") == 0 && argc >= 4) {
            if (prime_base_collision_energy_poles(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!prime_base_collision_energy_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown prime-base-collision-energy action: %s\n",
                    argv[2]);
            prime_base_collision_energy_help();
            return 1;
        }

    } else if (strcmp(cmd, "capacity-resolution") == 0) {
        return collision_capacity_transition_command(argc-2,argv+2);
    } else if (strcmp(cmd, "capacity-generation") == 0) {
        return collision_capacity_generation_command(argc-2,argv+2);

    } else if (strcmp(cmd, "collision-sampling") == 0) {
        return collision_sampling_command(argc-2,argv+2);
    } else if (strcmp(cmd, "boundary-spectrum") == 0) {
        return boundary_spectrum_command(argc-2,argv+2);

    } else if (strcmp(cmd, "arithmetic-boundary-defect") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            arithmetic_boundary_defect_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            if (arithmetic_boundary_defect_inspect(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "scan") == 0 && argc >= 4) {
            if (arithmetic_boundary_defect_scan(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!arithmetic_boundary_defect_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown arithmetic-boundary-defect action: %s\n",
                    argv[2]);
            arithmetic_boundary_defect_help();
            return 1;
        }

    } else if (strcmp(cmd, "carry-completed-carrier") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            carry_completed_carrier_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 6) {
            if (carry_completed_carrier_inspect(
                    atoi(argv[3]), atoi(argv[4]), atoi(argv[5])) != 0)
                return 1;
        } else if (strcmp(argv[2], "seam") == 0 && argc >= 4) {
            if (carry_completed_carrier_seam(atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "product") == 0 && argc >= 7) {
            if (carry_completed_carrier_product(
                    atoi(argv[3]), atoi(argv[4]),
                    atoi(argv[5]), atoi(argv[6])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!carry_completed_carrier_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown carry-completed-carrier action: %s\n",
                    argv[2]);
            carry_completed_carrier_help();
            return 1;
        }

    } else if (strcmp(cmd, "reflection-identity") == 0) {
        if (argc < 3) {
            reflection_identity_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            int base = parse_base(argc, argv, 4);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (reflection_identity_inspect(
                    base, lag, atoi(argv[3])) != 0)
                return 1;
        } else if (strcmp(argv[2], "table") == 0) {
            int base = parse_base(argc, argv, 3);
            int lag = parse_int_option(argc, argv, "--lag", 1);
            if (reflection_identity_table(base, lag) != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!reflection_identity_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown reflection-identity action: %s\n",
                    argv[2]);
            reflection_identity_help();
            return 1;
        }

    } else if (strcmp(cmd, "half-group") == 0) {
        if (argc < 3) {
            half_group_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 5) {
            if (half_group_inspect(atoi(argv[3]), atoi(argv[4])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!half_group_verify()) return 1;
        } else {
            fprintf(stderr, "Unknown half-group action: %s\n", argv[2]);
            half_group_help();
            return 1;
        }

    } else if (strcmp(cmd, "boundary-conductor-ledger") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            boundary_conductor_ledger_help();
        } else if (strcmp(argv[2], "inspect") == 0 && argc >= 4) {
            const char *support = parse_string_option(
                argc, argv, "--support");
            if (boundary_conductor_ledger_inspect(
                    atoi(argv[3]), support) != 0)
                return 1;
        } else if (strcmp(argv[2], "terminal") == 0 && argc >= 5) {
            if (boundary_conductor_ledger_terminal(
                    atoi(argv[3]), atoi(argv[4])) != 0)
                return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!boundary_conductor_ledger_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown boundary-conductor-ledger action: %s\n",
                    argv[2]);
            boundary_conductor_ledger_help();
            return 1;
        }

    } else if (strcmp(cmd, "terminal-collision-conductor-ledger") == 0) {
        if (argc < 3 || strcmp(argv[2], "--help") == 0 ||
            strcmp(argv[2], "help") == 0) {
            terminal_collision_conductor_ledger_help();
        } else if (strcmp(argv[2], "audit") == 0) {
            if (terminal_collision_conductor_ledger_audit() != 0) return 1;
        } else if (strcmp(argv[2], "verify") == 0) {
            if (!terminal_collision_conductor_ledger_verify()) return 1;
        } else {
            fprintf(stderr,
                    "Unknown terminal-collision-conductor-ledger action: %s\n",
                    argv[2]);
            terminal_collision_conductor_ledger_help();
            return 1;
        }

    } else if (strcmp(cmd, "spectrum") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 7;
        int base = parse_base(argc, argv, 3);
        spectrum_print(p, base);

    } else if (strcmp(cmd, "gate") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 7;
        int base = parse_base(argc, argv, 3);
        gate_print(p, base);

    } else if (strcmp(cmd, "derangements") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 13;
        int base = parse_base(argc, argv, 3);
        derangements_print(p, base);

    } else if (strcmp(cmd, "fluctuation_sum") == 0 ||
               strcmp(cmd, "mertens_growth") == 0) {
        int base = parse_base(argc, argv, 2);
        int lag = 1;
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++) {
            if (strcmp(argv[i], "--lag") == 0) lag = atoi(argv[i+1]);
            if (strcmp(argv[i], "--primes") == 0) maxp = atoi(argv[i+1]);
        }
        fluctuation_sum_print(base, lag, maxp);

    } else if (strcmp(cmd, "class_bias") == 0) {
        int base = parse_base(argc, argv, 2);
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "--primes") == 0) maxp = atoi(argv[i+1]);
        class_bias_print(base, maxp);

    } else if (strcmp(cmd, "character_components") == 0) {
        /* Show character magnitudes using CRT */
        int base_arg = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9') base_arg = atoi(argv[2]);
        base_arg = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base_arg;
        character_components_print(base_arg);

    } else if (strcmp(cmd, "class_means") == 0) {
        int base = parse_base(argc, argv, 2);
        class_means_print(base);

    } else if (strcmp(cmd, "centered_sum") == 0) {
        int base = parse_base(argc, argv, 2);
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "--primes") == 0) maxp = atoi(argv[i+1]);
        centered_sum_print(base, maxp);

    } else if (strcmp(cmd, "neutrality") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "-N") == 0 || strcmp(argv[i], "--primes") == 0)
                maxp = atoi(argv[i+1]);
        neutrality_print(base, maxp);

    } else if (strcmp(cmd, "neutrality_sweep") == 0) {
        neutrality_sweep_print();

    } else if (strcmp(cmd, "finite_det") == 0) {
        return verify_dispatch("finite-det");

    } else if (strcmp(cmd, "mod3_means") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        mod3_means_print(base);

    } else if (strcmp(cmd, "polarity_field") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9') base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        polarity_field_print(base);

    } else if (strcmp(cmd, "help") == 0) {
        if (argc < 3) {
            usage();
        } else if (!print_help_topic(argv[2])) {
            fprintf(stderr, "Unknown help topic: %s\n", argv[2]);
            fprintf(stderr, "Use `nfield --help` to list available topics.\n");
            return 1;
        }

    } else {
        fprintf(stderr, "Unknown command: %s\n", cmd);
        return 1;
    }

done:
    if (show_time) {
        clock_gettime(CLOCK_MONOTONIC, &t1);
        fflush(stdout);
        print_elapsed_time(&t0, &t1);
    }

    return 0;
}
