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
#include "nfield.h"

static void usage(void)
{
    fprintf(stderr,
        "nfield .:. fractional field analysis engine\n"
        "A. S. Petty, 2025-2026\n"
        "\n"
        "Usage:\n"
        "  nfield <n> [--base <b>]                   Analyze a single n\n"
        "  nfield field <n> [--base <b>]             Show the full fractional field\n"
        "  nfield polar <n> [--base <b>]             Field content + cumulative polarity\n"
        "  nfield survey <max> [--base <b>] [--csv]  Survey n=2..max\n"
        "  nfield range <min> <max> [--base <b>] [--csv]\n"
        "                                            Survey a range\n"
        "  nfield align <n> [--base <b>]             Compute alignment\n"
        "  nfield table1                             Reproduce paper Table 1\n"
        "  nfield decompose <n> [--base <b>]         Show alpha, sigma, F\n"
        "  nfield spectral <p> [--base <b>]          Show Phi(k) spectrum\n"
        "  nfield equations                          Show invariant definitions\n"
        "\n"
        "Any command accepts --time to print elapsed time to stderr.\n"
    );
}

static int parse_base(int argc, char **argv, int start)
{
    for (int i = start; i < argc - 1; i++) {
        if (strcmp(argv[i], "--base") == 0)
            return atoi(argv[i + 1]);
    }
    return 10;
}

static int has_flag(int argc, char **argv, const char *flag)
{
    for (int i = 1; i < argc; i++)
        if (strcmp(argv[i], flag) == 0)
            return 1;
    return 0;
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        usage();
        return 1;
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

    if (strcmp(cmd, "analyze") == 0 && argc >= 3) {
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

    } else if (strcmp(cmd, "table1") == 0) {
        table1();

    } else if (strcmp(cmd, "align") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        double a = alignment_exact(n, base);
        printf("alignment(%d, base=%d) = %.6f\n", n, base, a);

    } else if (strcmp(cmd, "spectral") == 0 && argc >= 3) {
        int p    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        spectral_print(p, base);

    } else if (strcmp(cmd, "decompose") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        decompose_print(n, base);

    } else if (strcmp(cmd, "equations") == 0) {
        printf(
        "nfield .:. invariant definitions\n"
        "\n"
        "Given integer n and base b, the fractional field is\n"
        "  F(n) = { k/n : k = 1, ..., n-1 }\n"
        "Each k/n is expanded in base b to obtain its repetend (periodic block).\n"
        "\n"
        "── Repetend ───────────────────────────────────────────\n"
        "  1/n in base b has a repetend of length L = ord_p(b)\n"
        "  where p is the largest prime factor of n coprime to b.\n"
        "\n"
        "── Row invariants (per k) ─────────────────────────────\n"
        "  rot_index   rotation offset: k/n's cycle is base cycle shifted by rot_index\n"
        "  alignment   fraction of positions where k/n's cycle matches 1/n's cycle\n"
        "  curvature   mean |d[i] - d[i+1 mod L]| over the cycle digits\n"
        "\n"
        "── Primitive invariants (per n) ────────────────────────\n"
        "  C(n)   curvature      normalized total variation of the base repetend\n"
        "  R(n)   coherence      concentration of the (Z/nZ)* rotation action\n"
        "  H3(n)  harmonicity    1 if ord_n(b) %% 3 == 0, else 0\n"
        "  rot_sigma             equidistribution measure of rotation indices\n"
        "\n"
        "── Composite invariants (exploratory) ─────────────────\n"
        "  S(n)   structure    R/C + H3\n"
        "  B(n)   burden       C/L + (1-R) + (1-H3) + rot_sigma/L\n"
        "  D(n)   depth        1/S + B\n"
        "  These combinations are useful for classification but\n"
        "  are not uniquely determined by the mathematics.\n"
        "\n"
        "── Alignment (proven) ─────────────────────────────────\n"
        "  alignment(n)  mean of row alignments across F(n)\n"
        "\n"
        "  For n = pm with p the smallest prime not dividing b,\n"
        "  ord_p(b) = 1, and m is b-smooth:\n"
        "\n"
        "    alignment(n) = (2m - 1) / (pm - 1)\n"
        "\n"
        "  This exceeds 1/phi iff m >= phi^2 = phi + 1\n"
        "  (when p = 3, the unique prime selected by the golden ratio).\n"
        "\n"
        "── Self-referential identity ──────────────────────────\n"
        "  tau = 1/phi is the unique threshold satisfying:\n"
        "    tau^2 + tau = 1      (golden ratio equation)\n"
        "    tau^4 = 2 - 3*tau    (selects p = 3 algebraically)\n"
        "\n"
        "  Reference: A. S. Petty, 'Why the Golden Ratio Selects\n"
        "  the Prime Three', 2020.\n"
        );

    } else {
        usage();
        return 1;
    }

done:
    if (show_time) {
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double elapsed = (t1.tv_sec - t0.tv_sec)
                       + (t1.tv_nsec - t0.tv_nsec) / 1e9;
        fprintf(stderr, "%.3fs\n", elapsed);
    }

    return 0;
}
