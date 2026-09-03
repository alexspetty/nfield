/*
 * output.c: Display routines for fields, invariants, and surveys.
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "nfield.h"

#ifdef NFIELD_PARALLEL
#include <omp.h>
#endif

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

/* ── field display ───────────────────────────────────────── */

static void print_digits(const int *d, int len, int base)
{
    if (base <= 10) {
        for (int j = 0; j < len; j++) printf("%d", d[j]);
    } else {
        for (int j = 0; j < len; j++) {
            if (j > 0) printf(".");
            printf("%d", d[j]);
        }
    }
}

static const char *rep_type(const Repetend *r)
{
    if (r->cycle_len == 0) return "open";
    if (r->cycle_start == 0) return "closed";
    return "mixed";
}

void field_print(const Field *f)
{
    int L = f->base_rep.cycle_len;
    int b = f->base;

    /* Compute orbit length: L * (b-1) / gcd(digit_sum, b-1) */
    int orbit_len = L;
    if (L > 0) {
        int digit_sum = 0;
        for (int j = f->base_rep.cycle_start;
             j < f->base_rep.cycle_start + L; j++)
            digit_sum += f->base_rep.digits[j];
        int g = digit_sum % (b - 1);
        if (g < 0) g += (b - 1);
        /* gcd(digit_sum mod (b-1), b-1) */
        int a2 = g, b2 = b - 1;
        while (b2) { int t = b2; b2 = a2 % b2; a2 = t; }
        int gcd_val = a2 > 0 ? a2 : b - 1;
        orbit_len = L * (b - 1) / gcd_val;
    }

    /* lambda = number of repetend periods to close the orbit */
    int lambda = (L > 0) ? orbit_len / L : 0;

    printf("n = %d, base = %d, repetend = %d, orbit = %d\n\n",
           f->n, f->base, L, orbit_len);

    for (int i = 0; i < f->num_rows; i++) {
        const Row *r = &f->rows[i];
        const Repetend *rep = &r->rep;

        printf("  %d/%d => 0.", r->k, f->n);

        if (rep->cycle_len == 0) {
            /* terminating (open) */
            if (rep->len == 0) {
                printf("0");
            } else {
                print_digits(rep->digits, rep->len, f->base);
            }
        } else {
            /* non-repeating prefix */
            if (rep->cycle_start > 0)
                print_digits(rep->digits, rep->cycle_start, f->base);
            /* orbit in pipes: repeat the repetend lambda times */
            printf("|");
            for (int j = 0; j < lambda; j++)
                print_digits(rep->digits + rep->cycle_start,
                             rep->cycle_len, f->base);
            printf("|");
        }

        printf(" (%s)\n", rep_type(rep));
    }
}

/* ── polar display ──────────────────────────────────────── */

static int digital_root(int n)
{
    if (n == 0) return 0;
    int r = n % 9;
    return r ? r : 9;
}

void polar_print(int n, int base)
{
    if (n < 2) {
        printf("No field for n < 2\n");
        return;
    }

    Field f = field_build(n, base);
    int L = f.base_rep.cycle_len;

    /* count open and closed */
    int n_open = 0, n_closed = 0;
    for (int i = 0; i < f.num_rows; i++) {
        if (f.rows[i].rep.cycle_len == 0) n_open++;
        else n_closed++;
    }

    printf("n = %d, base = %d, cycle_length = %d\n", n, base, L);
    printf("open (terminating): %d, closed (repeating): %d\n\n", n_open, n_closed);

    /* open fractions */
    if (n_open > 0) {
        printf("── open field content ─────────────────────────────\n\n");
        for (int i = 0; i < f.num_rows; i++) {
            const Row *r = &f.rows[i];
            if (r->rep.cycle_len != 0) continue;

            printf("  %3d/%-3d  ", r->k, n);

            /* digits */
            printf("digits: ");
            if (r->rep.len == 0) {
                printf("0");
            } else {
                for (int j = 0; j < r->rep.len; j++)
                    printf("%d ", r->rep.digits[j]);
            }

            /* digital root of digit sum */
            int sum = 0;
            for (int j = 0; j < r->rep.len; j++)
                sum += r->rep.digits[j];
            int dr = digital_root(sum);
            printf(" dr=%d", dr);

            /* cumulative polarity */
            printf("  polar: ");
            int running = 0;
            for (int j = 0; j < r->rep.len; j++) {
                running += r->rep.digits[j];
                int cp = running % 9;
                if (cp == 0) cp = 9;
                printf("%d ", cp);
            }

            printf("\n");
        }
        printf("\n");
    }

    /* closed fractions */
    if (n_closed > 0) {
        printf("── closed field content ───────────────────────────\n\n");

        /* header */
        printf("          ");
        int cL = L > 0 ? L : 1;
        for (int j = 0; j < cL && j < 60; j++)
            printf("%2d", j);
        printf("\n          ");
        for (int j = 0; j < cL && j < 60; j++)
            printf("--");
        printf("\n");

        for (int i = 0; i < f.num_rows; i++) {
            const Row *r = &f.rows[i];
            if (r->rep.cycle_len == 0) continue;

            const int *c = r->rep.digits + r->rep.cycle_start;
            int rL = r->rep.cycle_len;

            printf("  %3d/%-3d ", r->k, n);
            for (int j = 0; j < rL && j < 60; j++)
                printf("%2d", c[j]);
            printf("\n");
        }

        printf("\n── orientation (cumulative polarity) ──────────────\n\n");

        /* header */
        printf("          ");
        for (int j = 0; j < cL && j < 60; j++)
            printf("%2d", j);
        printf("\n          ");
        for (int j = 0; j < cL && j < 60; j++)
            printf("--");
        printf("\n");

        for (int i = 0; i < f.num_rows; i++) {
            const Row *r = &f.rows[i];
            if (r->rep.cycle_len == 0) continue;

            const int *c = r->rep.digits + r->rep.cycle_start;
            int rL = r->rep.cycle_len;

            printf("  %3d/%-3d ", r->k, n);
            int running = 0;
            for (int j = 0; j < rL && j < 60; j++) {
                running += c[j];
                int cp = running % 9;
                if (cp == 0) cp = 9;
                printf("%2d", cp);
            }
            printf("\n");
        }
        printf("\n");
    }

    field_free(&f);
}

/* ── invariants display ──────────────────────────────────── */

void invariants_print(const Invariants *inv)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    const char *tier;
    if (inv->alignment >= 1.0 - 1e-12)
        tier = "T1";
    else if (inv->alignment >= tau)
        tier = "T2";
    else
        tier = "T3";

    printf("n            = %d\n", inv->n);
    printf("base         = %d\n", inv->base);
    printf("cycle length = %d\n", inv->cycle_length);
    printf("alignment    = %.6f\n", inv->alignment);
    printf("tier         = %s\n", tier);

    if (inv->cycle_length > 1) {
        printf("curvature    = %.6f\n", inv->curvature);
        printf("coherence    = %.6f\n", inv->coherence);
        printf("harmonicity  = %d\n", inv->harmonicity);
        printf("structure    = %.6f\n", inv->structure);
        printf("burden       = %.6f\n", inv->burden);
        printf("depth        = %.6f\n", inv->depth);
    }
}

/* ── tier string ─────────────────────────────────────────── */

static const char *tier_str(double alignment)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    if (alignment >= 1.0 - 1e-12)
        return "T1";
    else if (alignment >= tau)
        return "T2";
    else
        return "T3";
}

/* ── survey ──────────────────────────────────────────────── */

void survey(int n_max, int base, int csv)
{
    survey_range(2, n_max, base, csv);
}

void survey_range(int n_min, int n_max, int base, int csv)
{
    if (csv) {
        printf("n,base,cycle_length,curvature,coherence,harmonicity,"
               "structure,burden,depth,alignment,tier\n");
    } else {
        printf("%5s %4s %8s %8s %3s %8s %8s %8s %10s %5s\n",
               "n", "L", "C", "R", "H3", "S", "B", "D", "align", "tier");
        for (int i = 0; i < 75; i++) putchar('-');
        putchar('\n');
    }

    int count = n_max - n_min + 1;
    Invariants *results = malloc(count * sizeof(Invariants));

#ifdef NFIELD_PARALLEL
    #pragma omp parallel for schedule(dynamic)
#endif
    for (int n = n_min; n <= n_max; n++)
        results[n - n_min] = invariants_compute(n, base);

    for (int i = 0; i < count; i++) {
        Invariants inv = results[i];
        int n = n_min + i;
        const char *tier = tier_str(inv.alignment);

        if (csv) {
            printf("%d,%d,%d,%.6f,%.6f,%d,%.6f,%.6f,%.6f,%.6f,%s\n",
                   n, base, inv.cycle_length, inv.curvature, inv.coherence,
                   inv.harmonicity, inv.structure, inv.burden, inv.depth,
                   inv.alignment, tier);
        } else {
            printf("%5d %4d %8.4f %8.4f %3d %8.4f %8.4f %8.4f %10.6f %5s\n",
                   n, inv.cycle_length, inv.curvature, inv.coherence,
                   inv.harmonicity, inv.structure, inv.burden, inv.depth,
                   inv.alignment, tier);
        }
    }
    free(results);
}

/* ── coherence decomposition ────────────────────── */

double sigma_exact(int n, int base)
{
    if (n < 3 || base < 2) return NAN;
    Field f = field_build(n, base);
    int depth = f.base_rep.cycle_start;
    int L = f.base_rep.cycle_len;

    double total = 0.0;
    long count = 0;

    for (int i = 0; i < f.num_rows; i++) {
        for (int j = i + 1; j < f.num_rows; j++) {
            Row *ri = &f.rows[i];
            Row *rj = &f.rows[j];

            if (ri->rep.cycle_len == 0 && rj->rep.cycle_len == 0) {
                total += 1.0;
            } else if (ri->rep.cycle_len > 0 && rj->rep.cycle_len > 0
                       && L > 0) {
                int matches = 0;
                for (int pos = 0; pos < L; pos++)
                    if (repetend_digit_at(&ri->rep, depth + pos)
                        == repetend_digit_at(&rj->rep, depth + pos))
                        matches++;
                total += (double)matches / L;
            }
            count++;
        }
    }

    field_free(&f);
    return count > 0 ? total / count : 0.0;
}

int decompose_print(int n, int base)
{
    if (n < 3) {
        fprintf(stderr,
                "n must be at least 3; F(2) has no distinct unordered pair\n");
        return 1;
    }
    if (base < 2) {
        fprintf(stderr, "base must be at least 2\n");
        return 1;
    }
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    double alpha = alignment_exact(n, base);
    double sigma = sigma_exact(n, base);
    double F = alpha - sigma;

    printf("n            = %d\n", n);
    printf("base         = %d\n", base);
    printf("alpha        = %.6f  (reference alignment)\n", alpha);
    printf("sigma        = %.6f  (symmetric pairwise alignment)\n", sigma);
    printf("F            = %.6f  (signed residual alpha - sigma)\n", F);

    if (sigma > 1e-12)
        printf("alpha/sigma  = %.4f\n", alpha / sigma);

    if (F < tau && alpha >= tau)
        printf("1/phi in gap = yes\n");
    else if (alpha < tau)
        printf("1/phi in gap = no (alpha below threshold)\n");
    else
        printf("1/phi in gap = no (F above threshold)\n");
    return 0;
}
