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

void field_print(const Field *f)
{
    printf("n = %d, base = %d, cycle_length = %d\n\n",
           f->n, f->base, f->base_rep.cycle_len);

    for (int i = 0; i < f->num_rows; i++) {
        const Row *r = &f->rows[i];

        printf("  k=%3d  ", r->k);
        if (r->rep.cycle_len == 0) {
            /* terminating: show the digits */
            printf("term=");
            if (r->rep.len == 0) {
                printf("0");
            } else if (f->base <= 10) {
                for (int j = 0; j < r->rep.len; j++)
                    printf("%d", r->rep.digits[j]);
            } else {
                for (int j = 0; j < r->rep.len; j++) {
                    if (j > 0) printf(".");
                    printf("%d", r->rep.digits[j]);
                }
            }
        } else {
            printf("cycle=");
            const int *c = r->rep.digits + r->rep.cycle_start;
            int L = r->rep.cycle_len;
            if (f->base <= 10) {
                for (int j = 0; j < L; j++) printf("%d", c[j]);
            } else {
                for (int j = 0; j < L; j++) {
                    if (j > 0) printf(".");
                    printf("%d", c[j]);
                }
            }
        }
        printf("  rot=%3d  align=%.4f\n", r->rot_index, r->alignment);
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

/* ── table 1 reproduction ────────────────────────────────── */

void table1(void)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    printf("Table 1: Repetend alignment for n = 3m (10-smooth m)\n");
    printf("  1/phi = %.6f\n\n", tau);
    printf("%5s %5s %12s %12s %12s %5s\n",
           "m", "n", "alpha", "predicted", "delta", ">=1/phi");

    for (int i = 0; i < 60; i++) putchar('-');
    putchar('\n');

    int ms[] = {1, 2, 4, 5, 8, 10, 16, 20, 25, 32, 40, 50, 64, 100, 128, 200, 256};
    int nms = sizeof(ms) / sizeof(ms[0]);

    for (int i = 0; i < nms; i++) {
        int m = ms[i];
        int n = 3 * m;
        double computed  = alignment_exact(n, 10);
        double predicted = alignment_formula(m, 3);
        double delta     = computed - tau;
        int above        = computed >= tau;
        printf("%5d %5d %12.6f %12.6f %+12.6f %5s\n",
               m, n, computed, predicted, delta, above ? "yes" : "no");
    }
}

/* ── paper 5: coherence decomposition ────────────────────── */

double sigma_exact(int n, int base)
{
    Field f = field_build(n, base);

    double total = 0.0;
    long count = 0;

    for (int i = 0; i < f.num_rows; i++) {
        for (int j = i + 1; j < f.num_rows; j++) {
            Row *ri = &f.rows[i];
            Row *rj = &f.rows[j];

            if (ri->rep.cycle_len == 0 && rj->rep.cycle_len == 0) {
                total += 1.0;
            } else if (ri->rep.cycle_len > 0 && rj->rep.cycle_len > 0
                       && ri->rep.cycle_len == rj->rep.cycle_len) {
                int cL = ri->rep.cycle_len;
                int *ci = ri->rep.digits + ri->rep.cycle_start;
                int *cj = rj->rep.digits + rj->rep.cycle_start;
                int matches = 0;
                for (int pos = 0; pos < cL; pos++)
                    if (ci[pos] == cj[pos])
                        matches++;
                total += (double)matches / cL;
            }
            count++;
        }
    }

    field_free(&f);
    return count > 0 ? total / count : 0.0;
}

void decompose_print(int n, int base)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    double alpha = alignment_exact(n, base);
    double sigma = sigma_exact(n, base);
    double F = alpha - sigma;

    printf("n            = %d\n", n);
    printf("base         = %d\n", base);
    printf("alpha        = %.6f  (total coherence)\n", alpha);
    printf("sigma        = %.6f  (diffuse coherence)\n", sigma);
    printf("F            = %.6f  (focused coherence)\n", F);

    if (sigma > 1e-12)
        printf("alpha/sigma  = %.4f\n", alpha / sigma);

    if (F < tau && alpha >= tau)
        printf("1/phi in gap = yes\n");
    else if (alpha < tau)
        printf("1/phi in gap = no (alpha below threshold)\n");
    else
        printf("1/phi in gap = no (F above threshold)\n");
}

/* ── paper 8: spectral power ─────────────────────────────── */

void spectral_print(int p, int base)
{
    /* compute bin sizes */
    int bins[256] = {0};
    for (int r = 1; r < p; r++)
        bins[(base * r) / p]++;

    /* multiplicative order */
    int L = mult_order(base, p);

    printf("n = %d, base = %d, L = %d\n\n", p, base, L);
    printf("Spectral power Phi(k):\n");
    printf("%5s %12s\n", "k", "Phi(k)");

    for (int k = 0; k < p; k++) {
        double phi_k = 0.0;
        if (k == 0) {
            for (int d = 0; d < base; d++)
                phi_k += (double)bins[d] * bins[d];
        } else {
            for (int d = 0; d < base; d++) {
                int nd = bins[d];
                if (nd == 0) continue;
                double num = sin(M_PI * k * nd / (double)p);
                double den = sin(M_PI * k / (double)p);
                phi_k += (num / den) * (num / den);
            }
        }
        printf("%5d %12.4f\n", k, phi_k);
    }

    /* also show autocorrelation R(ell) for verification */
    int *orbit = malloc(L * sizeof(int));
    int r = 1;
    for (int j = 0; j < L; j++) {
        orbit[j] = r;
        r = (r * base) % p;
    }

    /* compute repetend */
    int *rep = malloc(L * sizeof(int));
    for (int j = 0; j < L; j++)
        rep[j] = (base * orbit[j]) / p;

    printf("\nAutocorrelation R(ell):\n");
    printf("%5s %8s\n", "ell", "R(ell)");
    for (int ell = 0; ell < L; ell++) {
        int R = 0;
        for (int j = 0; j < L; j++)
            if (rep[j] == rep[(j + ell) % L])
                R++;
        printf("%5d %8d\n", ell, R);
    }

    free(orbit);
    free(rep);
}
