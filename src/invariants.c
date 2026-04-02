/*
 * invariants.c: Structural invariants of a fractional field.
 *
 * Primitive invariants (pre-alignment program, exploratory):
 *   C(n)  curvature:   mean adjacent-digit variation in the base repetend
 *   R(n)  coherence:   dominance of the most common rotation index
 *   H3(n) harmonicity: whether the cycle length is divisible by 3
 *   S(n)  structure:   R/C + H3
 *   B(n)  burden:      accumulated structural load
 *   D(n)  depth:       1/S + B
 *
 * The alignment program invariants (alpha, sigma, F, Phi, R(ell), C(g))
 * are computed in output.c.
 */

#include <stdlib.h>
#include <math.h>
#include "nfield.h"

Invariants invariants_compute(int n, int base)
{
    Invariants inv = {0};
    inv.n    = n;
    inv.base = base;

    if (n < 2) {
        inv.alignment = 0.0;
        return inv;
    }

    Field f = field_build(n, base);

    int L = f.base_rep.cycle_len;
    inv.cycle_length = L;

    /* ── curvature C(n) ─────────────────────────────────── */

    double C = 0.0;
    if (L > 1) {
        const int *bc = f.base_rep.digits + f.base_rep.cycle_start;
        double sum = 0.0;
        for (int i = 0; i < L; i++)
            sum += fabs((double)bc[i] - (double)bc[(i + 1) % L]);
        C = sum / L;
    }
    inv.curvature = C;

    /* ── coherence R(n): rotation histogram dominance ──── */

    int *hist     = NULL;
    int  hist_len = 0;
    int  rot_total = 0;

    if (L > 0) {
        hist = calloc(L, sizeof(int));
        for (int i = 0; i < f.num_rows; i++) {
            int ri = f.rows[i].rot_index;
            if (ri >= 0 && ri < L) {
                hist[ri]++;
                rot_total++;
            }
        }
        hist_len = L;
    }

    double R = 0.0;
    if (rot_total > 0) {
        int max_count = 0;
        for (int j = 0; j < hist_len; j++)
            if (hist[j] > max_count)
                max_count = hist[j];
        R = (double)max_count / rot_total;
    }
    inv.coherence = R;

    /* ── harmonicity H3(n) ──────────────────────────────── */

    inv.harmonicity = (L > 0 && L % 3 == 0) ? 1 : 0;

    /* ── structure S(n) ─────────────────────────────────── */

    double S;
    if (C > 0.0)
        S = R / C + inv.harmonicity;
    else
        S = (inv.harmonicity > 0) ? (double)inv.harmonicity : 1e-10;
    inv.structure = S;

    /* ── burden B(n) ────────────────────────────────────── */

    double C_norm  = (L > 0) ? C / L : 0.0;
    double d_coh   = 1.0 - R;
    double d_triad = (inv.harmonicity) ? 0.0 : 1.0;

    double rot_sigma = 0.0;
    if (rot_total >= 2 && L > 0) {
        double mean = 0.0;
        for (int j = 0; j < hist_len; j++)
            mean += (double)j * hist[j];
        mean /= rot_total;

        double var = 0.0;
        for (int j = 0; j < hist_len; j++) {
            double diff = (double)j - mean;
            var += diff * diff * hist[j];
        }
        var /= rot_total;
        rot_sigma = sqrt(var) / L;
    }

    inv.burden = C_norm + d_coh + d_triad + rot_sigma;

    /* ── depth D(n) ─────────────────────────────────────── */

    inv.depth = (S > 0 ? 1.0 / S : 1e10) + inv.burden;

    /* ── alignment ──────────────────────────────────────── */

    double sum_align = 0.0;
    for (int i = 0; i < f.num_rows; i++)
        sum_align += f.rows[i].alignment;
    inv.alignment = sum_align / f.num_rows;

    /* ── cleanup ────────────────────────────────────────── */

    free(hist);
    field_free(&f);

    return inv;
}

double alignment_exact(int n, int base)
{
    Field f = field_build(n, base);

    double sum = 0.0;
    for (int i = 0; i < f.num_rows; i++)
        sum += f.rows[i].alignment;

    double a = sum / f.num_rows;
    field_free(&f);
    return a;
}

double alignment_formula(int m, int p)
{
    return (2.0 * m - 1.0) / ((double)p * m - 1.0);
}

int mult_order(int base, int p)
{
    int r = base % p;
    if (r == 0) return 0;
    int order = 1, pw = r;
    while (pw != 1) {
        pw = (pw * base) % p;
        order++;
    }
    return order;
}

int is_b_smooth(int n, int base)
{
    if (n <= 1) return 1;
    int primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31};
    for (int i = 0; i < 11; i++)
        if (base % primes[i] == 0)
            while (n % primes[i] == 0)
                n /= primes[i];
    return n == 1;
}
