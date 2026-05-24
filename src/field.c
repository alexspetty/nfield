/*
 * field.c: Build and analyze the fractional field {k/n : k=1..n-1}.
 *
 * For each k, computes the repetend, rotation index relative to the
 * base repetend of 1/n, position-wise alignment, and cycle curvature.
 */

#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "nfield.h"

/* ── helpers ─────────────────────────────────────────────── */

static int *cycle_ptr(const Repetend *r)
{
    return r->digits + r->cycle_start;
}

static double cycle_curvature(const int *cycle, int L)
{
    if (L <= 1)
        return 0.0;

    double sum = 0.0;
    for (int i = 0; i < L; i++)
        sum += fabs((double)cycle[i] - (double)cycle[(i + 1) % L]);

    return sum / L;
}

static int find_rotation(const int *base, const int *target, int L)
{
    if (L == 0)
        return -1;

    for (int k = 0; k < L; k++) {
        int match = 1;
        for (int i = 0; i < L; i++) {
            if (target[i] != base[(i + k) % L]) {
                match = 0;
                break;
            }
        }
        if (match)
            return k;
    }
    return -1;
}

static double position_alignment(const int *a, const int *b, int L)
{
    if (L == 0)
        return 1.0;

    int match = 0;
    for (int i = 0; i < L; i++)
        if (a[i] == b[i])
            match++;

    return (double)match / L;
}

/* ── field construction ──────────────────────────────────── */

Field field_build(int n, int base)
{
    Field f  = {0};
    f.n      = n;
    f.base   = base;

    f.base_rep = repetend_compute(1, n, base);

    int      L     = f.base_rep.cycle_len;
    const int *bc  = cycle_ptr(&f.base_rep);

    f.num_rows = n - 1;
    f.rows     = calloc(f.num_rows, sizeof(Row));

    for (int k = 1; k < n; k++) {
        Row *row   = &f.rows[k - 1];
        row->k     = k;
        row->rep   = repetend_compute(k, n, base);

        int  rL    = row->rep.cycle_len;
        const int *rc = cycle_ptr(&row->rep);

        if (rL == L && L > 0) {
            row->rot_index = find_rotation(bc, rc, L);
            row->alignment = position_alignment(rc, bc, L);
        } else if (rL == 0) {
            row->rot_index = 0;
            row->alignment = 1.0;   /* terminating = aligned */
        } else {
            row->rot_index = -1;
            row->alignment = 0.0;
        }

        row->curvature = (rL > 0) ? cycle_curvature(rc, rL) : 0.0;
    }

    return f;
}

void field_free(Field *f)
{
    repetend_free(&f->base_rep);
    for (int i = 0; i < f->num_rows; i++)
        repetend_free(&f->rows[i].rep);
    free(f->rows);
    f->rows     = NULL;
    f->num_rows = 0;
}
