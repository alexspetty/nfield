/*
 * rho_crossing.c - Find where rho(s) = 1 precisely.
 *
 * Compute rho(s) at fine s grid for multiple prime bases.
 * Find the crossing point where the collision spectrum
 * transitions from aligned (rho > 1) to repelling (rho < 1).
 *
 * Uses OpenMP for parallel base computation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <omp.h>

#define MAX_PRIME 3000000
#define MAX_M 2500
#define MAX_CHARS 1200
#define NS 21

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

/* Sieve up to MAX_PRIME */
static char *sieve;

static void build_sieve(void) {
    sieve = calloc(MAX_PRIME + 1, 1);
    for (int i = 2; i <= MAX_PRIME; i++) sieve[i] = 1;
    for (int i = 2; (long long)i * i <= MAX_PRIME; i++)
        if (sieve[i])
            for (int j = i * i; j <= MAX_PRIME; j += i)
                sieve[j] = 0;
}

typedef struct {
    int b;
    int n_odd;
    double rho[NS];
    double crossing_s;
} result_t;

void compute_base(int b, result_t *res) {
    int m = b * b;
    int units[MAX_M], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    /* Primitive root */
    int g = -1;
    for (int c = 2; c < m; c++) {
        if (gcd(c, m) != 1) continue;
        int v = 1, o = 0;
        do { v = (int)((long long)v * c % m); o++; } while (v != 1);
        if (o == n_units) { g = c; break; }
    }
    if (g < 0) { res->b = b; res->n_odd = 0; return; }

    int *dlog = calloc(m, sizeof(int));
    memset(dlog, -1, sizeof(int) * m);
    { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * g % m); } }

    /* Build S table */
    int *S = calloc(m, sizeof(int));
    int *has_S = calloc(m, sizeof(int));

    for (int p = m + 1; p < 80000; p++) {
        if (!sieve[p] || gcd(p, b) != 1) continue;
        int a = p % m;
        if (has_S[a]) continue;
        int C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)b * r / p);
            long long br = (long long)b * r % p;
            int d2 = (int)((long long)b * br / p);
            if (d1 == d2) C++;
        }
        S[a] = C - (p - 1) / b;
        has_S[a] = 1;
    }

    /* Center */
    double *cls_sum = calloc(b, sizeof(double));
    int *cls_cnt = calloc(b, sizeof(int));
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (!has_S[a]) continue;
        cls_sum[(a-1)%b] += S[a];
        cls_cnt[(a-1)%b]++;
    }
    double *mean_R = calloc(b, sizeof(double));
    for (int R = 0; R < b; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    /* Find odd characters */
    int dl_m1 = dlog[m - 1];
    int odd_j[MAX_CHARS], n_odd = 0;
    for (int j = 0; j < n_units && n_odd < MAX_CHARS; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* Compute |s_hat|^2 (independent of s) */
    double *sh_mag2 = calloc(n_odd, sizeof(double));
    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];
        double re = 0, im = 0;
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_S[a]) continue;
            double sc = S[a] - mean_R[(a-1)%b];
            double angle = -2 * M_PI * j * dlog[a] / (double)n_units;
            re += sc * cos(angle);
            im += sc * sin(angle);
        }
        re /= n_units; im /= n_units;
        sh_mag2[c] = re*re + im*im;
    }

    double total_sh = 0;
    for (int c = 0; c < n_odd; c++) total_sh += sh_mag2[c];

    /* For each s, compute P(s,chi) and overlap */
    double s_vals[NS];
    for (int si = 0; si < NS; si++)
        s_vals[si] = 0.5 + si * 0.025; /* 0.50 to 1.00 in steps of 0.025 */

    /* Accumulate P for all s simultaneously */
    double (*P_re)[NS] = calloc(n_odd, sizeof(double[NS]));
    double (*P_im)[NS] = calloc(n_odd, sizeof(double[NS]));

    for (int p = m + 1; p < MAX_PRIME; p++) {
        if (!sieve[p] || gcd(p, b) != 1) continue;
        int a = p % m;
        int dl = dlog[a];
        if (dl < 0) continue;

        double log_p = log((double)p);

        for (int c = 0; c < n_odd; c++) {
            double angle = 2 * M_PI * odd_j[c] * dl / (double)n_units;
            double cos_a = cos(angle), sin_a = sin(angle);

            for (int si = 0; si < NS; si++) {
                double w = exp(-s_vals[si] * log_p);
                P_re[c][si] += cos_a * w;
                P_im[c][si] += sin_a * w;
            }
        }
    }

    /* Compute rho at each s */
    res->b = b;
    res->n_odd = n_odd;
    res->crossing_s = -1;

    for (int si = 0; si < NS; si++) {
        double total_P = 0;
        double *P_mag2 = calloc(n_odd, sizeof(double));
        for (int c = 0; c < n_odd; c++) {
            P_mag2[c] = P_re[c][si]*P_re[c][si] + P_im[c][si]*P_im[c][si];
            total_P += P_mag2[c];
        }

        double overlap = 0;
        for (int c = 0; c < n_odd; c++)
            overlap += (sh_mag2[c] / total_sh) * (P_mag2[c] / total_P);

        res->rho[si] = n_odd * overlap;
        free(P_mag2);

        /* Check for crossing */
        if (si > 0 && res->rho[si-1] > 1.0 && res->rho[si] <= 1.0) {
            /* Linear interpolation */
            double r0 = res->rho[si-1], r1 = res->rho[si];
            double s0 = s_vals[si-1], s1 = s_vals[si];
            res->crossing_s = s0 + (1.0 - r0) * (s1 - s0) / (r1 - r0);
        }
    }

    free(dlog); free(S); free(has_S); free(cls_sum);
    free(cls_cnt); free(mean_R); free(sh_mag2);
    free(P_re); free(P_im);
}

int main(void) {
    build_sieve();

    int bases[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43};
    int nb = sizeof(bases) / sizeof(bases[0]);
    result_t results[nb];

    #pragma omp parallel for schedule(dynamic)
    for (int i = 0; i < nb; i++) {
        compute_base(bases[i], &results[i]);
    }

    /* Print header */
    printf("%5s %4s", "base", "n");
    for (int si = 0; si < NS; si++)
        printf(" %6.3f", 0.5 + si * 0.025);
    printf(" %8s\n", "cross");

    /* Print results */
    for (int i = 0; i < nb; i++) {
        if (results[i].n_odd == 0) continue;
        printf("%5d %4d", results[i].b, results[i].n_odd);
        for (int si = 0; si < NS; si++)
            printf(" %6.3f", results[i].rho[si]);
        printf(" %8.4f\n", results[i].crossing_s);
    }

    /* Summary: average crossing point */
    double sum_cross = 0;
    int n_cross = 0;
    for (int i = 0; i < nb; i++) {
        if (results[i].crossing_s > 0) {
            sum_cross += results[i].crossing_s;
            n_cross++;
        }
    }
    if (n_cross > 0)
        printf("\nMean crossing point: s = %.4f (%d bases)\n",
               sum_cross / n_cross, n_cross);

    printf("1 - 1/e = %.4f\n", 1.0 - 1.0/exp(1.0));
    printf("1/phi   = %.4f\n", (sqrt(5.0)-1)/2);
    printf("ln(2)   = %.4f\n", log(2.0));

    free(sieve);
    return 0;
}
