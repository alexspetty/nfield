/*
 * alpha_multi_base.c - Cancellation exponent across bases.
 *
 * For each base b, compute F°, F°°, M at several s values,
 * track the ratio and fitted alpha as prime count grows.
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#define MAX_PRIME 10000000
#define NS 6

static int is_prime(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

static void run_base(int b) {
    int m = b * b;

    /* Build S table */
    int *S_table = calloc(m, sizeof(int));
    int *has_S = calloc(m, sizeof(int));

    for (int p = m + 1; p < 80000 && p < MAX_PRIME; p++) {
        if (!is_prime(p) || gcd(p, b) != 1) continue;
        int a = p % m;
        if (has_S[a]) continue;

        int C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)b * r / p);
            long long br = (long long)b * r % p;
            int d2 = (int)((long long)b * br / p);
            if (d1 == d2) C++;
        }
        S_table[a] = C - (p - 1) / b;
        has_S[a] = 1;
    }

    /* Class means (spectral class R = (a-1) % b) */
    double *cls_sum = calloc(b, sizeof(double));
    int *cls_cnt = calloc(b, sizeof(int));

    for (int a = 1; a < m; a++) {
        if (gcd(a, m) != 1 || !has_S[a]) continue;
        int R = (a - 1) % b;
        cls_sum[R] += S_table[a];
        cls_cnt[R]++;
    }
    double *mean_R = calloc(b, sizeof(double));
    for (int R = 0; R < b; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    /* Centered S° */
    double *S_cent = calloc(m, sizeof(double));
    int *has_cent = calloc(m, sizeof(int));
    for (int a = 1; a < m; a++) {
        if (gcd(a, m) != 1 || !has_S[a]) continue;
        S_cent[a] = S_table[a] - mean_R[(a - 1) % b];
        has_cent[a] = 1;
    }

    /* Mod-3 means of S° */
    double m3_sum[3] = {0, 0, 0};
    int m3_cnt[3] = {0, 0, 0};
    for (int a = 1; a < m; a++) {
        if (!has_cent[a]) continue;
        m3_sum[a % 3] += S_cent[a];
        m3_cnt[a % 3]++;
    }
    double mean_3[3];
    for (int k = 0; k < 3; k++)
        mean_3[k] = m3_cnt[k] > 0 ? m3_sum[k] / m3_cnt[k] : 0;

    double c0 = (mean_3[1] + mean_3[2]) / 2;
    double c1 = (mean_3[1] - mean_3[2]) / 2;

    printf("\n========== BASE %d (m=%d, phi=%d) ==========\n", b, m, m3_cnt[0]+m3_cnt[1]+m3_cnt[2]);
    printf("mod-3 means: m0=%+.4f m1=%+.4f m2=%+.4f\n", mean_3[0], mean_3[1], mean_3[2]);
    printf("c0=%.4f c1=%.4f\n", c0, c1);

    /* Accumulate sums */
    double s_vals[NS] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    double F_single[NS] = {0};
    double F_double[NS] = {0};
    double F_mod3[NS] = {0};

    int count = 0;

    for (int p = m + 1; p < MAX_PRIME; p++) {
        if (!is_prime(p) || gcd(p, b) != 1) continue;
        count++;

        int a = p % m;
        if (!has_cent[a]) continue;

        double sc = S_cent[a];
        int k = p % 3;
        double mod3_val = mean_3[k];
        double sc_double = sc - mod3_val;

        for (int j = 0; j < NS; j++) {
            double w = pow((double)p, -s_vals[j]);
            F_single[j] += sc * w;
            F_double[j] += sc_double * w;
            F_mod3[j] += mod3_val * w;
        }
    }

    printf("\nFINAL (%d primes):\n", count);
    printf("%5s %10s %10s %10s %12s\n", "s", "F°", "F°°", "M", "1+ratio");

    double log_x[NS], log_y[NS];
    int npts = 0;

    for (int j = 0; j < NS; j++) {
        double ratio = (fabs(F_mod3[j]) > 1e-10) ?
            F_double[j] / F_mod3[j] : 0;
        double one_plus = 1.0 + ratio;
        double absF = fabs(F_double[j]);

        printf("%5.1f %+10.4f %+10.4f %+10.4f %+12.6f\n",
               s_vals[j], F_single[j], F_double[j], F_mod3[j], one_plus);

        if (absF > 0.5 && fabs(one_plus) > 1e-12) {
            log_x[npts] = log(absF);
            log_y[npts] = log(fabs(one_plus));
            npts++;
        }
    }

    if (npts >= 3) {
        double sx = 0, sy = 0, sxx = 0, sxy = 0;
        for (int i = 0; i < npts; i++) {
            sx += log_x[i]; sy += log_y[i];
            sxx += log_x[i]*log_x[i]; sxy += log_x[i]*log_y[i];
        }
        double slope = (npts*sxy - sx*sy) / (npts*sxx - sx*sx);
        double alpha = -slope;
        printf("  => fitted alpha = %.4f (%d points)\n", alpha, npts);
    }

    free(S_table); free(has_S); free(cls_sum); free(cls_cnt);
    free(mean_R); free(S_cent); free(has_cent);
}

int main(void) {
    int bases[] = {3, 5, 7, 10, 11, 12, 13};
    int nb = sizeof(bases) / sizeof(bases[0]);

    for (int i = 0; i < nb; i++)
        run_base(bases[i]);

    return 0;
}
