/*
 * alpha_drift.c - Track the cancellation exponent alpha as prime count grows.
 *
 * For each checkpoint (number of primes), compute F°, F°°, M at several
 * s values, then fit alpha from the log-log regression:
 *   log(1 + ratio) = -alpha * log|F°°| + log C
 *
 * If alpha drifts toward 1.0 as we add primes, the 0.6 is pre-asymptotic.
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#define B 10
#define M (B * B)
#define MAX_PRIME 20000000  /* ~1.27M primes */
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

int main(void) {
    /* Build S table for all units mod m */
    int S_table[M];
    int has_S[M];
    memset(has_S, 0, sizeof(has_S));

    for (int p = M + 1; p < 10000; p++) {
        if (!is_prime(p) || gcd(p, B) != 1) continue;
        int a = p % M;
        if (has_S[a]) continue;

        /* Collision count at lag 1 */
        int C = 0;
        for (int r = 1; r < p; r++) {
            int br = B * r;
            int gr = (long long)B * r % p;  /* g = b for lag 1 */
            if (br / p == (int)((long long)B * ((long long)B * r % p)) / p)
                C++;
        }
        /* Wait, g = b mod p for lag 1. Let me redo this properly. */
        /* Actually for lag 1, g = b. C(g) = #{r : floor(br/p) = floor(b(br mod p)/p)} */
        /* br mod p is the image under multiplication by b. */
        C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)B * r / p);  /* floor(br/p) - but careful with overflow */
            long long br_mod_p = (long long)B * r % p;
            int d2 = (int)((long long)B * br_mod_p / p);
            if (d1 == d2) C++;
        }
        S_table[a] = C - (p - 1) / B;
        has_S[a] = 1;
    }

    /* Compute class means */
    double cls_sum[B];
    int cls_cnt[B];
    memset(cls_sum, 0, sizeof(cls_sum));
    memset(cls_cnt, 0, sizeof(cls_cnt));

    for (int a = 1; a < M; a++) {
        if (gcd(a, M) != 1 || !has_S[a]) continue;
        int R = (a - 1) % B;
        cls_sum[R] += S_table[a];
        cls_cnt[R]++;
    }
    double mean_R[B];
    for (int R = 0; R < B; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    /* Centered S° */
    double S_cent[M];
    int has_cent[M];
    memset(has_cent, 0, sizeof(has_cent));
    for (int a = 1; a < M; a++) {
        if (gcd(a, M) != 1 || !has_S[a]) continue;
        S_cent[a] = S_table[a] - mean_R[(a - 1) % B];
        has_cent[a] = 1;
    }

    /* Mod-3 means of S° */
    double m3_sum[3] = {0, 0, 0};
    int m3_cnt[3] = {0, 0, 0};
    for (int a = 1; a < M; a++) {
        if (!has_cent[a]) continue;
        int k = a % 3;
        m3_sum[k] += S_cent[a];
        m3_cnt[k]++;
    }
    double mean_3[3];
    for (int k = 0; k < 3; k++)
        mean_3[k] = m3_cnt[k] > 0 ? m3_sum[k] / m3_cnt[k] : 0;

    printf("Mod-3 means of S°:\n");
    for (int k = 0; k < 3; k++)
        printf("  a ≡ %d mod 3: mean = %+.6f (n=%d)\n", k, mean_3[k], m3_cnt[k]);
    printf("\nc0 = %.6f, c1 = %.6f\n\n", (mean_3[1]+mean_3[2])/2, (mean_3[1]-mean_3[2])/2);

    /* Accumulate sums */
    double s_vals[NS] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    double F_single[NS] = {0};
    double F_double[NS] = {0};
    double F_mod3[NS] = {0};

    int checkpoints[] = {10000, 50000, 100000, 200000, 348488, 500000, 700000, 1000000, 1270000};
    int ncheck = sizeof(checkpoints) / sizeof(checkpoints[0]);
    int ci = 0;

    int count = 0;

    printf("%10s  ", "primes");
    for (int j = 0; j < NS; j++) printf("  alpha@%.1f", s_vals[j]);
    printf("   alpha_fit\n");

    for (int p = M + 1; p < MAX_PRIME && ci < ncheck; p++) {
        if (!is_prime(p) || gcd(p, B) != 1) continue;
        count++;

        int a = p % M;
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

        if (count >= checkpoints[ci]) {
            /* Print the full table */
            printf("\n--- %d primes (p ≈ %d) ---\n", count, p);
            printf("%5s %10s %10s %10s %12s %10s %12s\n",
                   "s", "F°", "F°°", "M", "1+ratio", "|F°°|", "product@0.6");

            /* Also collect points for alpha fit */
            double log_x[NS], log_y[NS];
            int npts = 0;

            for (int j = 0; j < NS; j++) {
                double ratio = (fabs(F_mod3[j]) > 1e-10) ?
                    F_double[j] / F_mod3[j] : 0;
                double one_plus = 1.0 + ratio;
                double absF = fabs(F_double[j]);
                double prod06 = fabs(one_plus) * pow(absF, 0.6);

                printf("%5.1f %+10.4f %+10.4f %+10.4f %+12.6f %10.2f %12.6f\n",
                       s_vals[j], F_single[j], F_double[j], F_mod3[j],
                       one_plus, absF, prod06);

                if (absF > 0.5 && fabs(one_plus) > 1e-12) {
                    log_x[npts] = log(absF);
                    log_y[npts] = log(fabs(one_plus));
                    npts++;
                }
            }

            /* Fit alpha by linear regression: log(1+ratio) = -alpha * log|F°°| + const */
            if (npts >= 3) {
                double sx = 0, sy = 0, sxx = 0, sxy = 0;
                for (int i = 0; i < npts; i++) {
                    sx += log_x[i];
                    sy += log_y[i];
                    sxx += log_x[i] * log_x[i];
                    sxy += log_x[i] * log_y[i];
                }
                double slope = (npts * sxy - sx * sy) / (npts * sxx - sx * sx);
                double alpha = -slope;
                printf("  => fitted alpha = %.4f (from %d points)\n", alpha, npts);
            }

            ci++;
        }
    }

    printf("\nTotal primes: %d\n", count);
    return 0;
}
