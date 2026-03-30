/*
 * rho_precise.c - Pin down the repulsion ratio precisely.
 *
 * Compute n * overlap for many prime bases to get a tight
 * estimate of rho. Is it 1/phi = 0.6180? Or 3/5 = 0.6?
 * Or something else?
 *
 * Also: compute at multiple s values to check if rho
 * depends on s.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 3000000

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

double compute_rho(int b, double s) {
    int m = b * b;
    int units[m], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    int g = -1;
    for (int c = 2; c < m; c++) {
        if (gcd(c, m) != 1) continue;
        int v = 1, o = 0;
        do { v = (int)((long long)v * c % m); o++; } while (v != 1);
        if (o == n_units) { g = c; break; }
    }
    if (g < 0) return -1;

    int dlog[m];
    memset(dlog, -1, sizeof(int) * m);
    { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * g % m); } }

    int S[m], has_S[m];
    memset(has_S, 0, sizeof(int) * m);
    for (int p = m + 1; p < 80000; p++) {
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
        S[a] = C - (p - 1) / b;
        has_S[a] = 1;
    }

    double cls_sum[b];
    int cls_cnt[b];
    memset(cls_sum, 0, sizeof(double) * b);
    memset(cls_cnt, 0, sizeof(int) * b);
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (!has_S[a]) continue;
        cls_sum[(a-1)%b] += S[a];
        cls_cnt[(a-1)%b]++;
    }
    double mean_R[b];
    for (int R = 0; R < b; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    int dl_m1 = dlog[m - 1];
    int odd_j[2000], n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 2000; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    double sh_mag2[2000];
    double P_re[2000], P_im[2000], P_mag2[2000];
    memset(P_re, 0, sizeof(double) * n_odd);
    memset(P_im, 0, sizeof(double) * n_odd);

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

    for (int p = m + 1; p < MAX_PRIME; p++) {
        if (!is_prime(p) || gcd(p, b) != 1) continue;
        int a = p % m;
        int dl = dlog[a];
        if (dl < 0) continue;
        double w = pow((double)p, -s);
        for (int c = 0; c < n_odd; c++) {
            double angle = 2 * M_PI * odd_j[c] * dl / (double)n_units;
            P_re[c] += cos(angle) * w;
            P_im[c] += sin(angle) * w;
        }
    }

    for (int c = 0; c < n_odd; c++)
        P_mag2[c] = P_re[c]*P_re[c] + P_im[c]*P_im[c];

    double total_sh = 0, total_P = 0;
    for (int c = 0; c < n_odd; c++) {
        total_sh += sh_mag2[c];
        total_P += P_mag2[c];
    }

    double overlap = 0;
    for (int c = 0; c < n_odd; c++)
        overlap += (sh_mag2[c] / total_sh) * (P_mag2[c] / total_P);

    return n_odd * overlap;
}

int main(void) {
    double phi_inv = (sqrt(5.0) - 1.0) / 2.0;

    /* First: many bases at s = 0.5 */
    printf("=== rho at s = 0.5 across many bases ===\n");
    printf("%5s %4s %10s %10s\n", "base", "n", "rho", "rho-1/phi");

    double sum_rho = 0;
    int count = 0;

    int bases[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43};
    int nb = sizeof(bases) / sizeof(bases[0]);

    for (int i = 0; i < nb; i++) {
        int b = bases[i];
        int n = b * (b - 1) / 2; /* approximate n_odd */
        double rho = compute_rho(b, 0.5);
        if (rho < 0) continue;
        printf("%5d %4d %10.4f %+10.4f\n", b, n, rho, rho - phi_inv);
        sum_rho += rho;
        count++;
    }

    printf("\nMean rho = %.4f\n", sum_rho / count);
    printf("1/phi    = %.4f\n", phi_inv);
    printf("3/5      = %.4f\n", 0.6);
    printf("Diff from 1/phi: %+.4f\n", sum_rho / count - phi_inv);
    printf("Diff from 3/5:   %+.4f\n", sum_rho / count - 0.6);

    /* Second: s dependence at base 13 */
    printf("\n=== rho vs s at base 13 ===\n");
    printf("%5s %10s\n", "s", "rho");
    double s_vals[] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    for (int i = 0; i < 6; i++) {
        double rho = compute_rho(13, s_vals[i]);
        printf("%5.1f %10.4f\n", s_vals[i], rho);
    }

    return 0;
}
