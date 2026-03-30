/*
 * uncertainty.c - Test finite group uncertainty principle.
 *
 * For a function f on a finite abelian group G of order N,
 * the Donoho-Stark uncertainty principle says:
 *   |supp(f)| * |supp(f_hat)| >= N
 *
 * More generally, for "effective support" (using entropy or
 * concentration measures):
 *   H(|f|^2) + H(|f_hat|^2) >= log N
 *
 * We test: does the collision invariant S° saturate or
 * approach these bounds? And does the "cross-uncertainty"
 * between |s_hat|^2 and |P|^2 follow a similar pattern?
 *
 * For each prime base b:
 * - Compute |s_hat(chi)|^2 distribution over odd characters
 * - Compute |P(0.5, chi)|^2 distribution over odd characters
 * - Compute Shannon entropy of both distributions
 * - Compute effective support (exp(H))
 * - Check product of effective supports vs group size
 * - Compute the "overlap" between the two distributions
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000

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
    printf("%5s %4s %4s | %8s %8s %8s | %8s %8s %8s | %8s %8s\n",
           "base", "phi", "odd",
           "H(sh)", "eff_sh", "max_sh",
           "H(P)", "eff_P", "max_P",
           "overlap", "prod/n");

    for (int b = 3; b <= 31; b++) {
        if (!is_prime(b)) continue;
        int m = b * b;
        int units[m], n_units = 0;
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
        if (g < 0) continue;

        int dlog[m];
        memset(dlog, -1, sizeof(int) * m);
        { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * g % m); } }

        /* Build S, center */
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

        double Sc[m];
        int has_Sc[m];
        memset(has_Sc, 0, sizeof(int) * m);
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_S[a]) continue;
            Sc[a] = S[a] - mean_R[(a-1)%b];
            has_Sc[a] = 1;
        }

        int dl_m1 = dlog[m - 1];

        /* Find odd characters, compute |s_hat|^2 and |P|^2 */
        int odd_j[2000], n_odd = 0;
        for (int j = 0; j < n_units && n_odd < 2000; j++) {
            long long test = 2LL * j * dl_m1;
            if ((int)(test % (2 * n_units)) != n_units) continue;
            odd_j[n_odd++] = j;
        }

        double sh_mag2[2000], P_mag2[2000];
        double sh_re[2000], sh_im[2000];
        double P_re[2000], P_im[2000];
        memset(P_re, 0, sizeof(double) * n_odd);
        memset(P_im, 0, sizeof(double) * n_odd);

        for (int c = 0; c < n_odd; c++) {
            int j = odd_j[c];
            double re = 0, im = 0;
            for (int i = 0; i < n_units; i++) {
                int a = units[i];
                if (!has_Sc[a]) continue;
                double angle = -2 * M_PI * j * dlog[a] / (double)n_units;
                re += Sc[a] * cos(angle);
                im += Sc[a] * sin(angle);
            }
            sh_re[c] = re / n_units;
            sh_im[c] = im / n_units;
            sh_mag2[c] = sh_re[c]*sh_re[c] + sh_im[c]*sh_im[c];
        }

        for (int p = m + 1; p < MAX_PRIME; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            int dl = dlog[a];
            if (dl < 0) continue;
            double w = 1.0 / sqrt((double)p);
            for (int c = 0; c < n_odd; c++) {
                double angle = 2 * M_PI * odd_j[c] * dl / (double)n_units;
                P_re[c] += cos(angle) * w;
                P_im[c] += sin(angle) * w;
            }
        }

        for (int c = 0; c < n_odd; c++)
            P_mag2[c] = P_re[c]*P_re[c] + P_im[c]*P_im[c];

        /* Normalize to probability distributions */
        double total_sh = 0, total_P = 0;
        double max_sh = 0, max_P = 0;
        for (int c = 0; c < n_odd; c++) {
            total_sh += sh_mag2[c];
            total_P += P_mag2[c];
            if (sh_mag2[c] > max_sh) max_sh = sh_mag2[c];
            if (P_mag2[c] > max_P) max_P = P_mag2[c];
        }

        /* Shannon entropy H = -sum p_i log p_i */
        double H_sh = 0, H_P = 0;
        for (int c = 0; c < n_odd; c++) {
            if (sh_mag2[c] > 1e-15) {
                double p = sh_mag2[c] / total_sh;
                H_sh -= p * log(p);
            }
            if (P_mag2[c] > 1e-15) {
                double p = P_mag2[c] / total_P;
                H_P -= p * log(p);
            }
        }

        double eff_sh = exp(H_sh);  /* effective support */
        double eff_P = exp(H_P);

        /* Overlap: sum of product of normalized distributions */
        /* (cosine similarity of the |.|^2 distributions) */
        double overlap = 0;
        for (int c = 0; c < n_odd; c++)
            overlap += (sh_mag2[c] / total_sh) * (P_mag2[c] / total_P);

        /* Product of effective supports / n */
        double prod_ratio = (eff_sh * eff_P) / n_odd;

        printf("%5d %4d %4d | %8.3f %8.2f %8.4f | %8.3f %8.2f %8.4f | %8.5f %8.4f\n",
               b, n_units, n_odd,
               H_sh, eff_sh, max_sh / total_sh,
               H_P, eff_P, max_P / total_P,
               overlap, prod_ratio);
    }

    return 0;
}
