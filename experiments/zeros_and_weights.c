/*
 * zeros_and_weights.c - Direct comparison of collision weights
 * with L-function values near the critical line.
 *
 * For each odd character chi mod b^2:
 * - Compute |s_hat(chi)| (collision weight)
 * - Compute |L(s, chi)| at several s values on the real axis
 *   using truncated Euler product
 * - Small |L(s, chi)| means a zero is nearby
 * - Check: do large |s_hat| pair with large |L| (far from zeros)?
 *
 * If yes: the collision invariant avoids the characters
 * whose L-functions have zeros near s.
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
    int b = 13;  /* prime base with enough characters */
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

    int dl_m1 = dlog[m - 1];
    int odd_j[500], n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 500; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* Compute |s_hat|^2 */
    double sh_mag[500];
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
        sh_mag[c] = sqrt(re*re + im*im);
    }

    /* Compute |L(s, chi)| using truncated Euler product
     * L(s, chi) = prod_p (1 - chi(p)/p^s)^{-1}
     * |L(s, chi)| = prod_p |1 - chi(p)/p^s|^{-1}
     *
     * We compute log|L| = -sum_p log|1 - chi(p)/p^s|
     *
     * For convergence, we need Re(s) > 1/2 (conditional on GRH)
     * or Re(s) > 1 (unconditional absolute convergence).
     * At s = 0.75, the Euler product should give a reasonable
     * approximation with enough primes.
     */

    double s_vals[] = {0.55, 0.60, 0.65, 0.70, 0.75, 0.80, 0.90, 1.00};
    int n_s = 8;

    printf("Base %d, %d odd characters\n\n", b, n_odd);

    for (int si = 0; si < n_s; si++) {
        double s = s_vals[si];

        /* Compute log|L(s, chi)| for each odd character */
        double L_mag[500];
        memset(L_mag, 0, sizeof(double) * n_odd);

        for (int p = 2; p < MAX_PRIME; p++) {
            if (!is_prime(p)) continue;
            if (p == b) continue; /* skip p = b */

            int a = p % m;
            if (dlog[a] < 0 && gcd(a, m) != 1) continue;

            double p_s = pow((double)p, -s);

            for (int c = 0; c < n_odd; c++) {
                int j = odd_j[c];
                /* chi(p) = exp(2*pi*i * j * dlog[p%m] / phi) */
                int dl = dlog[p % m];
                if (dl < 0) continue;
                double angle = 2 * M_PI * j * dl / (double)n_units;
                double chi_re = cos(angle), chi_im = sin(angle);

                /* 1 - chi(p)/p^s */
                double re = 1.0 - chi_re * p_s;
                double im = -chi_im * p_s;
                double mag2 = re*re + im*im;

                /* log|L| += -log|1 - chi(p)/p^s| = -(1/2) log(mag2) */
                if (mag2 > 1e-30)
                    L_mag[c] -= 0.5 * log(mag2);
            }
        }

        /* Convert to |L| */
        for (int c = 0; c < n_odd; c++)
            L_mag[c] = exp(L_mag[c]);

        /* Correlation between |s_hat| and |L(s, chi)| */
        double sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0;
        int n = 0;
        for (int c = 0; c < n_odd; c++) {
            if (sh_mag[c] < 1e-10) continue;
            double x = sh_mag[c], y = L_mag[c];
            sx += x; sy += y;
            sxx += x*x; syy += y*y;
            sxy += x*y;
            n++;
        }
        double mx = sx/n, my = sy/n;
        double vx = sxx/n - mx*mx, vy = syy/n - my*my;
        double cov = sxy/n - mx*my;
        double corr = (vx > 0 && vy > 0) ? cov / sqrt(vx*vy) : 0;

        /* Also: correlation between |s_hat| and 1/|L| (closeness to zero) */
        double sy2 = 0, syy2 = 0, sxy2 = 0;
        for (int c = 0; c < n_odd; c++) {
            if (sh_mag[c] < 1e-10) continue;
            double x = sh_mag[c], y = 1.0 / L_mag[c];
            sy2 += y; syy2 += y*y; sxy2 += x*y;
        }
        double my2 = sy2/n;
        double vy2 = syy2/n - my2*my2;
        double cov2 = sxy2/n - mx*my2;
        double corr2 = (vx > 0 && vy2 > 0) ? cov2 / sqrt(vx*vy2) : 0;

        printf("s=%.2f: corr(|sh|,|L|)=%+.4f  corr(|sh|,1/|L|)=%+.4f  "
               "mean|L|=%.3f  min|L|=%.3f\n",
               s, corr, corr2, my,
               L_mag[0]); /* not real min, fix below */

        /* Find actual min |L| and which character */
        double min_L = 1e30;
        int min_c = 0;
        double max_L = 0;
        int max_c = 0;
        for (int c = 0; c < n_odd; c++) {
            if (L_mag[c] < min_L) { min_L = L_mag[c]; min_c = c; }
            if (L_mag[c] > max_L) { max_L = L_mag[c]; max_c = c; }
        }
        printf("       min|L|=%.4f at c=%d (|sh|=%.4f)  "
               "max|L|=%.4f at c=%d (|sh|=%.4f)\n",
               min_L, min_c, sh_mag[min_c],
               max_L, max_c, sh_mag[max_c]);
    }

    /* Print top 5 and bottom 5 by |s_hat| with their |L(0.7)| */
    printf("\n=== Top 5 |s_hat| with |L(0.7)| ===\n");
    /* Sort by sh_mag */
    int idx[500];
    for (int c = 0; c < n_odd; c++) idx[c] = c;
    for (int i = 0; i < n_odd - 1; i++)
        for (int k = i + 1; k < n_odd; k++)
            if (sh_mag[idx[k]] > sh_mag[idx[i]]) {
                int t = idx[i]; idx[i] = idx[k]; idx[k] = t;
            }

    /* Recompute |L(0.7)| */
    double L_at_07[500];
    memset(L_at_07, 0, sizeof(double) * n_odd);
    for (int p = 2; p < MAX_PRIME; p++) {
        if (!is_prime(p) || p == b) continue;
        int dl = dlog[p % m];
        if (dl < 0) continue;
        double p_s = pow((double)p, -0.7);
        for (int c = 0; c < n_odd; c++) {
            double angle = 2 * M_PI * odd_j[c] * dl / (double)n_units;
            double re = 1.0 - cos(angle) * p_s;
            double im = -sin(angle) * p_s;
            double mag2 = re*re + im*im;
            if (mag2 > 1e-30)
                L_at_07[c] -= 0.5 * log(mag2);
        }
    }
    for (int c = 0; c < n_odd; c++)
        L_at_07[c] = exp(L_at_07[c]);

    printf("Top 5 (large collision weight):\n");
    for (int i = 0; i < 5; i++)
        printf("  c=%3d  |sh|=%.4f  |L(0.7)|=%.4f\n",
               idx[i], sh_mag[idx[i]], L_at_07[idx[i]]);

    printf("Bottom 5 (small collision weight):\n");
    for (int i = n_odd - 5; i < n_odd; i++)
        printf("  c=%3d  |sh|=%.4f  |L(0.7)|=%.4f\n",
               idx[i], sh_mag[idx[i]], L_at_07[idx[i]]);

    return 0;
}
