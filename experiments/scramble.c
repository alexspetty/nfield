/*
 * scramble.c - Does the anti-correlation matter?
 *
 * Take the actual |s_hat| values and the actual P(s, chi) values.
 * Scramble the assignment: randomly permute which |s_hat| pairs
 * with which P. Preserve conjugate pairing and antisymmetry.
 *
 * For each scramble, compute the net Re(sum). If most scrambles
 * give divergent (large) nets or negative nets, then the specific
 * assignment matters and the anti-correlation is load-bearing.
 *
 * Base 10, lag 1, s = 0.5.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

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
    srand(42); /* reproducible */

    /* Run for multiple prime bases */
    int bases[] = {7, 11, 13, 17, 19, 23, 29, 31};
    int n_bases = sizeof(bases) / sizeof(bases[0]);

    printf("%5s %4s %10s %10s %10s %8s\n",
           "base", "odd", "actual", "mean_scr", "std_scr", "z-score");

    for (int bi = 0; bi < n_bases; bi++) {
        int b = bases[bi];
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
        if (g < 0) continue;

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

        /* Find odd characters */
        int odd_j[1000], n_odd = 0;
        for (int j = 0; j < n_units && n_odd < 1000; j++) {
            long long test = 2LL * j * dl_m1;
            if ((int)(test % (2 * n_units)) != n_units) continue;
            odd_j[n_odd++] = j;
        }

        /* Compute s_hat (complex) and P(0.5) (complex) for each */
        double sh_re[1000], sh_im[1000];
        double P_re[1000], P_im[1000];
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

        /* Actual net = sum Re(s_hat * P) */
        double actual = 0;
        for (int c = 0; c < n_odd; c++)
            actual += sh_re[c]*P_re[c] - sh_im[c]*P_im[c];

        /* Scramble test: permute the s_hat values among characters
         * and recompute net. Do 10000 trials. */
        int N_TRIALS = 10000;
        double sum_scr = 0, sum_scr2 = 0;
        int n_smaller = 0; /* how many scrambles have |net| < |actual| */
        int n_positive = 0;

        /* Store magnitudes and phases separately for scrambling */
        double sh_mag[1000], sh_phase[1000];
        double P_mag[1000], P_phase[1000];
        for (int c = 0; c < n_odd; c++) {
            sh_mag[c] = sqrt(sh_re[c]*sh_re[c] + sh_im[c]*sh_im[c]);
            sh_phase[c] = atan2(sh_im[c], sh_re[c]);
            P_mag[c] = sqrt(P_re[c]*P_re[c] + P_im[c]*P_im[c]);
            P_phase[c] = atan2(P_im[c], P_re[c]);
        }

        for (int trial = 0; trial < N_TRIALS; trial++) {
            /* Fisher-Yates shuffle of sh indices */
            int perm[1000];
            for (int c = 0; c < n_odd; c++) perm[c] = c;
            for (int c = n_odd - 1; c > 0; c--) {
                int j = rand() % (c + 1);
                int t = perm[c]; perm[c] = perm[j]; perm[j] = t;
            }

            /* Compute net with scrambled assignment:
             * pair s_hat[perm[c]] with P[c] */
            double net = 0;
            for (int c = 0; c < n_odd; c++) {
                int pc = perm[c];
                net += sh_re[pc]*P_re[c] - sh_im[pc]*P_im[c];
            }

            sum_scr += net;
            sum_scr2 += net * net;
            if (net > 0) n_positive++;
            if (fabs(net) < fabs(actual)) n_smaller++;
        }

        double mean_scr = sum_scr / N_TRIALS;
        double var_scr = sum_scr2 / N_TRIALS - mean_scr * mean_scr;
        double std_scr = sqrt(var_scr > 0 ? var_scr : 0);
        double z = std_scr > 0 ? (actual - mean_scr) / std_scr : 0;

        printf("%5d %4d %+10.4f %+10.4f %10.4f %+8.2f\n",
               b, n_odd, actual, mean_scr, std_scr, z);
    }

    return 0;
}
