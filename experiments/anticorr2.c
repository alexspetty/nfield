/*
 * anticorr2.c - Optimized: scan primes once, accumulate all characters.
 * Only compute at s = 0.5.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000
#define MAX_CHARS 1000

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
    printf("%5s %4s %8s %8s %8s\n",
           "base", "odd", "corr", "rank_cor", "top3_P");

    for (int b = 3; b <= 37; b++) {
        if (!is_prime(b)) continue;
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

        /* Find odd character indices */
        int odd_j[MAX_CHARS], n_odd = 0;
        for (int j = 0; j < n_units && n_odd < MAX_CHARS; j++) {
            long long test = 2LL * j * dl_m1;
            if ((int)(test % (2 * n_units)) != n_units) continue;
            odd_j[n_odd++] = j;
        }

        /* Precompute angles for each unit: angle[i][c] = 2*pi*j*dlog[a]/phi */
        /* Too much memory. Instead, precompute dlog values and compute on the fly. */

        /* Compute s_hat for each odd character */
        double sh_mag[MAX_CHARS];
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
            sh_mag[c] = sqrt(re*re + im*im) / n_units;
        }

        /* Compute P(0.5) for each odd character: scan primes ONCE */
        double P_re[MAX_CHARS], P_im[MAX_CHARS];
        memset(P_re, 0, sizeof(double) * n_odd);
        memset(P_im, 0, sizeof(double) * n_odd);

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

        double P_mag[MAX_CHARS];
        for (int c = 0; c < n_odd; c++)
            P_mag[c] = sqrt(P_re[c]*P_re[c] + P_im[c]*P_im[c]);

        /* Pearson correlation between |s_hat| and |P| */
        double sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0;
        int n = 0;
        for (int c = 0; c < n_odd; c++) {
            if (sh_mag[c] < 1e-10) continue;
            double x = sh_mag[c], y = P_mag[c];
            sx += x; sy += y;
            sxx += x*x; syy += y*y;
            sxy += x*y;
            n++;
        }
        double mx = sx/n, my = sy/n;
        double vx = sxx/n - mx*mx, vy = syy/n - my*my;
        double cov = sxy/n - mx*my;
        double corr = (vx > 0 && vy > 0) ? cov / sqrt(vx*vy) : 0;

        /* Spearman rank correlation */
        /* Sort indices by sh_mag and by P_mag, compute rank correlation */
        int rank_sh[MAX_CHARS], rank_P[MAX_CHARS];
        int idx[MAX_CHARS];
        for (int c = 0; c < n_odd; c++) idx[c] = c;

        /* Rank by sh_mag */
        for (int i = 0; i < n_odd - 1; i++)
            for (int k = i + 1; k < n_odd; k++)
                if (sh_mag[idx[k]] > sh_mag[idx[i]]) {
                    int t = idx[i]; idx[i] = idx[k]; idx[k] = t;
                }
        for (int i = 0; i < n_odd; i++) rank_sh[idx[i]] = i;

        /* Rank by P_mag */
        for (int c = 0; c < n_odd; c++) idx[c] = c;
        for (int i = 0; i < n_odd - 1; i++)
            for (int k = i + 1; k < n_odd; k++)
                if (P_mag[idx[k]] > P_mag[idx[i]]) {
                    int t = idx[i]; idx[i] = idx[k]; idx[k] = t;
                }
        for (int i = 0; i < n_odd; i++) rank_P[idx[i]] = i;

        double d2_sum = 0;
        for (int c = 0; c < n_odd; c++) {
            double d = rank_sh[c] - rank_P[c];
            d2_sum += d * d;
        }
        double spearman = 1.0 - 6.0 * d2_sum / (n_odd * ((double)n_odd*n_odd - 1));

        /* Average |P| for top 3 |s_hat| characters */
        double top3_P = 0;
        int top3_n = 0;
        for (int c = 0; c < n_odd && top3_n < 3; c++) {
            /* Find c-th largest sh_mag */
            int best = -1;
            double best_val = -1;
            for (int i = 0; i < n_odd; i++) {
                if (rank_sh[i] == c) { best = i; break; }
            }
            if (best >= 0) {
                top3_P += P_mag[best];
                top3_n++;
            }
        }
        top3_P /= top3_n;

        /* Average |P| overall */
        double avg_P = sy / n;

        printf("%5d %4d %+8.4f %+8.4f %8.4f (avg=%.4f)\n",
               b, n_odd, corr, spearman, top3_P, avg_P);
    }

    return 0;
}
