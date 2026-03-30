/*
 * largest_coeff.c - For each prime base b, find the largest collision
 * transform coefficient and check if it supports convergence.
 *
 * Question: does the largest |s_hat(chi)| always pair with a
 * positive Re(s_hat * P)?
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
    printf("%5s %4s %4s | %8s %5s | %8s %5s | %8s %5s | %9s\n",
           "base", "phi", "odd",
           "|sh|_1", "sign1",
           "|sh|_2", "sign2",
           "|sh|_3", "sign3",
           "net");

    for (int b = 3; b <= 37; b++) {
        if (!is_prime(b)) continue;
        int m = b * b;
        int units[m], n_units = 0;
        for (int a = 1; a < m; a++)
            if (gcd(a, m) == 1) units[n_units++] = a;

        /* Find primitive root */
        int g = -1;
        for (int cand = 2; cand < m; cand++) {
            if (gcd(cand, m) != 1) continue;
            int val = 1, ord = 0;
            do { val = (int)((long long)val * cand % m); ord++; } while (val != 1);
            if (ord == n_units) { g = cand; break; }
        }
        if (g < 0) continue;

        int dlog[m];
        memset(dlog, -1, sizeof(int) * m);
        { int val = 1; for (int k = 0; k < n_units; k++) { dlog[val] = k; val = (int)((long long)val * g % m); } }

        /* Build S table */
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

        /* Center */
        double cls_sum[b], cls_cnt_d[b];
        int cls_cnt[b];
        memset(cls_sum, 0, sizeof(double) * b);
        memset(cls_cnt, 0, sizeof(int) * b);
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_S[a]) continue;
            int R = (a - 1) % b;
            cls_sum[R] += S[a];
            cls_cnt[R]++;
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
            Sc[a] = S[a] - mean_R[(a - 1) % b];
            has_Sc[a] = 1;
        }

        /* dlog of -1 */
        int dl_m1 = dlog[m - 1];

        /* Find odd characters, compute s_hat and P(0.5) */
        int n_odd = 0;
        /* Store: index, |s_hat|, Re(s_hat*P), sign */
        typedef struct { int j; double sh_mag; double prod_re; } entry_t;
        entry_t entries[n_units];

        for (int j = 0; j < n_units; j++) {
            long long test = 2LL * j * dl_m1;
            if ((int)(test % (2 * n_units)) != n_units) continue;

            /* s_hat */
            double sh_re = 0, sh_im = 0;
            for (int i = 0; i < n_units; i++) {
                int a = units[i];
                if (!has_Sc[a]) continue;
                double angle = -2 * M_PI * j * dlog[a] / (double)n_units;
                sh_re += Sc[a] * cos(angle);
                sh_im += Sc[a] * sin(angle);
            }
            sh_re /= n_units;
            sh_im /= n_units;

            /* P(0.5) */
            double P_re = 0, P_im = 0;
            for (int p = m + 1; p < MAX_PRIME; p++) {
                if (!is_prime(p) || gcd(p, b) != 1) continue;
                int a = p % m;
                if (dlog[a] < 0) continue;
                double angle = 2 * M_PI * j * dlog[a] / (double)n_units;
                double w = 1.0 / sqrt((double)p);
                P_re += cos(angle) * w;
                P_im += sin(angle) * w;
            }

            double prod_re = sh_re * P_re - sh_im * P_im;
            entries[n_odd].j = j;
            entries[n_odd].sh_mag = sqrt(sh_re*sh_re + sh_im*sh_im);
            entries[n_odd].prod_re = prod_re;
            n_odd++;
        }

        /* Sort by |s_hat| descending */
        for (int i = 0; i < n_odd - 1; i++)
            for (int k = i + 1; k < n_odd; k++)
                if (entries[k].sh_mag > entries[i].sh_mag) {
                    entry_t tmp = entries[i];
                    entries[i] = entries[k];
                    entries[k] = tmp;
                }

        double net = 0;
        for (int i = 0; i < n_odd; i++) net += entries[i].prod_re;

        /* Report top 3 */
        char s1 = entries[0].prod_re >= -1e-10 ? '+' : '-';
        char s2 = n_odd > 1 ? (entries[1].prod_re >= -1e-10 ? '+' : '-') : '?';
        char s3 = n_odd > 2 ? (entries[2].prod_re >= -1e-10 ? '+' : '-') : '?';

        printf("%5d %4d %4d | %8.4f %5c | %8.4f %5c | %8.4f %5c | %+9.3f\n",
               b, n_units, n_odd,
               entries[0].sh_mag, s1,
               n_odd > 1 ? entries[1].sh_mag : 0, s2,
               n_odd > 2 ? entries[2].sh_mag : 0, s3,
               net);
    }

    return 0;
}
