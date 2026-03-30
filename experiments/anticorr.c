/*
 * anticorr.c - Test anti-correlation between |s_hat(chi)| and |P(s,chi)|
 * across odd characters, for multiple prime bases.
 *
 * If the collision invariant "avoids" the zero-sensitive characters,
 * large |s_hat| should pair with small |P| and vice versa.
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
    double s_vals[] = {1.0, 0.7, 0.5};
    int n_s = 3;

    printf("%5s %4s | ", "base", "odd");
    for (int si = 0; si < n_s; si++)
        printf("corr@%.1f  ", s_vals[si]);
    printf("\n");

    for (int b = 3; b <= 37; b++) {
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

        /* Find odd characters, compute |s_hat| and |P(s)| */
        int n_odd = 0;
        double sh_mag[n_units];
        double P_mag[n_units][3]; /* for each s value */

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
            sh_mag[n_odd] = sqrt(sh_re*sh_re + sh_im*sh_im);

            /* P(s) for each s */
            for (int si = 0; si < n_s; si++) {
                double P_re = 0, P_im = 0;
                double s = s_vals[si];
                for (int p = m + 1; p < MAX_PRIME; p++) {
                    if (!is_prime(p) || gcd(p, b) != 1) continue;
                    int a = p % m;
                    if (dlog[a] < 0) continue;
                    double angle = 2 * M_PI * j * dlog[a] / (double)n_units;
                    double w = pow((double)p, -s);
                    P_re += cos(angle) * w;
                    P_im += sin(angle) * w;
                }
                P_mag[n_odd][si] = sqrt(P_re*P_re + P_im*P_im);
            }
            n_odd++;
        }

        /* Compute Pearson correlation between |s_hat| and |P(s)| */
        printf("%5d %4d | ", b, n_odd);
        for (int si = 0; si < n_s; si++) {
            double sum_x = 0, sum_y = 0, sum_xx = 0, sum_yy = 0, sum_xy = 0;
            int n = 0;
            for (int i = 0; i < n_odd; i++) {
                if (sh_mag[i] < 1e-10) continue; /* skip zero coefficients */
                double x = sh_mag[i];
                double y = P_mag[i][si];
                sum_x += x; sum_y += y;
                sum_xx += x*x; sum_yy += y*y;
                sum_xy += x*y;
                n++;
            }
            double mx = sum_x / n, my = sum_y / n;
            double vx = sum_xx/n - mx*mx;
            double vy = sum_yy/n - my*my;
            double cov = sum_xy/n - mx*my;
            double corr = (vx > 0 && vy > 0) ? cov / sqrt(vx * vy) : 0;
            printf("%+.4f   ", corr);
        }
        printf("\n");
    }

    return 0;
}
