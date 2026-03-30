/*
 * higher_lag.c - Anti-correlation and sign structure at higher lags.
 *
 * At lag ℓ, the modulus is m = b^(ℓ+1) and the multiplier is g = b^ℓ.
 * More characters, more structure. Does the anti-correlation persist?
 *
 * Start with base 3 (smallest, fastest) at lags 1, 2, 3, 4.
 * Then base 5 at lags 1, 2, 3.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000
#define MAX_UNITS 5000
#define MAX_M 10000

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

static long long power(int base, int exp) {
    long long r = 1;
    for (int i = 0; i < exp; i++) r *= base;
    return r;
}

void run(int b, int lag) {
    long long m_ll = power(b, lag + 1);
    if (m_ll > MAX_M) {
        printf("%5d %4d %6lld  (too large)\n", b, lag, m_ll);
        return;
    }
    int m = (int)m_ll;
    int g_mult = (int)power(b, lag); /* multiplier = b^lag */

    int units[MAX_UNITS], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    /* Find primitive root */
    int prim = -1;
    for (int c = 2; c < m; c++) {
        if (gcd(c, m) != 1) continue;
        int v = 1, o = 0;
        do { v = (int)((long long)v * c % m); o++; } while (v != 1);
        if (o == n_units) { prim = c; break; }
    }
    if (prim < 0) {
        printf("%5d %4d %6d %5d  (no prim root)\n", b, lag, m, n_units);
        return;
    }

    int *dlog = calloc(m, sizeof(int));
    for (int i = 0; i < m; i++) dlog[i] = -1;
    { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * prim % m); } }

    /* Build S table at this lag.
     * S_ℓ(p) = C(b^ℓ mod p) - floor((p-1)/b)
     * C(g) = #{r : floor(br/p) = floor(b*(gr mod p)/p)}
     * But we use finite determination: S depends on p mod m.
     * Compute for small primes to fill the table. */
    int *S = calloc(m, sizeof(int));
    int *has_S = calloc(m, sizeof(int));

    for (int p = m + 1; p < 200000 && p < MAX_PRIME; p++) {
        if (!is_prime(p) || gcd(p, b) != 1) continue;
        int a = p % m;
        if (has_S[a]) continue;

        /* Compute collision count C(g_mult mod p) */
        int gp = g_mult % p;
        int C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)b * r / p);
            int d2 = (int)((long long)b * ((long long)gp * r % p) / p);
            if (d1 == d2) C++;
        }
        S[a] = C - (p - 1) / b;
        has_S[a] = 1;
    }

    /* Center by spectral class R = (a-1) mod b */
    double *cls_sum = calloc(b, sizeof(double));
    int *cls_cnt = calloc(b, sizeof(int));
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (!has_S[a]) continue;
        int R = (a - 1) % b;
        cls_sum[R] += S[a];
        cls_cnt[R]++;
    }
    double *mean_R = calloc(b, sizeof(double));
    for (int R = 0; R < b; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    double *Sc = calloc(m, sizeof(double));
    int *has_Sc = calloc(m, sizeof(int));
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (!has_S[a]) continue;
        Sc[a] = S[a] - mean_R[(a - 1) % b];
        has_Sc[a] = 1;
    }

    int dl_m1 = dlog[m - 1];

    /* Find odd characters */
    int *odd_j = calloc(n_units, sizeof(int));
    int n_odd = 0;
    for (int j = 0; j < n_units; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* Compute s_hat and P(0.5) */
    double *sh_re = calloc(n_odd, sizeof(double));
    double *sh_im = calloc(n_odd, sizeof(double));
    double *P_re = calloc(n_odd, sizeof(double));
    double *P_im = calloc(n_odd, sizeof(double));

    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_Sc[a]) continue;
            double angle = -2 * M_PI * j * dlog[a] / (double)n_units;
            sh_re[c] += Sc[a] * cos(angle);
            sh_im[c] += Sc[a] * sin(angle);
        }
        sh_re[c] /= n_units;
        sh_im[c] /= n_units;
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

    /* Compute sign split, net, and anti-correlation */
    int n_pos = 0, n_neg = 0;
    double net = 0;
    double sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0;
    int n_corr = 0;

    for (int c = 0; c < n_odd; c++) {
        double prod = sh_re[c]*P_re[c] - sh_im[c]*P_im[c];
        net += prod;
        if (prod >= -1e-10) n_pos++; else n_neg++;

        double sh_mag = sqrt(sh_re[c]*sh_re[c] + sh_im[c]*sh_im[c]);
        double P_mag = sqrt(P_re[c]*P_re[c] + P_im[c]*P_im[c]);
        if (sh_mag < 1e-10) continue;
        sx += sh_mag; sy += P_mag;
        sxx += sh_mag*sh_mag; syy += P_mag*P_mag;
        sxy += sh_mag*P_mag;
        n_corr++;
    }

    double mx = sx/n_corr, my = sy/n_corr;
    double vx = sxx/n_corr - mx*mx, vy = syy/n_corr - my*my;
    double cov = sxy/n_corr - mx*my;
    double corr = (vx > 0 && vy > 0) ? cov / sqrt(vx*vy) : 0;

    printf("%5d %4d %6d %5d %5d %4d+/%-4d %+8.3f %+7.3f\n",
           b, lag, m, n_units, n_odd, n_pos, n_neg, net, corr);

    free(dlog); free(S); free(has_S); free(cls_sum); free(cls_cnt);
    free(mean_R); free(Sc); free(has_Sc); free(odd_j);
    free(sh_re); free(sh_im); free(P_re); free(P_im);
}

int main(void) {
    printf("%5s %4s %6s %5s %5s %10s %8s %7s\n",
           "base", "lag", "m", "phi", "odd", "sign", "net", "corr");

    /* Base 3: lags 1-5 (m = 9, 27, 81, 243, 729) */
    for (int lag = 1; lag <= 7; lag++) run(3, lag);
    printf("\n");

    /* Base 5: lags 1-3 (m = 25, 125, 625) */
    for (int lag = 1; lag <= 4; lag++) run(5, lag);
    printf("\n");

    /* Base 7: lags 1-3 (m = 49, 343, 2401) */
    for (int lag = 1; lag <= 3; lag++) run(7, lag);

    return 0;
}
