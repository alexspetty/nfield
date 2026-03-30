/*
 * ratio_test.c - Is |S_G(chi)| / |L(s,chi)| constant?
 *
 * If |S_G| = c * |L|, then the slice transparency
 * conjecture reduces to: the Bernoulli connection gives
 * |s_hat| = c' * |L|^2 (double encoding).
 *
 * Compute the ratio for all odd characters at multiple bases.
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

void run_base(int b) {
    int m = b * b;
    int units[m], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    int g = -1;
    for (int c = 2; c < m; c++) {
        if (gcd(c, m) != 1) continue;
        int v = 1, o = 0;
        do { v=(int)((long long)v*c%m); o++; } while (v!=1);
        if (o == n_units) { g = c; break; }
    }
    if (g < 0) return;

    int dlog[m];
    memset(dlog, -1, sizeof(int)*m);
    { int v=1; for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);} }

    int dl_m1 = dlog[m-1];
    int odd_j[1000], n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 1000; j++) {
        long long t = 2LL * j * dl_m1;
        if ((int)(t%(2*n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* Compute S_G for each odd character */
    double SG_mag[1000];
    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];
        double re = 0, im = 0;
        for (int k = 0; k < b; k++) {
            int n = k * (b + 1);
            int n1 = (n + 1) % m;
            int n_mod = n % m;

            double re_n1=0,im_n1=0,re_n=0,im_n=0;
            if (n1 > 0 && n1 < m && gcd(n1,m)==1 && dlog[n1]>=0) {
                double angle = -2*M_PI*j*dlog[n1]/(double)n_units;
                re_n1=cos(angle); im_n1=sin(angle);
            }
            if (n_mod > 0 && gcd(n_mod,m)==1 && dlog[n_mod]>=0) {
                double angle = -2*M_PI*j*dlog[n_mod]/(double)n_units;
                re_n=cos(angle); im_n=sin(angle);
            }
            re += re_n1 - re_n;
            im += im_n1 - im_n;
        }
        SG_mag[c] = sqrt(re*re + im*im);
    }

    /* Compute |L(1, chi)| via Euler product */
    double L1[1000];
    memset(L1, 0, sizeof(double)*n_odd);
    for (int p = 2; p < MAX_PRIME; p++) {
        if (!is_prime(p) || p == b) continue;
        int dl = dlog[p%m];
        if (dl < 0) continue;
        double ps = 1.0 / p;
        for (int c = 0; c < n_odd; c++) {
            double angle = 2*M_PI*odd_j[c]*dl/(double)n_units;
            double re = 1 - cos(angle)*ps;
            double im = -sin(angle)*ps;
            double mag2 = re*re + im*im;
            if (mag2 > 1e-30) L1[c] -= 0.5*log(mag2);
        }
    }
    for (int c = 0; c < n_odd; c++) L1[c] = exp(L1[c]);

    /* Compute ratio |S_G| / |L(1)| */
    double sum_ratio = 0, sum_ratio2 = 0;
    int cnt = 0;
    double min_ratio = 1e30, max_ratio = 0;

    for (int c = 0; c < n_odd; c++) {
        if (SG_mag[c] < 1e-6 || L1[c] < 0.01) continue;
        double ratio = SG_mag[c] / L1[c];
        sum_ratio += ratio;
        sum_ratio2 += ratio * ratio;
        if (ratio < min_ratio) min_ratio = ratio;
        if (ratio > max_ratio) max_ratio = ratio;
        cnt++;
    }

    double mean = sum_ratio / cnt;
    double var = sum_ratio2/cnt - mean*mean;
    double cv = sqrt(var) / mean; /* coefficient of variation */

    printf("%5d %4d %4d %8.3f %8.3f %8.3f %8.4f %8.4f\n",
           b, n_odd, cnt, mean, min_ratio, max_ratio,
           sqrt(var), cv);
}

int main(void) {
    printf("%5s %4s %4s %8s %8s %8s %8s %8s\n",
           "base", "n", "used", "mean", "min", "max", "std", "CV");

    int bases[] = {5, 7, 11, 13, 17, 19, 23, 29, 31};
    for (int i = 0; i < 9; i++)
        run_base(bases[i]);

    return 0;
}
