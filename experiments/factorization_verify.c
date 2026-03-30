/*
 * factorization_verify.c - Verify S_G = -2 chi_bar(b+1) sum_{k=1}^{b-1} chi_bar(k)
 * and check if |sum chi_bar(k)| ~ |L(1, chi)|.
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

    /* For each odd character, compute:
     * 1. S_G directly (sum over good slices)
     * 2. The formula: -2 chi_bar(b+1) sum_{k=1}^{b-1} chi_bar(k)
     * 3. |partial sum| = |sum_{k=1}^{b-1} chi_bar(k)|
     * 4. |L(1, chi)| via Euler product
     */

    int dl_bp1 = dlog[(b+1) % m]; /* dlog of b+1 */

    printf("=== Base %d (m=%d, %d odd chars) ===\n", b, m, n_odd);

    double sum_ratio = 0;
    int cnt = 0;
    int n_verify_ok = 0;

    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];

        /* 1. S_G directly */
        double sg_re = 0, sg_im = 0;
        for (int kk = 0; kk < b; kk++) {
            int n = kk * (b+1);
            int n1 = (n+1) % m;
            int n_mod = n % m;

            double re_n1=0,im_n1=0,re_n=0,im_n=0;
            if (n1>0 && n1<m && gcd(n1,m)==1 && dlog[n1]>=0) {
                double angle = -2*M_PI*j*dlog[n1]/(double)n_units;
                re_n1=cos(angle); im_n1=sin(angle);
            }
            if (n_mod>0 && gcd(n_mod,m)==1 && dlog[n_mod]>=0) {
                double angle = -2*M_PI*j*dlog[n_mod]/(double)n_units;
                re_n=cos(angle); im_n=sin(angle);
            }
            sg_re += re_n1 - re_n;
            sg_im += im_n1 - im_n;
        }

        /* 2. Formula: -2 chi_bar(b+1) * partial_sum */
        double ps_re = 0, ps_im = 0;
        for (int k = 1; k <= b-1; k++) {
            if (dlog[k] < 0) continue;
            double angle = -2*M_PI*j*dlog[k]/(double)n_units;
            ps_re += cos(angle);
            ps_im += sin(angle);
        }

        /* chi_bar(b+1) */
        double cb_re = 0, cb_im = 0;
        if (dl_bp1 >= 0) {
            double angle = -2*M_PI*j*dl_bp1/(double)n_units;
            cb_re = cos(angle);
            cb_im = sin(angle);
        }

        /* -2 * chi_bar(b+1) * partial_sum */
        double formula_re = -2 * (cb_re*ps_re - cb_im*ps_im);
        double formula_im = -2 * (cb_re*ps_im + cb_im*ps_re);

        /* Verify */
        double err = sqrt((sg_re-formula_re)*(sg_re-formula_re) +
                         (sg_im-formula_im)*(sg_im-formula_im));
        if (err < 1e-8) n_verify_ok++;

        double ps_mag = sqrt(ps_re*ps_re + ps_im*ps_im);
        double sg_mag = sqrt(sg_re*sg_re + sg_im*sg_im);

        /* 4. |L(1, chi)| */
        double logL = 0;
        for (int p = 2; p < MAX_PRIME; p++) {
            if (!is_prime(p) || p == b) continue;
            int dl = dlog[p%m];
            if (dl < 0) continue;
            double angle = 2*M_PI*j*dl/(double)n_units;
            double re = 1 - cos(angle)/p;
            double im = sin(angle)/p;
            double mag2 = re*re + im*im;
            if (mag2 > 1e-30) logL -= 0.5*log(mag2);
        }
        double L1 = exp(logL);

        if (ps_mag > 0.01 && L1 > 0.01) {
            double ratio = ps_mag / L1;
            sum_ratio += ratio;
            cnt++;
        }
    }

    printf("  Formula verified: %d/%d characters\n", n_verify_ok, n_odd);
    if (cnt > 0)
        printf("  Mean |partial_sum| / |L(1)| = %.4f (%d chars)\n",
               sum_ratio / cnt, cnt);

    /* More detail: print ratio for each character */
    printf("\n  %4s %8s %8s %8s\n", "c", "|ps|", "|L(1)|", "ratio");
    for (int c = 0; c < n_odd && c < 15; c++) {
        int j = odd_j[c];

        double ps_re=0, ps_im=0;
        for (int k = 1; k <= b-1; k++) {
            if (dlog[k] < 0) continue;
            double angle = -2*M_PI*j*dlog[k]/(double)n_units;
            ps_re += cos(angle); ps_im += sin(angle);
        }
        double ps_mag = sqrt(ps_re*ps_re + ps_im*ps_im);

        double logL = 0;
        for (int p = 2; p < MAX_PRIME; p++) {
            if (!is_prime(p) || p == b) continue;
            int dl = dlog[p%m];
            if (dl < 0) continue;
            double angle = 2*M_PI*j*dl/(double)n_units;
            double re = 1 - cos(angle)/p;
            double im = sin(angle)/p;
            double mag2 = re*re + im*im;
            if (mag2 > 1e-30) logL -= 0.5*log(mag2);
        }
        double L1 = exp(logL);

        double ratio = (L1 > 0.01) ? ps_mag / L1 : 0;
        printf("  %4d %8.4f %8.4f %8.4f\n", c, ps_mag, L1, ratio);
    }
    printf("\n");
}

int main(void) {
    int bases[] = {5, 7, 13};
    for (int i = 0; i < 3; i++)
        run_base(bases[i]);
    return 0;
}
