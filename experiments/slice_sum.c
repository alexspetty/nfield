/*
 * slice_sum.c - Compute the good-slice character sum
 *
 * S_G(chi) = sum_{n in G} [chi_bar(n+1) - chi_bar(n)]
 *
 * If this has stable nonzero magnitude, the slice
 * transparency conjecture follows from the Bernoulli
 * connection.
 *
 * Check: is |S_G(chi)| proportional to |s_hat(chi)| / |L(1,chi)|?
 * If so, the mechanism is confirmed.
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
    int b = 13;
    int m = b * b; /* 169 */
    int ell = 1;

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

    int dlog[m];
    memset(dlog, -1, sizeof(int) * m);
    { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * g % m); } }

    /* Good slice set G: n such that floor(n/b^ell) = n mod b */
    /* For ell=1: floor(n/b) = n mod b, where 0 <= n < m = b^2 */
    int G[m], nG = 0;
    for (int n = 0; n < m; n++) {
        if (n / b == n % b)  /* floor(n/b^1) = n mod b */
            G[nG++] = n;
    }
    printf("Base %d, m=%d, phi=%d, |G|=%d\n", b, m, n_units, nG);
    printf("Good slices: ");
    for (int i = 0; i < nG && i < 20; i++) printf("%d ", G[i]);
    printf("\n\n");

    /* Find odd characters */
    int dl_m1 = dlog[m - 1];
    int odd_j[500], n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 500; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* Build S, center, compute |s_hat| */
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

    /* Compute |L(0.7, chi)| */
    double L_mag[500];
    memset(L_mag, 0, sizeof(double) * n_odd);
    for (int p = 2; p < MAX_PRIME; p++) {
        if (!is_prime(p) || p == b) continue;
        int dl = dlog[p % m];
        if (dl < 0) continue;
        double ps = pow((double)p, -0.7);
        for (int c = 0; c < n_odd; c++) {
            double angle = 2 * M_PI * odd_j[c] * dl / (double)n_units;
            double re = 1 - cos(angle) * ps;
            double im = -sin(angle) * ps;
            double mag2 = re*re + im*im;
            if (mag2 > 1e-30) L_mag[c] -= 0.5 * log(mag2);
        }
    }
    for (int c = 0; c < n_odd; c++) L_mag[c] = exp(L_mag[c]);

    /* Compute S_G(chi) = sum_{n in G} [chi_bar(n+1) - chi_bar(n)] */
    double SG_re[500], SG_im[500], SG_mag[500];
    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];
        double re = 0, im = 0;

        for (int gi = 0; gi < nG; gi++) {
            int n = G[gi];
            int n1 = n + 1;

            /* chi_bar(n+1) - chi_bar(n) */
            /* chi_bar(a) = exp(-2*pi*i * j * dlog[a] / phi) */
            /* Need a coprime to m for dlog to exist */

            double re_n1 = 0, im_n1 = 0;
            double re_n = 0, im_n = 0;

            if (n1 < m && gcd(n1, m) == 1 && dlog[n1] >= 0) {
                double angle = -2 * M_PI * j * dlog[n1] / (double)n_units;
                re_n1 = cos(angle);
                im_n1 = sin(angle);
            }

            if (n > 0 && gcd(n, m) == 1 && dlog[n] >= 0) {
                double angle = -2 * M_PI * j * dlog[n] / (double)n_units;
                re_n = cos(angle);
                im_n = sin(angle);
            }

            re += (re_n1 - re_n);
            im += (im_n1 - im_n);
        }

        SG_re[c] = re;
        SG_im[c] = im;
        SG_mag[c] = sqrt(re*re + im*im);
    }

    /* Print comparison */
    printf("%4s %8s %8s %8s %8s %8s\n",
           "c", "|sh|", "|L|", "|SG|", "|sh|/|L|", "|SG|");

    for (int c = 0; c < n_odd && c < 20; c++) {
        double ratio = L_mag[c] > 0.01 ? sh_mag[c] / L_mag[c] : 0;
        printf("%4d %8.4f %8.4f %8.4f %8.4f %8.4f\n",
               c, sh_mag[c], L_mag[c], SG_mag[c],
               ratio, SG_mag[c]);
    }

    /* Correlations */
    double sx=0,sy=0,sxx=0,syy=0,sxy=0;
    int cnt = 0;
    for (int c = 0; c < n_odd; c++) {
        if (sh_mag[c] < 1e-10) continue;
        double x = sh_mag[c], y = SG_mag[c];
        sx+=x; sy+=y; sxx+=x*x; syy+=y*y; sxy+=x*y;
        cnt++;
    }
    double mx=sx/cnt, my=sy/cnt;
    double vx=sxx/cnt-mx*mx, vy=syy/cnt-my*my;
    double cv=sxy/cnt-mx*my;
    double r_sh_SG = (vx>0&&vy>0) ? cv/sqrt(vx*vy) : 0;

    /* corr(|SG|, |L|) */
    sx=sy=sxx=syy=sxy=0; cnt=0;
    for (int c = 0; c < n_odd; c++) {
        if (SG_mag[c] < 1e-10) continue;
        double x = SG_mag[c], y = L_mag[c];
        sx+=x; sy+=y; sxx+=x*x; syy+=y*y; sxy+=x*y;
        cnt++;
    }
    mx=sx/cnt; my=sy/cnt;
    vx=sxx/cnt-mx*mx; vy=syy/cnt-my*my;
    cv=sxy/cnt-mx*my;
    double r_SG_L = (vx>0&&vy>0) ? cv/sqrt(vx*vy) : 0;

    /* corr(|sh|/|L|, |SG|) -- if sh ~ L * SG, this should be high */
    sx=sy=sxx=syy=sxy=0; cnt=0;
    for (int c = 0; c < n_odd; c++) {
        if (sh_mag[c] < 1e-10 || L_mag[c] < 0.01) continue;
        double x = sh_mag[c] / L_mag[c], y = SG_mag[c];
        sx+=x; sy+=y; sxx+=x*x; syy+=y*y; sxy+=x*y;
        cnt++;
    }
    mx=sx/cnt; my=sy/cnt;
    vx=sxx/cnt-mx*mx; vy=syy/cnt-my*my;
    cv=sxy/cnt-mx*my;
    double r_ratio_SG = (vx>0&&vy>0) ? cv/sqrt(vx*vy) : 0;

    printf("\nCorrelations:\n");
    printf("  corr(|sh|, |SG|)      = %+.4f\n", r_sh_SG);
    printf("  corr(|SG|, |L|)       = %+.4f\n", r_SG_L);
    printf("  corr(|sh|/|L|, |SG|)  = %+.4f\n", r_ratio_SG);

    printf("\nIf |sh| ~ |L| * |SG|, then |sh|/|L| ~ |SG|.\n");
    printf("corr(|sh|/|L|, |SG|) = %.4f tells us if the\n", r_ratio_SG);
    printf("factorization holds.\n");

    return 0;
}
