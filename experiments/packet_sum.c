/*
 * packet_sum.c - Compute the actual packet sum for each chi.
 *
 * P_tilde(chi) = L(1, chi_bar) + (i/phi(b)) sum_{xi even} tau(xi_bar) L(1, xi*chi_bar)
 *
 * Compare |P_tilde| with |L(1)| to see how much the packet adds/subtracts.
 *
 * The packet's contribution is:
 *   Delta = (i/phi(b)) sum tau(xi_bar) L(1, xi*chi_bar)
 *
 * Check: |Delta| / |L(1)| as a function of b.
 * If |Delta| ~ |L|/log(b), the correlation decay follows.
 * If |Delta| ~ |L|/sqrt(b), the correlation decay is faster.
 */

#include <stdio.h>
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
    int phi_b = b - 1;
    int units[m], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    /* Generator mod m */
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

    /* Generator mod b */
    int h = -1;
    for (int c = 2; c < b; c++) {
        int v = 1, o = 0;
        do { v=v*c%b; o++; } while (v!=1);
        if (o == phi_b) { h = c; break; }
    }
    if (h < 0) return;

    int dlog_b[b];
    memset(dlog_b, -1, sizeof(dlog_b));
    { int v=1; for(int k=0;k<phi_b;k++){dlog_b[v]=k;v=v*h%b;} }

    int dl_m1 = dlog[m-1];
    int odd_j[1000]; int n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 1000; j++) {
        long long t = 2LL * j * dl_m1;
        if ((int)(t%(2*n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* For each odd chi, compute:
     * 1. L(1, chi) and L(1, chi_bar) [complex]
     * 2. For each even xi mod b: L(1, xi*chi_bar) [complex]
     * 3. tau(xi_bar) for each even xi
     * 4. The packet Delta = (i/phi_b) sum tau(xi_bar) L(1, xi*chi_bar)
     * 5. P_tilde = L(1, chi_bar) + Delta
     */

    /* Gauss sums tau(xi) for even xi mod b */
    /* tau(xi_j) = sum_{a=1}^{b-1} xi_j(a) e^{2*pi*i*a/b} */
    /* xi_j even means j_b even */
    int n_even = phi_b / 2;
    int even_jb[100]; int ne = 0;
    for (int jb = 0; jb < phi_b; jb += 2)
        even_jb[ne++] = jb;

    double tau_re[100], tau_im[100];
    for (int ei = 0; ei < ne; ei++) {
        int jb = even_jb[ei];
        double re = 0, im = 0;
        for (int a = 1; a < b; a++) {
            double xi_angle = 2*M_PI*jb*dlog_b[a]/(double)phi_b;
            double add_angle = 2*M_PI*a/(double)b;
            re += cos(xi_angle + add_angle);
            im += sin(xi_angle + add_angle);
        }
        tau_re[ei] = re;
        tau_im[ei] = im;
    }

    /* Stats accumulators */
    double sum_delta_over_L = 0;
    double sum_delta_over_L2 = 0;
    int cnt = 0;

    for (int ci = 0; ci < n_odd; ci++) {
        int j = odd_j[ci];

        /* L(1, chi_bar): use chi_bar = chi with index -j */
        /* Actually, for the Apostol formula, we need specific L-values.
         * Let me compute L(1, chi) first, then handle the twists. */

        /* L(1, chi_j) via Euler product */
        double logL_re = 0, logL_im = 0;
        for (int p = 2; p < MAX_PRIME; p++) {
            if (!is_prime(p) || p == b) continue;
            int dl = dlog[p%m]; if (dl < 0) continue;
            double angle = 2*M_PI*j*dl/(double)n_units;
            double w_re = 1-cos(angle)/p, w_im = -sin(angle)/p;
            double mag2 = w_re*w_re + w_im*w_im;
            if (mag2 > 1e-30) {
                logL_re -= 0.5*log(mag2);
                logL_im -= atan2(w_im, w_re);
            }
        }
        double L_chi_re = exp(logL_re)*cos(logL_im);
        double L_chi_im = exp(logL_re)*sin(logL_im);
        double L_chi_mag = exp(logL_re);

        /* For each even xi, compute L(1, xi * chi_bar).
         * chi_bar has index -j. xi has index jb (mod b component).
         * The product xi*chi_bar evaluated at prime p is:
         * xi(p mod b) * chi_bar(p) = e^{2pi i jb dlog_b(p%b)/phi_b} * e^{-2pi i j dlog(p%m)/phi_m}
         */

        double Delta_re = 0, Delta_im = 0;

        for (int ei = 1; ei < ne; ei++) { /* skip trivial xi (ei=0, jb=0) */
            int jb = even_jb[ei];

            /* L(1, xi_{jb} * chi_bar_j) via Euler product */
            double tL_re = 0, tL_im = 0;
            for (int p = 2; p < MAX_PRIME; p++) {
                if (!is_prime(p) || p == b) continue;
                int dl = dlog[p%m]; if (dl < 0) continue;
                int pb = p % b; if (pb == 0) continue;
                int dlb = dlog_b[pb]; if (dlb < 0) continue;

                /* (xi*chi_bar)(p) */
                double angle = 2*M_PI*(jb*dlb/(double)phi_b - j*dl/(double)n_units);
                double w_re = 1-cos(angle)/p, w_im = -sin(angle)/p;
                double mag2 = w_re*w_re + w_im*w_im;
                if (mag2 > 1e-30) {
                    tL_re -= 0.5*log(mag2);
                    tL_im -= atan2(w_im, w_re);
                }
            }
            double Lt_re = exp(tL_re)*cos(tL_im);
            double Lt_im = exp(tL_re)*sin(tL_im);

            /* tau(xi_bar) * L(1, xi*chi_bar) */
            /* tau_bar = conj(tau) for the conjugate */
            double tb_re = tau_re[ei], tb_im = -tau_im[ei]; /* conj of tau */
            double prod_re = tb_re*Lt_re - tb_im*Lt_im;
            double prod_im = tb_re*Lt_im + tb_im*Lt_re;

            Delta_re += prod_re;
            Delta_im += prod_im;
        }

        /* Scale by i/phi_b */
        /* i * (Delta_re + i*Delta_im) = -Delta_im + i*Delta_re */
        double scaled_re = -Delta_im / phi_b;
        double scaled_im = Delta_re / phi_b;

        double delta_mag = sqrt(scaled_re*scaled_re + scaled_im*scaled_im);
        double ratio = (L_chi_mag > 0.01) ? delta_mag / L_chi_mag : 0;

        if (L_chi_mag > 0.01 && delta_mag > 1e-6) {
            sum_delta_over_L += ratio;
            sum_delta_over_L2 += ratio * ratio;
            cnt++;
        }
    }

    double mean_ratio = sum_delta_over_L / cnt;
    double var = sum_delta_over_L2/cnt - mean_ratio*mean_ratio;
    printf("Base %2d: mean |Delta|/|L| = %.4f, std = %.4f (%d chars), "
           "1/sqrt(b)=%.4f, 1/log(b)=%.4f\n",
           b, mean_ratio, sqrt(var > 0 ? var : 0), cnt,
           1.0/sqrt(b), 1.0/log(b));
}

int main(void) {
    int bases[] = {5, 7, 11, 13, 17, 19, 23, 29, 31};
    for (int i = 0; i < 9; i++)
        run_base(bases[i]);
    return 0;
}
