/*
 * twist_moment.c - Compute the twist-correlation matrix C(xi).
 *
 * C(xi) = (1/n) sum_{chi primitive odd mod b^2}
 *         L(1, chi) * conj(L(1, xi*chi))
 *
 * for even characters xi mod b.
 *
 * The diagonal C(1) = (1/n) sum |L(1,chi)|^2 is always positive.
 * The off-diagonals involve twisted products.
 *
 * The correlation corr(|P|, |L|) is determined by whether
 * the off-diagonals cancel enough of the diagonal.
 *
 * If |sum C(xi)| << C(1), then P ~ L(1) and correlation ~ 1.
 * If |sum C(xi)| ~ C(1), then the packet cancels the signal
 * and correlation drops.
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

    /* Find odd characters mod m */
    int odd_j[1000]; int n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 1000; j++) {
        long long t = 2LL * j * dl_m1;
        if ((int)(t%(2*n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* Compute L(1, chi_j) for each odd character as complex number */
    double L_re[1000], L_im[1000];
    memset(L_re, 0, sizeof(double)*n_odd);
    memset(L_im, 0, sizeof(double)*n_odd);

    /* Use Euler product */
    for (int p = 2; p < MAX_PRIME; p++) {
        if (!is_prime(p) || p == b) continue;
        int dl = dlog[p%m]; if (dl < 0) continue;

        for (int ci = 0; ci < n_odd; ci++) {
            int j = odd_j[ci];
            double angle = 2*M_PI*j*dl/(double)n_units;
            double w_re = 1 - cos(angle)/p, w_im = -sin(angle)/p;
            double mag2 = w_re*w_re + w_im*w_im;
            if (mag2 > 1e-30) {
                double logmag = -0.5*log(mag2);
                double arg = -atan2(w_im, w_re);
                L_re[ci] += logmag; /* accumulating log|L| and arg(L) */
                L_im[ci] += arg;
            }
        }
    }
    /* Convert from log to actual */
    for (int ci = 0; ci < n_odd; ci++) {
        double mag = exp(L_re[ci]);
        double arg = L_im[ci];
        L_re[ci] = mag * cos(arg);
        L_im[ci] = mag * sin(arg);
    }

    /* Even characters mod b: xi with xi(-1) = +1 */
    /* For prime b: (Z/bZ)* is cyclic of order b-1.
     * Generator h of (Z/bZ)*. Even characters have
     * xi(-1) = 1, i.e., xi(b-1) = 1.
     * dlog_b(-1) = (b-1)/2 for the generator of (Z/bZ)*.
     * Even means j_b * (b-1)/2 = 0 mod (b-1), i.e., j_b even.
     */

    /* Find generator mod b */
    int h = -1;
    for (int c = 2; c < b; c++) {
        int v = 1, o = 0;
        do { v = v*c%b; o++; } while (v != 1);
        if (o == b-1) { h = c; break; }
    }

    int dlog_b[b];
    memset(dlog_b, -1, sizeof(dlog_b));
    if (h > 0) {
        int v = 1;
        for (int k = 0; k < b-1; k++) {
            dlog_b[v] = k;
            v = v * h % b;
        }
    }

    int n_even_b = (b-1)/2; /* number of even characters mod b */

    printf("Base %d: %d odd chars mod %d, %d even chars mod %d\n",
           b, n_odd, m, n_even_b, b);

    /* The twist-correlation:
     * For even xi_j (j_b = 0, 2, 4, ..., b-3 for prime b):
     * C(xi_j) = (1/n_odd) sum_chi L(1,chi) * conj(L(1, xi_j * chi))
     *
     * xi_j * chi: if chi has index j_m mod phi(m), and xi has index j_b
     * mod (b-1), the product xi*chi has a specific index in (Z/mZ)*.
     *
     * For simplicity: compute the MAGNITUDE version:
     * C_mag(xi) = (1/n) sum |L(1,chi)| * |L(1, xi*chi)|
     *
     * And compare diagonal (xi = trivial) with off-diagonal.
     *
     * Actually, for the Apostol formula, we need the COMPLEX C(xi).
     * But let me start with the magnitude version to see the structure.
     */

    /* Diagonal: C(1) = (1/n) sum |L(1)|^2 */
    double diag = 0;
    for (int ci = 0; ci < n_odd; ci++)
        diag += L_re[ci]*L_re[ci] + L_im[ci]*L_im[ci];
    diag /= n_odd;

    /* Off-diagonal: for each even xi mod b, compute
     * (1/n) sum_chi |L(1,chi)| * |L(1, xi*chi)|
     *
     * To compute L(1, xi*chi): xi acts on the coarse part (mod b)
     * of the character. The product xi*chi has a shifted index.
     *
     * For chi with index j in (Z/mZ)* and xi with index j_b in (Z/bZ)*:
     * The product xi*chi evaluated at a unit a has
     * (xi*chi)(a) = xi(a mod b) * chi(a)
     *
     * In terms of dlog: xi(a) = exp(2pi i j_b dlog_b(a mod b) / (b-1))
     *
     * So L(1, xi*chi) = sum_p (xi*chi)(p) / p
     *                  = sum_p xi(p mod b) chi(p) / p
     *
     * I need to recompute L for the twisted character.
     * For efficiency, I'll compute for each even j_b:
     * L_twisted(j_b, chi_ci) using the Euler product.
     */

    /* For each even j_b (0, 2, 4, ..., b-3): */
    printf("  Diagonal C(1) = %.6f\n", diag);

    double total_offdiag_mag = 0;
    int n_offdiag = 0;

    for (int jb = 0; jb < b-1; jb += 2) {
        /* Compute L(1, xi_{jb} * chi_{ci}) for each chi */
        double Lt_re[1000], Lt_im[1000];
        memset(Lt_re, 0, sizeof(double)*n_odd);
        memset(Lt_im, 0, sizeof(double)*n_odd);

        for (int p = 2; p < MAX_PRIME; p++) {
            if (!is_prime(p) || p == b) continue;
            int dl = dlog[p%m]; if (dl < 0) continue;
            int pb = p % b;
            if (pb == 0) continue;
            int dl_b = dlog_b[pb];
            if (dl_b < 0) continue;

            double xi_angle = 2*M_PI*jb*dl_b/(double)(b-1);
            double xi_re = cos(xi_angle), xi_im = sin(xi_angle);

            for (int ci = 0; ci < n_odd; ci++) {
                int j = odd_j[ci];
                double chi_angle = 2*M_PI*j*dl/(double)n_units;
                double chi_re = cos(chi_angle), chi_im = sin(chi_angle);

                /* (xi*chi)(p) = xi(p) * chi(p) */
                double xc_re = xi_re*chi_re - xi_im*chi_im;
                double xc_im = xi_re*chi_im + xi_im*chi_re;

                /* 1 - (xi*chi)(p)/p */
                double w_re = 1 - xc_re/p, w_im = -xc_im/p;
                double mag2 = w_re*w_re + w_im*w_im;
                if (mag2 > 1e-30) {
                    Lt_re[ci] -= 0.5*log(mag2);
                    Lt_im[ci] -= atan2(w_im, w_re);
                }
            }
        }

        /* Convert log to actual */
        for (int ci = 0; ci < n_odd; ci++) {
            double mag = exp(Lt_re[ci]);
            double arg = Lt_im[ci];
            Lt_re[ci] = mag * cos(arg);
            Lt_im[ci] = mag * sin(arg);
        }

        /* C(xi_{jb}) = (1/n) sum L(1,chi) * conj(L(1,xi*chi)) */
        double C_re = 0, C_im = 0;
        for (int ci = 0; ci < n_odd; ci++) {
            /* L * conj(Lt) */
            C_re += L_re[ci]*Lt_re[ci] + L_im[ci]*Lt_im[ci];
            C_im += L_im[ci]*Lt_re[ci] - L_re[ci]*Lt_im[ci];
        }
        C_re /= n_odd;
        C_im /= n_odd;

        double C_mag = sqrt(C_re*C_re + C_im*C_im);

        if (jb > 0) {
            total_offdiag_mag += C_mag;
            n_offdiag++;
        }

        printf("  C(xi_%d) = (%+.4f, %+.4f), |C| = %.4f, |C|/C(1) = %.4f\n",
               jb, C_re, C_im, C_mag, C_mag / diag);
    }

    double mean_offdiag = total_offdiag_mag / n_offdiag;
    printf("  Mean |off-diagonal| = %.4f, ratio to diagonal = %.4f\n",
           mean_offdiag, mean_offdiag / diag);
    printf("  Number of off-diag terms: %d\n", n_offdiag);
    printf("  log(b) = %.4f\n\n", log(b));
}

int main(void) {
    int bases[] = {5, 7, 11, 13, 17, 19, 23};
    for (int i = 0; i < 7; i++)
        run_base(bases[i]);
    return 0;
}
