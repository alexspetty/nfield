/*
 * coarse_fine.c - Decompose B1 into coarse and fine components.
 *
 * P = sum_{k=1}^{b-1} chi_bar(k)       (partial sum, coarse)
 * Q = sum_{k=1}^{b-1} k chi_bar(k)     (weighted partial sum)
 * F = sum_{j=0}^{b-1} j chi_bar(1+jb)  (fine subgroup sum)
 * B1 = (1/m) sum_a a chi_bar(a)        (full Bernoulli)
 *
 * Identity: m*B1 = b*F*Q - b^2*(mixed term)
 *
 * Check: what is |P|/|B1| in terms of |F|, |Q|?
 * Is there a universal ratio?
 */

#include <stdio.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    int bases[] = {5, 7, 11, 13};
    int nb = 4;
    double PI = acos(-1.0);

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;
        int phi = b * (b-1);

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

        int dlog[m];
        memset(dlog, -1, sizeof(int)*m);
        { int v=1; for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);} }

        int dl_m1 = dlog[m-1];

        printf("=== Base %d ===\n", b);
        printf("%4s %8s %8s %8s %8s %8s %8s %8s\n",
               "j", "|P|", "|Q|", "|F|", "|B1|",
               "P/B1", "Q/P", "F*Q/(m*B1/b)");

        for (int j = 0; j < n_units; j++) {
            long long t = 2LL * j * dl_m1;
            if ((int)(t % (2*n_units)) != n_units) continue;

            /* P = sum chi_bar(k) for k=1..b-1 */
            double P_re=0, P_im=0;
            for (int k = 1; k <= b-1; k++) {
                if (dlog[k] < 0) continue;
                double angle = -2*PI*j*dlog[k]/(double)n_units;
                P_re += cos(angle); P_im += sin(angle);
            }
            double P_mag = sqrt(P_re*P_re + P_im*P_im);

            /* Q = sum k*chi_bar(k) for k=1..b-1 */
            double Q_re=0, Q_im=0;
            for (int k = 1; k <= b-1; k++) {
                if (dlog[k] < 0) continue;
                double angle = -2*PI*j*dlog[k]/(double)n_units;
                Q_re += k*cos(angle); Q_im += k*sin(angle);
            }
            double Q_mag = sqrt(Q_re*Q_re + Q_im*Q_im);

            /* F = sum j*chi_bar(1+jb) for j=0..b-1 */
            double F_re=0, F_im=0;
            for (int jj = 0; jj < b; jj++) {
                int elem = 1 + jj*b;
                if (elem >= m) elem %= m;
                if (dlog[elem] < 0) continue;
                double angle = -2*PI*j*dlog[elem]/(double)n_units;
                F_re += jj*cos(angle); F_im += jj*sin(angle);
            }
            double F_mag = sqrt(F_re*F_re + F_im*F_im);

            /* B1 = (1/m) sum a*chi_bar(a) */
            double B1_re=0, B1_im=0;
            for (int a = 1; a < m; a++) {
                if (dlog[a] < 0) continue;
                double angle = -2*PI*j*dlog[a]/(double)n_units;
                B1_re += a*cos(angle)/m; B1_im += a*sin(angle)/m;
            }
            double B1_mag = sqrt(B1_re*B1_re + B1_im*B1_im);

            if (P_mag < 1e-6 || B1_mag < 1e-6) continue;

            double PoverB1 = P_mag / B1_mag;
            double QoverP = Q_mag / P_mag;

            /* Check: is F*Q related to m*B1/b? */
            double FQ = F_mag * Q_mag;
            double mB1b = m * B1_mag / b;
            double ratio_FQ = FQ / mB1b;

            printf("%4d %8.3f %8.3f %8.3f %8.3f %8.4f %8.4f %8.4f\n",
                   j, P_mag, Q_mag, F_mag, B1_mag,
                   PoverB1, QoverP, ratio_FQ);
        }

        /* Theoretical |F| = b / (2 sin(pi*r/b)) for some r */
        printf("\n  |F| theoretical: b/(2*sin(pi*r/b)) for r=1..b-1:\n  ");
        for (int r = 1; r < b; r++)
            printf(" r=%d:%.3f", r, b/(2*sin(PI*r/b)));
        printf("\n\n");
    }

    return 0;
}
