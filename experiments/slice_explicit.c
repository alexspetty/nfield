/*
 * slice_explicit.c - Evaluate S_G explicitly.
 *
 * G = {0, b+1, 2(b+1), ..., (b-1)(b+1)} at lag 1.
 *
 * S_G(chi) = sum_{k=0}^{b-1} [chi_bar(k(b+1)+1) - chi_bar(k(b+1))]
 *
 * Since chi_bar is multiplicative and periodic mod m = b^2:
 *   chi_bar(k(b+1)) = chi_bar(k) * chi_bar(b+1)  (if gcd(k, m)=1)
 *   chi_bar(k(b+1)+1) depends on k(b+1)+1 mod m
 *
 * But k(b+1) = kb + k, and k(b+1) mod b^2 = k(b+1) for k < b.
 * So the terms are at positions 0, b+1, 2b+2, ..., (b-1)(b+1)=b^2-1.
 *
 * Key: k(b+1) + 1 = kb + k + 1. And k(b+1) = kb + k.
 *
 * For k = 0: n = 0, n+1 = 1. chi_bar(0) = 0 (not coprime).
 *            Contribution: chi_bar(1) - 0 = 1.
 *
 * For k = b-1: n = (b-1)(b+1) = b^2 - 1 = m-1.
 *              n+1 = m = 0 mod m. chi_bar(m) = 0.
 *              Contribution: 0 - chi_bar(m-1) = -chi_bar(-1).
 *              For odd chi: chi(-1) = -1, so chi_bar(-1) = -1.
 *              Contribution: -(-1) = +1.
 *
 * So endpoints contribute 1 + 1 = 2 for odd characters.
 *
 * Interior terms (1 <= k <= b-2):
 *   chi_bar(k(b+1)+1) - chi_bar(k(b+1))
 *
 * Let's compute these and look for structure.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    int bases[] = {5, 7, 11, 13};
    int nb = 4;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
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

        int dlog[m];
        memset(dlog, -1, sizeof(int) * m);
        { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * g % m); } }

        printf("=== Base %d, m=%d, step=%d ===\n", b, m, b+1);
        printf("Good slices: ");
        for (int k = 0; k < b; k++) printf("%d ", k*(b+1));
        printf("\n");

        /* Check: which n and n+1 are coprime to m? */
        printf("\nSlice structure:\n");
        printf("%4s %6s %6s %4s %4s %6s\n",
               "k", "n", "n+1", "gcd_n", "gcd_1", "type");

        for (int k = 0; k < b; k++) {
            int n = k * (b + 1);
            int n1 = n + 1;
            int g_n = (n == 0) ? m : gcd(n, m);
            int g_n1 = (n1 >= m) ? m : gcd(n1, m);
            char *type;
            if (g_n != 1 && g_n1 != 1) type = "both bad";
            else if (g_n != 1) type = "n bad";
            else if (g_n1 != 1) type = "n+1 bad";
            else type = "both ok";
            printf("%4d %6d %6d %4d %4d %10s\n",
                   k, n % m, n1 % m, g_n, g_n1, type);
        }

        /* For a few odd characters, compute S_G term by term */
        int dl_m1 = dlog[m - 1];
        int odd_j[500], n_odd = 0;
        for (int j = 0; j < n_units && n_odd < 500; j++) {
            long long test = 2LL * j * dl_m1;
            if ((int)(test % (2 * n_units)) != n_units) continue;
            odd_j[n_odd++] = j;
        }

        /* Take the first odd character and decompose S_G */
        if (n_odd > 0) {
            int j = odd_j[0]; /* first odd character */
            printf("\nS_G decomposition for first odd character (j=%d):\n", j);
            printf("%4s %6s %6s %10s %10s %10s %10s\n",
                   "k", "n", "n+1", "Re(cb_n1)", "Re(cb_n)",
                   "Re(diff)", "Im(diff)");

            double total_re = 0, total_im = 0;
            for (int k = 0; k < b; k++) {
                int n = k * (b + 1);
                int n1 = (n + 1) % m;

                double re_n1 = 0, im_n1 = 0;
                double re_n = 0, im_n = 0;

                if (n1 < m && gcd(n1, m) == 1 && dlog[n1] >= 0) {
                    double angle = -2 * M_PI * j * dlog[n1] / (double)n_units;
                    re_n1 = cos(angle);
                    im_n1 = sin(angle);
                }

                int n_mod = n % m;
                if (n_mod > 0 && gcd(n_mod, m) == 1 && dlog[n_mod] >= 0) {
                    double angle = -2 * M_PI * j * dlog[n_mod] / (double)n_units;
                    re_n = cos(angle);
                    im_n = sin(angle);
                }

                double d_re = re_n1 - re_n;
                double d_im = im_n1 - im_n;
                total_re += d_re;
                total_im += d_im;

                printf("%4d %6d %6d %+10.4f %+10.4f %+10.4f %+10.4f\n",
                       k, n_mod, n1, re_n1, re_n, d_re, d_im);
            }
            printf("Total: Re=%+.4f Im=%+.4f |S_G|=%.4f\n",
                   total_re, total_im,
                   sqrt(total_re*total_re + total_im*total_im));
        }

        /* Key observation: for b prime, gcd(k(b+1), b^2) = gcd(k(b+1), b^2).
         * Since b+1 is coprime to b (gcd(b+1,b)=1), gcd(k(b+1), b^2) = gcd(k, b^2).
         * So gcd(n, m) = gcd(k, b^2). For k in {0,...,b-1}:
         *   k=0: gcd = b^2 (n=0, bad)
         *   k=b: doesn't exist (k < b)
         *   k coprime to b: gcd = 1 (n is a unit)
         *   k divisible by b: only k=0 in range, already handled
         * So for k = 1,...,b-1 with b prime: all n = k(b+1) are units.
         * And n+1 = k(b+1)+1: is this coprime to b^2?
         *   gcd(k(b+1)+1, b) = gcd(kb+k+1, b) = gcd(k+1, b).
         *   So n+1 is NOT coprime to b^2 when k+1 = b, i.e., k = b-1.
         *   At k = b-1: n+1 = (b-1)(b+1)+1 = b^2 = m. Already handled.
         */

        printf("\nFor b prime: interior slices (k=1..%d) all have\n", b-2);
        printf("both n and n+1 coprime to m.\n");
        printf("Endpoints: k=0 has n=0 (bad), k=%d has n+1=m (bad).\n\n", b-1);
    }

    return 0;
}
