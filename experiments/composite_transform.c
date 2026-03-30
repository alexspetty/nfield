/*
 * composite_transform.c - Full collision transform at n = pq.
 *
 * For n = p*q, compute:
 * 1. S(a) for all a coprime to n, via direct collision count
 *    (using a as a "fake prime" with floor(b*r/a) digit function)
 * 2. The collision transform: s_hat(chi) for each character mod n
 * 3. CRT decomposition: chi = chi_p x chi_q
 * 4. Check: does |s_hat(chi_p x chi_q)| factor as f(chi_p) * g(chi_q)?
 *
 * Actually, the finite determination says S depends on n mod b^2.
 * For n = pq, n mod b^2 is fixed. We want S(a) where a = n' mod b^2
 * for different "primes" n' that happen to equal different composites.
 *
 * But wait: the collision transform is over (Z/b^2 Z)*, not (Z/nZ)*.
 * For the COMPOSITE question, we want to work mod n, not mod b^2.
 *
 * Different approach: compute the digit function floor(b*r/n) for
 * the composite n directly, and compute the collision count C(g)
 * for each g in (Z/nZ)*. Then Fourier-transform C over (Z/nZ)*.
 *
 * Characters of (Z/77Z)* = (Z/7Z)* x (Z/11Z)*:
 * phi(77) = 6 * 10 = 60.
 * Characters labeled by (j7, j11) where j7 in {0,...,5}, j11 in {0,...,9}.
 */

#include <stdio.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    int b = 10;
    int p = 7, q = 11;
    int n = p * q;  /* 77 */
    int phi_n = (p-1) * (q-1);  /* 60 */

    printf("n = %d = %d x %d, phi = %d\n\n", n, p, q, phi_n);

    /* Compute C(g) for each g in (Z/nZ)* */
    /* C(g) = #{r in 1..n-1 : floor(br/n) = floor(b*(gr mod n)/n)} */
    int C[n];
    memset(C, 0, sizeof(C));
    int Q = (n - 1) / b;

    for (int g = 1; g < n; g++) {
        if (gcd(g, n) != 1) continue;
        int count = 0;
        for (int r = 1; r < n; r++) {
            int d1 = b * r / n;
            int gr = (int)((long long)g * r % n);
            int d2 = b * gr / n;
            if (d1 == d2) count++;
        }
        C[g] = count;
    }

    /* Collision deviation S(g) = C(g) - Q */
    /* Grand mean check */
    double sum_S = 0;
    int cnt = 0;
    for (int g = 1; g < n; g++) {
        if (gcd(g, n) != 1) continue;
        sum_S += C[g] - Q;
        cnt++;
    }
    printf("Grand mean of S: %.4f (should be -1/2 = -0.5)\n", sum_S / cnt);

    /* CRT: for each unit g mod 77, find g mod 7 and g mod 11 */
    /* Generator mod 7: g7 = 3 (order 6) */
    /* Generator mod 11: g11 = 2 (order 10) */

    /* Discrete logs */
    int dlog7[7], dlog11[11];
    memset(dlog7, -1, sizeof(dlog7));
    memset(dlog11, -1, sizeof(dlog11));

    { int v = 1; for (int k = 0; k < 6; k++) { dlog7[v] = k; v = v * 3 % 7; } }
    { int v = 1; for (int k = 0; k < 10; k++) { dlog11[v] = k; v = v * 2 % 11; } }

    /* Verify */
    printf("Generators: g7=3 (mod 7), g11=2 (mod 11)\n");

    /* For each character (j7, j11), compute
     * s_hat = (1/phi) sum_{g coprime} S(g) * chi_bar(g)
     * where chi(g) = exp(2pi i j7 dlog7(g%7) / 6) * exp(2pi i j11 dlog11(g%11) / 10)
     */

    double PI = acos(-1.0);

    /* Also compute s_hat at each prime individually */
    /* For prime p=7: S_p(g) for g mod 7 */
    int S_p[7];
    for (int g = 1; g < 7; g++) {
        int count = 0;
        for (int r = 1; r < 7; r++) {
            int d1 = b * r / 7;
            int gr = g * r % 7;
            int d2 = b * gr / 7;
            if (d1 == d2) count++;
        }
        S_p[g] = count - (7-1)/b;
    }

    /* For prime q=11 */
    int S_q[11];
    for (int g = 1; g < 11; g++) {
        int count = 0;
        for (int r = 1; r < 11; r++) {
            int d1 = b * r / 11;
            int gr = g * r % 11;
            int d2 = b * gr / 11;
            if (d1 == d2) count++;
        }
        S_q[g] = count - (11-1)/b;
    }

    /* s_hat for each prime */
    printf("\nCollision transform at p=%d:\n", p);
    double sh_p_re[6], sh_p_im[6];
    for (int j = 0; j < 6; j++) {
        double re = 0, im = 0;
        for (int g = 1; g < 7; g++) {
            double angle = -2*PI*j*dlog7[g]/6.0;
            re += S_p[g] * cos(angle);
            im += S_p[g] * sin(angle);
        }
        sh_p_re[j] = re / 6;
        sh_p_im[j] = im / 6;
        printf("  j7=%d: s_hat = (%+.4f, %+.4f), |s_hat| = %.4f\n",
               j, sh_p_re[j], sh_p_im[j],
               sqrt(re*re+im*im)/6);
    }

    printf("\nCollision transform at q=%d:\n", q);
    double sh_q_re[10], sh_q_im[10];
    for (int j = 0; j < 10; j++) {
        double re = 0, im = 0;
        for (int g = 1; g < 11; g++) {
            double angle = -2*PI*j*dlog11[g]/10.0;
            re += S_q[g] * cos(angle);
            im += S_q[g] * sin(angle);
        }
        sh_q_re[j] = re / 10;
        sh_q_im[j] = im / 10;
        printf("  j11=%d: s_hat = (%+.4f, %+.4f), |s_hat| = %.4f\n",
               j, sh_q_re[j], sh_q_im[j],
               sqrt(re*re+im*im)/10);
    }

    /* Collision transform at composite n=77 */
    printf("\nCollision transform at n=%d (CRT decomposition):\n", n);
    printf("%4s %4s %10s %10s %10s %10s %8s\n",
           "j7", "j11", "|sh_n|", "|sh_p|", "|sh_q|",
           "|sh_p*sh_q|", "ratio");

    for (int j7 = 0; j7 < 6; j7++) {
        for (int j11 = 0; j11 < 10; j11++) {
            double re = 0, im = 0;

            for (int g = 1; g < n; g++) {
                if (gcd(g, n) != 1) continue;
                int g7 = g % 7, g11 = g % 11;
                if (dlog7[g7] < 0 || dlog11[g11] < 0) continue;

                double angle = -2*PI*(j7*dlog7[g7]/6.0 + j11*dlog11[g11]/10.0);
                int S_g = C[g] - Q;
                re += S_g * cos(angle);
                im += S_g * sin(angle);
            }
            re /= phi_n;
            im /= phi_n;

            double sh_n_mag = sqrt(re*re + im*im);
            double sh_p_mag = sqrt(sh_p_re[j7]*sh_p_re[j7] + sh_p_im[j7]*sh_p_im[j7]);
            double sh_q_mag = sqrt(sh_q_re[j11]*sh_q_re[j11] + sh_q_im[j11]*sh_q_im[j11]);
            double product = sh_p_mag * sh_q_mag;
            double ratio = (product > 1e-8) ? sh_n_mag / product : 0;

            /* Only print non-trivial ones */
            if (sh_n_mag > 0.01 || product > 0.01) {
                printf("%4d %4d %10.4f %10.4f %10.4f %10.4f %8.4f\n",
                       j7, j11, sh_n_mag, sh_p_mag, sh_q_mag,
                       product, ratio);
            }
        }
    }

    return 0;
}
