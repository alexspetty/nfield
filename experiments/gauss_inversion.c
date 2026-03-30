/*
 * gauss_inversion.c - Evaluate the geometric sum exactly.
 *
 * S(t) = sum_{a=1}^{b-1} e^{2*pi*i*t*a/b^2}
 *
 * This is a geometric series:
 * S(t) = e^{2*pi*i*t/b^2} * (e^{2*pi*i*t*(b-1)/b^2} - 1) / (e^{2*pi*i*t/b^2} - 1)
 *      = (e^{2*pi*i*t*b/b^2} - e^{2*pi*i*t/b^2}) / (e^{2*pi*i*t/b^2} - 1)
 *      = (e^{2*pi*i*t/b} - e^{2*pi*i*t/b^2}) / (e^{2*pi*i*t/b^2} - 1)
 *
 * Key cases:
 * - t = 0 mod b: S(t) depends on t/b mod b
 * - t != 0 mod b: generic
 *
 * For the partial sum P = sum chi_bar(k), k=1..b-1:
 * P = (1/tau(chi)) * sum_t chi(t) S(t)
 *   = (1/tau(chi)) * sum_t chi(t) S(t)
 *
 * (Note: using chi not chi_bar for inversion:
 *  sum chi_bar(a) = (1/tau(chi)) sum chi(t) sum e^{2pi i ta/m})
 *
 * Wait, the exact formula:
 * chi_bar(a) = (1/tau(chi)) sum_{t} chi(t) e^{2*pi*i*t*a/m}  (DFT inversion)
 *
 * So sum_{a=1}^{b-1} chi_bar(a) = (1/tau(chi)) sum_t chi(t) S(t)
 *
 * And B_{1,chi_bar} = (1/m) sum_a a chi_bar(a)
 *                   = (1/(m*tau(chi))) sum_t chi(t) T(t)
 * where T(t) = sum_{a=1, gcd(a,m)=1}^{m-1} a e^{2*pi*i*t*a/m}
 *
 * Actually, let me be more careful. The sums should be over
 * a coprime to m for character sums, but the DFT is over all a.
 *
 * For PRIMITIVE chi mod m, the DFT inversion is:
 * chi(a) = (1/tau(chi_bar)) sum_{t=1}^{m} chi_bar(t) e^{2*pi*i*ta/m}
 *
 * So chi_bar(a) = (1/tau(chi)) sum_t chi(t) e^{-2*pi*i*ta/m}
 *              = (1/tau(chi)) sum_t chi(t) e^{2*pi*i*t*(m-a)/m}
 *
 * Hmm, let me just compute numerically for base 5 and verify the formula.
 *
 * Then: P = sum_{k=1}^{b-1} chi_bar(k)
 *        = (1/tau(chi)) sum_t chi(t) sum_{k=1}^{b-1} e^{-2*pi*i*tk/m}
 *        = (1/tau(chi)) sum_t chi(t) S'(t)
 *
 * where S'(t) = sum_{k=1}^{b-1} e^{-2*pi*i*tk/b^2}
 *             = conj(S(t))  (complex conjugate of S with +sign)
 *
 * And B1 = (1/m) sum_{a coprime} a chi_bar(a)
 *        = (1/(m*tau(chi))) sum_t chi(t) T'(t)
 * where T'(t) = sum_{a coprime} a e^{-2*pi*i*ta/m}
 *
 * So P/B1 = [sum chi(t) S'(t)] / [(1/m) sum chi(t) T'(t)]
 *         = m * [sum chi(t) S'(t)] / [sum chi(t) T'(t)]
 *
 * Both sums are over t coprime to m (since chi(t) = 0 otherwise).
 * The question: is sum chi(t) S'(t) proportional to sum chi(t) T'(t)?
 *
 * For S'(t): sum of e^{-2*pi*i*tk/b^2} for k=1..b-1.
 * For T'(t): sum of a * e^{-2*pi*i*ta/b^2} for a coprime to b^2, a=1..b^2-1.
 *
 * These are VERY different sums (4 terms vs 20 terms for b=5).
 * Their ratio depends on t, so the weighted sums are not simply proportional.
 *
 * BUT: at base 5, |P|/|B1| = sqrt(5)/2 for ALL primitive characters.
 * This means sum chi(t) S'(t) / sum chi(t) T'(t) = sqrt(5)/(2*25)
 * for every primitive chi. That's a strong constraint.
 *
 * Let me just compute S'(t) and T'(t) for each t coprime to 25
 * and see if there's a pattern.
 */

#include <stdio.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    int b = 5, m = 25;
    double PI = acos(-1.0);

    printf("S'(t) and T'(t) for t coprime to %d:\n\n", m);
    printf("%4s %12s %12s %12s %12s %12s\n",
           "t", "Re(S')", "Im(S')", "Re(T')", "Im(T')", "|S'|/|T'|*m");

    for (int t = 1; t < m; t++) {
        if (gcd(t, m) != 1) continue;

        /* S'(t) = sum_{k=1}^{b-1} e^{-2*pi*i*t*k/m} */
        double Sp_re = 0, Sp_im = 0;
        for (int k = 1; k <= b-1; k++) {
            double angle = -2*PI*t*k/(double)m;
            Sp_re += cos(angle);
            Sp_im += sin(angle);
        }

        /* T'(t) = sum_{a coprime, a=1..m-1} a * e^{-2*pi*i*t*a/m} */
        double Tp_re = 0, Tp_im = 0;
        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1) continue;
            double angle = -2*PI*t*a/(double)m;
            Tp_re += a * cos(angle);
            Tp_im += a * sin(angle);
        }

        double Sp_mag = sqrt(Sp_re*Sp_re + Sp_im*Sp_im);
        double Tp_mag = sqrt(Tp_re*Tp_re + Tp_im*Tp_im);
        double ratio = (Tp_mag > 0.01) ? m * Sp_mag / Tp_mag : 0;

        printf("%4d %+12.6f %+12.6f %+12.6f %+12.6f %12.6f\n",
               t, Sp_re, Sp_im, Tp_re, Tp_im, ratio);
    }

    /* Check: is S'(t) = c(t) * T'(t) / m for some c(t)?
     * If c(t) is the same for all t, then P/B1 = c regardless of chi.
     * If c(t) varies, but the variation is "orthogonal" to every primitive chi,
     * the ratio could still be constant.
     */

    printf("\nComplex ratio S'(t)*m / T'(t):\n");
    for (int t = 1; t < m; t++) {
        if (gcd(t, m) != 1) continue;

        double Sp_re = 0, Sp_im = 0;
        for (int k = 1; k <= b-1; k++) {
            double angle = -2*PI*t*k/(double)m;
            Sp_re += cos(angle); Sp_im += sin(angle);
        }

        double Tp_re = 0, Tp_im = 0;
        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1) continue;
            double angle = -2*PI*t*a/(double)m;
            Tp_re += a * cos(angle); Tp_im += a * sin(angle);
        }

        /* S'*m / T' */
        double Tp_mag2 = Tp_re*Tp_re + Tp_im*Tp_im;
        double r_re = 0, r_im = 0;
        if (Tp_mag2 > 0.01) {
            r_re = m * (Sp_re*Tp_re + Sp_im*Tp_im) / Tp_mag2;
            r_im = m * (Sp_im*Tp_re - Sp_re*Tp_im) / Tp_mag2;
        }
        printf("  t=%2d: ratio = (%+8.4f, %+8.4f), |ratio| = %8.4f\n",
               t, r_re, r_im, sqrt(r_re*r_re + r_im*r_im));
    }

    printf("\nsqrt(5)/2 = %.6f\n", sqrt(5.0)/2);

    return 0;
}
