/*
 * base5_proof.c - Prove |partial_sum| = c * |L(1,chi)| at base 5.
 *
 * For primitive chi mod 25:
 * partial_sum = chi_bar(1) + chi_bar(2) + chi_bar(3) + chi_bar(4)
 *
 * chi mod 25 has order dividing phi(25) = 20.
 * The subgroup of units mod 5 in (Z/25Z)* consists of
 * {1, 6, 11, 16, 21} (units a with a = 1 mod 5).
 *
 * Generator mod 25: g = 2 (order 20).
 * 2^1=2, 2^2=4, 2^3=8, 2^4=16, 2^5=7, 2^6=14, 2^7=3, 2^8=6,
 * 2^9=12, 2^10=24, 2^11=23, 2^12=21, 2^13=17, 2^14=9, 2^15=18,
 * 2^16=11, 2^17=22, 2^18=19, 2^19=13, 2^20=1.
 *
 * dlog(1)=0, dlog(2)=1, dlog(3)=7, dlog(4)=2.
 *
 * For chi_j: chi_j(a) = e^{2*pi*i * j * dlog(a) / 20}
 *
 * partial_sum(j) = e^0 + e^{2*pi*i*j/20} + e^{2*pi*i*7j/20} + e^{2*pi*i*2j/20}
 *                = 1 + w^j + w^{7j} + w^{2j}
 * where w = e^{2*pi*i/20} = e^{pi*i/10}.
 *
 * For the conjugate: chi_bar uses -j, so
 * partial_sum_bar(j) = 1 + w^{-j} + w^{-7j} + w^{-2j}
 *
 * Now, L(1, chi) for primitive chi mod 25:
 * L(1,chi) = -(tau(chi) / 25) * B_{1,chi_bar}
 *          = -(tau(chi) / 25) * (1/25) sum_{a=1}^{24} a chi_bar(a)
 *
 * Actually, the class number formula for odd primitive chi mod m:
 * L(1, chi) = -pi * i * B_{1,chi} / tau(chi)  ... or variants.
 *
 * Let me just compute everything numerically and find the exact relationship.
 */

#include <stdio.h>
#include <math.h>

int main(void) {
    int m = 25;
    double PI = acos(-1.0);
    /* Generator g=2, order 20 */
    int dlog[25] = {-1, 0, 1, 7, 2, -1, 8, 5, 3, 14,
                    -1, 16, 9, 19, 6, -1, 4, 13, 15, 18,
                    -1, 12, 17, 11, 10};

    printf("Odd characters mod 25 (chi(-1) = -1, dlog(24)=10, need j*10 = 10 mod 20)\n");
    printf("So j must be odd: j = 1,3,5,7,9,11,13,15,17,19\n\n");

    int odd_j[] = {1, 3, 5, 7, 9, 11, 13, 15, 17, 19};
    int n_odd = 10;

    printf("%4s %12s %12s %12s %12s %12s\n",
           "j", "|ps|", "|L(1)|", "|ps|/|L|", "|B1|", "|tau|");

    for (int ci = 0; ci < n_odd; ci++) {
        int j = odd_j[ci];

        /* Partial sum: chi_bar(1)+chi_bar(2)+chi_bar(3)+chi_bar(4) */
        /* chi_bar_j(a) = exp(-2*pi*i * j * dlog(a) / 20) */
        double ps_re = 0, ps_im = 0;
        for (int k = 1; k <= 4; k++) {
            double angle = -2*PI*j*dlog[k]/20.0;
            ps_re += cos(angle);
            ps_im += sin(angle);
        }
        double ps_mag = sqrt(ps_re*ps_re + ps_im*ps_im);

        /* Gauss sum tau(chi_j) = sum_{a coprime to 25} chi_j(a) e^{2*pi*i*a/25} */
        double tau_re = 0, tau_im = 0;
        for (int a = 1; a < 25; a++) {
            if (dlog[a] < 0) continue;
            double angle_chi = 2*PI*j*dlog[a]/20.0;
            double angle_add = 2*PI*a/25.0;
            tau_re += cos(angle_chi + angle_add);
            tau_im += sin(angle_chi + angle_add);
        }
        double tau_mag = sqrt(tau_re*tau_re + tau_im*tau_im);

        /* B_{1,chi} = (1/m) sum_{a=1}^{m-1} a * chi(a) */
        double B1_re = 0, B1_im = 0;
        for (int a = 1; a < 25; a++) {
            if (dlog[a] < 0) continue;
            double angle = 2*PI*j*dlog[a]/20.0;
            B1_re += a * cos(angle) / 25.0;
            B1_im += a * sin(angle) / 25.0;
        }
        double B1_mag = sqrt(B1_re*B1_re + B1_im*B1_im);

        /* L(1, chi) = -pi * i * B_{1,chi} / tau(chi) for odd primitive chi */
        /* |L(1)| = pi * |B1| / |tau| = pi * |B1| / 5 */
        double L1_formula = PI * B1_mag / tau_mag;

        /* Also compute L(1) via Euler product for verification */
        double logL_re = 0, logL_im = 0;
        for (int p = 2; p < 1000000; p++) {
            /* Simple primality */
            int is_p = 1;
            if (p < 2) is_p = 0;
            else if (p == 2 || p == 3) is_p = 1;
            else if (p%2==0 || p%3==0) is_p = 0;
            else for (int i=5; i*i<=p; i+=6)
                if (p%i==0 || p%(i+2)==0) { is_p=0; break; }
            if (!is_p || p == 5) continue;

            int dl = dlog[p % 25];
            if (dl < 0) continue;
            double angle = 2*PI*j*dl/20.0;
            double chi_re = cos(angle)/p, chi_im = sin(angle)/p;
            double w_re = 1-chi_re, w_im = -chi_im;
            double mag2 = w_re*w_re + w_im*w_im;
            logL_re -= 0.5*log(mag2);
            logL_im -= atan2(w_im, w_re);
        }
        double L1_euler = exp(logL_re);

        double ratio = (L1_euler > 0.01) ? ps_mag / L1_euler : 0;

        printf("%4d %12.6f %12.6f %12.6f %12.6f %12.6f",
               j, ps_mag, L1_euler, ratio, B1_mag, tau_mag);

        /* Check: does |ps| = (some function of B1, tau)? */
        /* From data: |ps|/|L| = 1.7794 for all primitive chars */
        /* |L| = pi * |B1| / 5 */
        /* So |ps| = 1.7794 * pi * |B1| / 5 */
        /* = 1.7794 * pi / 5 * |B1| */
        /* = 1.1187 * |B1| */
        double ps_over_B1 = (B1_mag > 0.01) ? ps_mag / B1_mag : 0;
        printf(" %8.4f\n", ps_over_B1);
    }

    printf("\npi/5 = %.6f\n", PI/5);
    printf("If |ps|/|L| = c, then |ps| = c * pi * |B1| / 5\n");
    printf("So |ps|/|B1| = c * pi / 5\n");

    /* The partial sum {1,2,3,4} and the Bernoulli number B1
     * are both sums over the same group elements but with
     * different weights (1 vs a/m). The ratio should be
     * expressible in terms of the mean of {1,2,3,4} = 2.5
     * and the Bernoulli weighting. */

    printf("\nMean of {1,2,3,4} = 2.5 = m/10 = 25/10\n");
    printf("Partial sum uses weight 1. B1 uses weight a/m.\n");
    printf("If chi varies slowly over {1,2,3,4}, then\n");
    printf("ps ~ 4 * chi_bar(2.5) and B1 ~ 4 * (2.5/25) * chi_bar(2.5)\n");
    printf("So ps/B1 ~ 1/(2.5/25) = 10. But actual ratio is ~1.12.\n");
    printf("The chi variation over {1,2,3,4} matters.\n");

    return 0;
}
