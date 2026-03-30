/*
 * composite_large.c - Tensor structure at n = p*q with larger primes.
 *
 * Use p=13, q=17, n=221 in base 10. Both > b+1 = 11.
 * phi(221) = 12*16 = 192.
 *
 * Compute collision transform over (Z/nZ)* using CRT:
 * chi = chi_p x chi_q where chi_p mod 13, chi_q mod 17.
 *
 * Generator mod 13: g=2, order 12.
 * Generator mod 17: g=3, order 16.
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
    int p = 13, q = 17;
    int n = p * q;  /* 221 */
    int phi_p = p - 1, phi_q = q - 1;
    int phi_n = phi_p * phi_q;  /* 192 */

    printf("n = %d = %d x %d, phi = %d\n", n, p, q, phi_n);
    printf("phi_p = %d, phi_q = %d\n\n", phi_p, phi_q);

    /* Generators */
    int g_p = 2, g_q = 3;

    /* Verify generators */
    { int v=1,o=0; do{v=v*g_p%p;o++;}while(v!=1);
      printf("g_p=%d has order %d mod %d: %s\n", g_p, o, p, o==phi_p?"OK":"BAD"); }
    { int v=1,o=0; do{v=v*g_q%q;o++;}while(v!=1);
      printf("g_q=%d has order %d mod %d: %s\n\n", g_q, o, q, o==phi_q?"OK":"BAD"); }

    /* Discrete logs mod p and mod q */
    int dlog_p[p], dlog_q[q];
    memset(dlog_p, -1, sizeof(dlog_p));
    memset(dlog_q, -1, sizeof(dlog_q));
    { int v=1; for(int k=0;k<phi_p;k++){dlog_p[v]=k;v=v*g_p%p;} }
    { int v=1; for(int k=0;k<phi_q;k++){dlog_q[v]=k;v=v*g_q%q;} }

    /* Compute C(g) for composite n */
    int C_n[n];
    memset(C_n, 0, sizeof(C_n));
    int Q_n = (n - 1) / b;

    for (int g = 1; g < n; g++) {
        if (gcd(g, n) != 1) continue;
        int count = 0;
        for (int r = 1; r < n; r++) {
            int d1 = b * r / n;
            int gr = (int)((long long)g * r % n);
            int d2 = b * gr / n;
            if (d1 == d2) count++;
        }
        C_n[g] = count;
    }

    /* Compute C(g) for each prime */
    int C_p[p], C_q[q];
    int Q_p = (p-1)/b, Q_q = (q-1)/b;

    for (int g = 1; g < p; g++) {
        int count = 0;
        for (int r = 1; r < p; r++) {
            int d1 = b*r/p;
            int gr = g*r%p;
            int d2 = b*gr/p;
            if (d1==d2) count++;
        }
        C_p[g] = count;
    }

    for (int g = 1; g < q; g++) {
        int count = 0;
        for (int r = 1; r < q; r++) {
            int d1 = b*r/q;
            int gr = g*r%q;
            int d2 = b*gr/q;
            if (d1==d2) count++;
        }
        C_q[g] = count;
    }

    /* Collision transforms at individual primes */
    double sh_p_re[12], sh_p_im[12], sh_p_mag[12];
    for (int j = 0; j < phi_p; j++) {
        double re=0,im=0;
        for (int g=1;g<p;g++) {
            double angle = -2*M_PI*j*dlog_p[g]/(double)phi_p;
            int S = C_p[g] - Q_p;
            re += S*cos(angle); im += S*sin(angle);
        }
        sh_p_re[j]=re/phi_p; sh_p_im[j]=im/phi_p;
        sh_p_mag[j]=sqrt(re*re+im*im)/phi_p;
    }

    double sh_q_re[16], sh_q_im[16], sh_q_mag[16];
    for (int j = 0; j < phi_q; j++) {
        double re=0,im=0;
        for (int g=1;g<q;g++) {
            double angle = -2*M_PI*j*dlog_q[g]/(double)phi_q;
            int S = C_q[g] - Q_q;
            re += S*cos(angle); im += S*sin(angle);
        }
        sh_q_re[j]=re/phi_q; sh_q_im[j]=im/phi_q;
        sh_q_mag[j]=sqrt(re*re+im*im)/phi_q;
    }

    printf("Collision transform at p=%d:\n", p);
    for (int j=0;j<phi_p;j++)
        printf("  j=%2d: |sh| = %.4f\n", j, sh_p_mag[j]);

    printf("\nCollision transform at q=%d:\n", q);
    for (int j=0;j<phi_q;j++)
        printf("  j=%2d: |sh| = %.4f\n", j, sh_q_mag[j]);

    /* Collision transform at composite via CRT */
    printf("\nComposite transform (j_p, j_q) -> |sh_n| vs |sh_p|*|sh_q|:\n");
    printf("%4s %4s %8s %8s %8s %8s\n",
           "j_p", "j_q", "|sh_n|", "|sh_p|", "|sh_q|", "ratio");

    int n_close = 0, n_far = 0;
    double sum_ratio = 0;
    int ratio_cnt = 0;

    for (int jp = 0; jp < phi_p; jp++) {
        for (int jq = 0; jq < phi_q; jq++) {
            double re=0, im=0;

            for (int g = 1; g < n; g++) {
                if (gcd(g, n) != 1) continue;
                int gp = g % p, gq = g % q;
                if (dlog_p[gp] < 0 || dlog_q[gq] < 0) continue;

                double angle = -2*M_PI*(jp*dlog_p[gp]/(double)phi_p
                                      + jq*dlog_q[gq]/(double)phi_q);
                int S = C_n[g] - Q_n;
                re += S*cos(angle); im += S*sin(angle);
            }
            re /= phi_n; im /= phi_n;

            double sh_n_mag = sqrt(re*re + im*im);
            double product = sh_p_mag[jp] * sh_q_mag[jq];
            double ratio = (product > 1e-6) ? sh_n_mag / product : -1;

            if (ratio > 0) {
                sum_ratio += ratio;
                ratio_cnt++;
                if (fabs(ratio - 1.0) < 0.1) n_close++;
                else n_far++;
            }

            /* Print selected rows */
            if ((jp < 3 && jq < 3) || (sh_n_mag > 0.5) ||
                (ratio > 0 && fabs(ratio-1) < 0.05)) {
                printf("%4d %4d %8.4f %8.4f %8.4f %8.4f\n",
                       jp, jq, sh_n_mag, sh_p_mag[jp], sh_q_mag[jq],
                       ratio);
            }
        }
    }

    printf("\n...\n");
    printf("Tensor test: %d/%d ratios near 1.0 (within 10%%)\n",
           n_close, n_close + n_far);
    printf("Mean ratio: %.4f\n", ratio_cnt > 0 ? sum_ratio/ratio_cnt : 0);

    /* Check: is the ratio CONSTANT? */
    if (ratio_cnt > 0) {
        double mean = sum_ratio / ratio_cnt;
        double var = 0;
        /* Recompute variance */
        for (int jp=0;jp<phi_p;jp++) {
            for (int jq=0;jq<phi_q;jq++) {
                double re=0,im=0;
                for (int g=1;g<n;g++) {
                    if(gcd(g,n)!=1)continue;
                    int gp=g%p,gq=g%q;
                    if(dlog_p[gp]<0||dlog_q[gq]<0)continue;
                    double angle=-2*M_PI*(jp*dlog_p[gp]/(double)phi_p+jq*dlog_q[gq]/(double)phi_q);
                    int S=C_n[g]-Q_n;
                    re+=S*cos(angle);im+=S*sin(angle);
                }
                re/=phi_n; im/=phi_n;
                double sh_n=sqrt(re*re+im*im);
                double prod=sh_p_mag[jp]*sh_q_mag[jq];
                if(prod>1e-6){
                    double r=sh_n/prod;
                    var+=(r-mean)*(r-mean);
                }
            }
        }
        var /= ratio_cnt;
        printf("CV of ratio: %.4f\n", sqrt(var)/mean);
    }

    return 0;
}
