/*
 * shat_over_L.c - Compute s_hat(chi) / L(1, chi) for each odd character.
 *
 * If this ratio has a closed form (involving Gauss sums, the
 * partial sum, or other computable quantities), we have the theorem.
 *
 * Compute both the complex ratio (not just magnitudes) to see
 * if the phase relationship is also clean.
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
    int b = 5;
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

    int dlog[m];
    memset(dlog, -1, sizeof(int)*m);
    { int v=1; for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);} }

    /* Build S, center */
    int S[m], has_S[m];
    memset(has_S, 0, sizeof(int)*m);
    for (int p = m+1; p < 80000; p++) {
        if (!is_prime(p) || gcd(p,b) != 1) continue;
        int a = p % m;
        if (has_S[a]) continue;
        int C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)b*r/p);
            long long br = (long long)b*r%p;
            int d2 = (int)((long long)b*br/p);
            if (d1==d2) C++;
        }
        S[a] = C - (p-1)/b; has_S[a] = 1;
    }

    double cls_sum[b]; int cls_cnt[b];
    memset(cls_sum,0,sizeof(double)*b);
    memset(cls_cnt,0,sizeof(int)*b);
    for (int i=0;i<n_units;i++) {
        int a=units[i]; if(!has_S[a])continue;
        cls_sum[(a-1)%b]+=S[a]; cls_cnt[(a-1)%b]++;
    }
    double mean_R[b];
    for (int R=0;R<b;R++)
        mean_R[R]=cls_cnt[R]>0?cls_sum[R]/cls_cnt[R]:0;

    int dl_m1 = dlog[m-1];
    int odd_j[100], n_odd = 0;
    for (int j=0;j<n_units&&n_odd<100;j++) {
        long long t=2LL*j*dl_m1;
        if ((int)(t%(2*n_units))!=n_units) continue;
        odd_j[n_odd++]=j;
    }

    printf("Base %d, m=%d, phi=%d, %d odd chars, gen=%d\n\n",
           b, m, n_units, n_odd, g);

    /* Compute s_hat(chi) as complex number */
    /* Compute L(1, chi) as complex number via Euler product */
    /* Compute their ratio */

    printf("%4s %16s %16s %16s %10s\n",
           "c", "s_hat", "L(1,chi)", "s_hat/L(1)", "|ratio|");

    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];

        /* s_hat(chi) */
        double sh_re=0, sh_im=0;
        for (int i=0;i<n_units;i++) {
            int a=units[i]; if(!has_S[a])continue;
            double sc=S[a]-mean_R[(a-1)%b];
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            sh_re+=sc*cos(angle); sh_im+=sc*sin(angle);
        }
        sh_re/=n_units; sh_im/=n_units;

        /* L(1, chi) via Euler product: L = prod (1 - chi(p)/p)^{-1}
         * Compute as complex number.
         * log L = -sum_p log(1 - chi(p)/p)
         */
        double logL_re=0, logL_im=0;
        for (int p=2;p<MAX_PRIME;p++) {
            if (!is_prime(p)||p==b) continue;
            int dl=dlog[p%m]; if(dl<0) continue;
            double angle=2*M_PI*j*dl/(double)n_units;
            double chi_re=cos(angle)/p, chi_im=sin(angle)/p;
            /* 1 - chi(p)/p */
            double w_re=1-chi_re, w_im=-chi_im;
            /* -log(w) = -(log|w| + i*arg(w)) */
            double mag2=w_re*w_re+w_im*w_im;
            logL_re -= 0.5*log(mag2);
            logL_im -= atan2(w_im, w_re);
        }
        double L_re=exp(logL_re)*cos(logL_im);
        double L_im=exp(logL_re)*sin(logL_im);

        /* s_hat / L(1) */
        double Lmag2=L_re*L_re+L_im*L_im;
        double ratio_re, ratio_im;
        if (Lmag2 > 1e-20) {
            ratio_re = (sh_re*L_re+sh_im*L_im)/Lmag2;
            ratio_im = (sh_im*L_re-sh_re*L_im)/Lmag2;
        } else {
            ratio_re=0; ratio_im=0;
        }
        double ratio_mag=sqrt(ratio_re*ratio_re+ratio_im*ratio_im);

        printf("%4d (%+7.4f,%+7.4f) (%+7.4f,%+7.4f) (%+7.4f,%+7.4f) %10.6f\n",
               c, sh_re, sh_im, L_re, L_im, ratio_re, ratio_im, ratio_mag);
    }

    /* Now compute the Gauss sum tau(chi) for comparison */
    printf("\nGauss sums tau(chi):\n");
    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];
        double tau_re=0, tau_im=0;
        for (int a=1;a<m;a++) {
            if (gcd(a,m)!=1||dlog[a]<0) continue;
            double angle_chi=2*M_PI*j*dlog[a]/(double)n_units;
            double angle_add=2*M_PI*a/(double)m;
            tau_re += cos(angle_chi)*cos(angle_add) - sin(angle_chi)*sin(angle_add);
            tau_im += cos(angle_chi)*sin(angle_add) + sin(angle_chi)*cos(angle_add);
        }
        double tau_mag=sqrt(tau_re*tau_re+tau_im*tau_im);
        printf("  c=%d: tau=(%+7.3f,%+7.3f), |tau|=%.4f, sqrt(m)=%.4f\n",
               c, tau_re, tau_im, tau_mag, sqrt((double)m));
    }

    /* Compute s_hat / (tau * L(1) / (phi * something)) */
    printf("\nGeneralized Bernoulli: B_{1,chi} = (1/m) sum a*chi(a)\n");
    for (int c = 0; c < n_odd && c < 5; c++) {
        int j = odd_j[c];
        double B_re=0, B_im=0;
        for (int a=1;a<m;a++) {
            if (gcd(a,m)!=1||dlog[a]<0) continue;
            double angle=2*M_PI*j*dlog[a]/(double)n_units;
            B_re += a*cos(angle)/(double)m;
            B_im += a*sin(angle)/(double)m;
        }
        printf("  c=%d: B1=(%+7.4f,%+7.4f), |B1|=%.4f\n",
               c, B_re, B_im, sqrt(B_re*B_re+B_im*B_im));
    }

    return 0;
}
