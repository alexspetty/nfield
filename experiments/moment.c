/*
 * moment.c - Compute the L-value moment implied by F°(1) convergence.
 *
 * F°(1) = -(1/phi) sum_chi B1(chi_bar) * conj(S_G(chi)) * P(1,chi)
 *
 * Since B1 ~ L(1) and P(1,chi) ~ log L(1,chi) - H(1,chi):
 * F°(1) ~ sum |L(1)| * |P_short| * log|L(1)| (roughly)
 *
 * Compute each factor explicitly and see what moment F°(1) encodes.
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
    int b = 13, m = b * b;

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
        int a = p%m;
        if (has_S[a]) continue;
        int C = 0;
        for (int r=1;r<p;r++){
            int d1=(int)((long long)b*r/p);
            long long br=(long long)b*r%p;
            int d2=(int)((long long)b*br/p);
            if(d1==d2)C++;
        }
        S[a]=C-(p-1)/b; has_S[a]=1;
    }

    double cls_sum[b]; int cls_cnt[b];
    memset(cls_sum,0,sizeof(double)*b);
    memset(cls_cnt,0,sizeof(int)*b);
    for(int i=0;i<n_units;i++){
        int a=units[i]; if(!has_S[a])continue;
        cls_sum[(a-1)%b]+=S[a]; cls_cnt[(a-1)%b]++;
    }
    double mean_R[b];
    for(int R=0;R<b;R++)
        mean_R[R]=cls_cnt[R]>0?cls_sum[R]/cls_cnt[R]:0;

    int dl_m1=dlog[m-1];
    int odd_j[500]; int n_odd=0;
    for(int j=0;j<n_units&&n_odd<500;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))!=n_units)continue;
        odd_j[n_odd++]=j;
    }

    printf("Base %d: %d odd characters\n\n", b, n_odd);

    /* For each character, compute all factors */
    printf("%4s %8s %8s %8s %8s %10s %10s\n",
           "c", "|B1|", "|SG|", "|L(1)|", "|P(1)|",
           "Re(term)", "|term|");

    double F_total_re = 0, F_total_im = 0;

    for (int ci = 0; ci < n_odd; ci++) {
        int j = odd_j[ci];

        /* s_hat */
        double sh_re=0, sh_im=0;
        for(int i=0;i<n_units;i++){
            int a=units[i]; if(!has_S[a])continue;
            double sc=S[a]-mean_R[(a-1)%b];
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            sh_re+=sc*cos(angle); sh_im+=sc*sin(angle);
        }
        sh_re/=n_units; sh_im/=n_units;

        /* B1(chi_bar) */
        double B1_re=0, B1_im=0;
        for(int a=1;a<m;a++){
            if(dlog[a]<0)continue;
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            B1_re+=a*cos(angle)/m; B1_im+=a*sin(angle)/m;
        }
        double B1_mag = sqrt(B1_re*B1_re + B1_im*B1_im);

        /* S_G */
        int dl_bp1 = dlog[(b+1)%m];
        double cb_re=0,cb_im=0;
        if(dl_bp1>=0){
            double angle=-2*M_PI*j*dl_bp1/(double)n_units;
            cb_re=cos(angle); cb_im=sin(angle);
        }
        double ps_re=0, ps_im=0;
        for(int k=1;k<=b-1;k++){
            if(dlog[k]<0)continue;
            double angle=-2*M_PI*j*dlog[k]/(double)n_units;
            ps_re+=cos(angle); ps_im+=sin(angle);
        }
        double sg_re=-2*(cb_re*ps_re-cb_im*ps_im);
        double sg_im=-2*(cb_re*ps_im+cb_im*ps_re);
        double sg_mag = sqrt(sg_re*sg_re + sg_im*sg_im);

        /* L(1, chi) via Euler product */
        double logL_re=0, logL_im=0;
        for(int p=2;p<MAX_PRIME;p++){
            if(!is_prime(p)||p==b)continue;
            int dl=dlog[p%m]; if(dl<0)continue;
            double angle=2*M_PI*j*dl/(double)n_units;
            double w_re=1-cos(angle)/p, w_im=-sin(angle)/p;
            double mag2=w_re*w_re+w_im*w_im;
            logL_re -= 0.5*log(mag2);
            logL_im -= atan2(w_im, w_re);
        }
        double L_re=exp(logL_re)*cos(logL_im);
        double L_im=exp(logL_re)*sin(logL_im);
        double L_mag=exp(logL_re);

        /* P(1, chi) = sum_p chi(p)/p */
        double P1_re=0, P1_im=0;
        for(int p=m+1;p<MAX_PRIME;p++){
            if(!is_prime(p)||gcd(p,b)!=1)continue;
            int dl=dlog[p%m]; if(dl<0)continue;
            double angle=2*M_PI*j*dl/(double)n_units;
            P1_re+=cos(angle)/p; P1_im+=sin(angle)/p;
        }
        double P1_mag=sqrt(P1_re*P1_re+P1_im*P1_im);

        /* The term: s_hat(chi) * P(1, chi) */
        /* F°(1) = sum s_hat(chi) * P(1,chi) */
        double term_re = sh_re*P1_re - sh_im*P1_im;
        double term_im = sh_re*P1_im + sh_im*P1_re;
        double term_mag = sqrt(term_re*term_re + term_im*term_im);

        F_total_re += term_re;
        F_total_im += term_im;

        if (ci < 15) {
            printf("%4d %8.4f %8.4f %8.4f %8.4f %+10.6f %10.6f\n",
                   ci, B1_mag, sg_mag, L_mag, P1_mag,
                   term_re, term_mag);
        }
    }

    printf("...\n");
    printf("\nF°(1) = %+.6f + %.6fi, |F°(1)| = %.6f\n",
           F_total_re, F_total_im,
           sqrt(F_total_re*F_total_re + F_total_im*F_total_im));

    /* Now: express F°(1) as a moment.
     * F°(1) = sum s_hat * P(1) = sum (-B1*conj(SG)/phi) * P(1)
     * = -(1/phi) sum B1 * conj(SG) * P(1)
     * = -(1/phi) sum B1 * conj(SG) * [logL(1) - H(1)]
     *
     * |B1| = sqrt(m) |L(1)| / pi
     * |SG| = 2|P_short| ~ |L(1)|^{0.8}
     *
     * So |term| ~ |L(1)| * |L(1)|^{0.8} * |logL(1)|
     *          ~ |L(1)|^{1.8} * log|L(1)|
     *
     * This is a 1.8-th moment of L(1) weighted by log|L(1)|.
     */

    printf("\nThe convergence F°(1) < infinity encodes:\n");
    printf("  sum |L(1,chi)|^{~1.8} * |log L(1,chi)| < infinity\n");
    printf("  (a weighted moment of L-function special values)\n");

    /* Compute the actual moments for comparison */
    double mom1=0, mom2=0, mom18=0, mom18log=0;
    int cnt=0;
    for(int ci=0;ci<n_odd;ci++){
        int j=odd_j[ci];
        double logL=0;
        for(int p=2;p<MAX_PRIME;p++){
            if(!is_prime(p)||p==b)continue;
            int dl=dlog[p%m]; if(dl<0)continue;
            double angle=2*M_PI*j*dl/(double)n_units;
            double re=1-cos(angle)/p, im=-sin(angle)/p;
            double mag2=re*re+im*im;
            if(mag2>1e-30) logL-=0.5*log(mag2);
        }
        double L=exp(logL);
        mom1+=L;
        mom2+=L*L;
        mom18+=pow(L,1.8);
        mom18log+=pow(L,1.8)*fabs(logL);
        cnt++;
    }

    printf("\nL-value moments over %d odd chars (base %d):\n", cnt, b);
    printf("  mean |L(1)|      = %.4f\n", mom1/cnt);
    printf("  mean |L(1)|^2    = %.4f\n", mom2/cnt);
    printf("  mean |L(1)|^1.8  = %.4f\n", mom18/cnt);
    printf("  mean |L|^1.8*log = %.4f\n", mom18log/cnt);

    return 0;
}
