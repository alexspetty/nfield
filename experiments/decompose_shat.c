/*
 * decompose_shat.c - Verify the decomposition
 * s_hat(chi) = L(1,chi) * [A + B * S_G(chi)]
 *
 * If this holds, then:
 * |s_hat| = |L| * |A + B*S_G|
 * and |A + B*S_G| ~ |L|^{0.80} explains the exponent 1.80.
 *
 * Compute s_hat, L(1), S_G as complex numbers for each
 * odd character, then solve for A and B.
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
    int b = 5, m = 25;

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
        for (int r=1;r<p;r++) {
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
    int odd_j[100]; int n_odd=0;
    for(int j=0;j<n_units&&n_odd<100;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))!=n_units)continue;
        odd_j[n_odd++]=j;
    }

    printf("Base %d: decomposing s_hat into L * factor\n\n", b);

    for (int ci = 0; ci < n_odd; ci++) {
        int j = odd_j[ci];

        /* s_hat(chi) */
        double sh_re=0, sh_im=0;
        for(int i=0;i<n_units;i++){
            int a=units[i]; if(!has_S[a])continue;
            double sc=S[a]-mean_R[(a-1)%b];
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            sh_re+=sc*cos(angle); sh_im+=sc*sin(angle);
        }
        sh_re/=n_units; sh_im/=n_units;

        /* L(1, chi) as complex */
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

        /* S_G(chi) = -2*chi_bar(b+1)*sum_{k=1}^{b-1} chi_bar(k) */
        int dl_bp1 = dlog[(b+1)%m];
        double cb_re=0, cb_im=0;
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

        /* S_G = -2 * (cb_re+i*cb_im) * (ps_re+i*ps_im) */
        double sg_re = -2*(cb_re*ps_re - cb_im*ps_im);
        double sg_im = -2*(cb_re*ps_im + cb_im*ps_re);

        /* Compute s_hat / L(1) */
        double Lmag2 = L_re*L_re + L_im*L_im;
        double ratio_re=0, ratio_im=0;
        if(Lmag2 > 1e-20){
            ratio_re = (sh_re*L_re+sh_im*L_im)/Lmag2;
            ratio_im = (sh_im*L_re-sh_re*L_im)/Lmag2;
        }

        /* Also compute B1(chi_bar) = (1/m) sum a chi_bar(a) */
        double B1_re=0, B1_im=0;
        for(int a=1;a<m;a++){
            if(dlog[a]<0)continue;
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            B1_re += a*cos(angle)/m;
            B1_im += a*sin(angle)/m;
        }

        /* tau(chi) */
        double tau_re=0, tau_im=0;
        for(int a=1;a<m;a++){
            if(dlog[a]<0)continue;
            double angle_chi=2*M_PI*j*dlog[a]/(double)n_units;
            double angle_add=2*M_PI*a/(double)m;
            tau_re += cos(angle_chi+angle_add);
            tau_im += sin(angle_chi+angle_add);
        }

        /* s_hat / (B1 * S_G) -- if s_hat = c * B1 * S_G */
        double B1sg_re = B1_re*sg_re - B1_im*sg_im;
        double B1sg_im = B1_re*sg_im + B1_im*sg_re;
        double B1sg_mag2 = B1sg_re*B1sg_re + B1sg_im*B1sg_im;
        double r2_re=0, r2_im=0;
        if(B1sg_mag2>1e-20){
            r2_re=(sh_re*B1sg_re+sh_im*B1sg_im)/B1sg_mag2;
            r2_im=(sh_im*B1sg_re-sh_re*B1sg_im)/B1sg_mag2;
        }

        printf("j=%2d: |sh|=%6.4f |L|=%6.4f |SG|=%6.4f |B1|=%6.4f"
               " sh/L=(%+6.3f,%+6.3f) sh/(B1*SG)=(%+7.4f,%+7.4f)\n",
               j,
               sqrt(sh_re*sh_re+sh_im*sh_im),
               sqrt(Lmag2),
               sqrt(sg_re*sg_re+sg_im*sg_im),
               sqrt(B1_re*B1_re+B1_im*B1_im),
               ratio_re, ratio_im,
               r2_re, r2_im);
    }

    return 0;
}
