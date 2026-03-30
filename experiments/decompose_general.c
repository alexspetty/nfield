/*
 * decompose_general.c - Check s_hat = B1 * S_G / phi(m) at all bases.
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

void run_base(int b) {
    int m = b*b;
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
    int odd_j[1000]; int n_odd=0;
    for(int j=0;j<n_units&&n_odd<1000;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))!=n_units)continue;
        odd_j[n_odd++]=j;
    }

    int dl_bp1 = dlog[(b+1)%m];

    /* For each odd char: compute |s_hat / (B1 * S_G)| * phi */
    double sum_r = 0, sum_r2 = 0; int cnt = 0;

    for(int ci=0;ci<n_odd;ci++){
        int j=odd_j[ci];

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

        /* S_G */
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
        double sg_re=-2*(cb_re*ps_re-cb_im*ps_im);
        double sg_im=-2*(cb_re*ps_im+cb_im*ps_re);

        /* B1 * S_G */
        double prod_re = B1_re*sg_re - B1_im*sg_im;
        double prod_im = B1_re*sg_im + B1_im*sg_re;
        double prod_mag = sqrt(prod_re*prod_re + prod_im*prod_im);
        double sh_mag = sqrt(sh_re*sh_re + sh_im*sh_im);

        if(prod_mag < 1e-8 || sh_mag < 1e-8) continue;

        /* ratio = s_hat * phi / (B1 * S_G) */
        double prod_mag2 = prod_re*prod_re + prod_im*prod_im;
        double r_re = n_units*(sh_re*prod_re+sh_im*prod_im)/prod_mag2;
        double r_im = n_units*(sh_im*prod_re-sh_re*prod_im)/prod_mag2;
        double r_mag = sqrt(r_re*r_re + r_im*r_im);

        sum_r += r_mag;
        sum_r2 += r_mag*r_mag;
        cnt++;
    }

    double mean = sum_r / cnt;
    double var = sum_r2/cnt - mean*mean;
    double cv = sqrt(var>0?var:0)/mean;

    printf("base %2d: mean|sh*phi/(B1*SG)| = %.6f, CV = %.6f (%d chars)\n",
           b, mean, cv, cnt);
}

int main(void) {
    int bases[]={5,7,11,13,17,19};
    for(int i=0;i<6;i++) run_base(bases[i]);
    return 0;
}
