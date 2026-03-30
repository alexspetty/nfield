/*
 * L_squared.c - Is |s_hat| ~ |L(1)|^2 at all bases?
 *
 * At base 5: |s_hat|/|L|^2 = 0.2835 exactly.
 * Check at other bases.
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
    int odd_j[1000]; int n_odd=0;
    for(int j=0;j<n_units&&n_odd<1000;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))!=n_units)continue;
        odd_j[n_odd++]=j;
    }

    /* Compute |s_hat| */
    double sh_mag[1000];
    for(int c=0;c<n_odd;c++){
        int j=odd_j[c]; double re=0,im=0;
        for(int i=0;i<n_units;i++){
            int a=units[i]; if(!has_S[a])continue;
            double sc=S[a]-mean_R[(a-1)%b];
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            re+=sc*cos(angle); im+=sc*sin(angle);
        }
        re/=n_units; im/=n_units;
        sh_mag[c]=sqrt(re*re+im*im);
    }

    /* Compute |L(1)| */
    double L1[1000];
    memset(L1,0,sizeof(double)*n_odd);
    for(int p=2;p<MAX_PRIME;p++){
        if(!is_prime(p)||p==b)continue;
        int dl=dlog[p%m]; if(dl<0)continue;
        for(int c=0;c<n_odd;c++){
            double angle=2*M_PI*odd_j[c]*dl/(double)n_units;
            double re=1-cos(angle)/p, im=-sin(angle)/p;
            double mag2=re*re+im*im;
            if(mag2>1e-30) L1[c]-=0.5*log(mag2);
        }
    }
    for(int c=0;c<n_odd;c++) L1[c]=exp(L1[c]);

    /* Compute |s_hat|/|L|^2 and check constancy */
    double sum_r=0, sum_r2=0; int cnt=0;
    for(int c=0;c<n_odd;c++){
        if(sh_mag[c]<1e-8||L1[c]<0.01)continue;
        double r=sh_mag[c]/(L1[c]*L1[c]);
        sum_r+=r; sum_r2+=r*r; cnt++;
    }
    double mean=sum_r/cnt;
    double var=sum_r2/cnt-mean*mean;
    double cv=sqrt(var>0?var:0)/mean;

    /* Also check |s_hat|/|L|^1.5 and |s_hat|/|L|^2.5 */
    double sum15=0,sum25=0;
    for(int c=0;c<n_odd;c++){
        if(sh_mag[c]<1e-8||L1[c]<0.01)continue;
        sum15+=sh_mag[c]/pow(L1[c],1.5);
        sum25+=sh_mag[c]/pow(L1[c],2.5);
    }

    /* Best-fit exponent via log-log regression */
    double sx=0,sy=0,sxx=0,sxy=0; int n=0;
    for(int c=0;c<n_odd;c++){
        if(sh_mag[c]<1e-8||L1[c]<0.01)continue;
        double x=log(L1[c]), y=log(sh_mag[c]);
        sx+=x; sy+=y; sxx+=x*x; sxy+=x*y; n++;
    }
    double slope=(n*sxy-sx*sy)/(n*sxx-sx*sx);

    printf("%5d %4d %8.4f %8.4f %8.2f\n",
           b, cnt, mean, cv, slope);
}

int main(void) {
    printf("%5s %4s %8s %8s %8s\n",
           "base", "n", "|sh|/L^2", "CV", "exponent");

    int bases[]={5,7,11,13,17,19,23,29,31,37};
    for(int i=0;i<10;i++) run_base(bases[i]);
    return 0;
}
