/*
 * L_correlation_sweep.c - Is corr(|s_hat|, |L|) = 0.92 universal?
 *
 * For each prime base b, compute:
 * - |s_hat(chi)| for each odd character
 * - |L(s, chi)| via truncated Euler product at s = 0.7
 * - |L(1, chi)| (special value at s = 1)
 * - Pearson correlation between them
 *
 * Also: check if |s_hat| correlates better with |L(1)| than |L(0.7)|
 * (which would mean the collision weight tracks the special value,
 * not the depth-dependent value).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <omp.h>

#define MAX_PRIME 2000000

static char *sieve;
static void build_sieve(void) {
    sieve = calloc(MAX_PRIME + 1, 1);
    for (int i = 2; i <= MAX_PRIME; i++) sieve[i] = 1;
    for (int i = 2; (long long)i * i <= MAX_PRIME; i++)
        if (sieve[i])
            for (int j = i * i; j <= MAX_PRIME; j += i)
                sieve[j] = 0;
}

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

double pearson(double *x, double *y, int n) {
    double sx=0,sy=0,sxx=0,syy=0,sxy=0;
    int cnt=0;
    for (int i = 0; i < n; i++) {
        if (x[i] < 1e-10) continue;
        sx+=x[i]; sy+=y[i];
        sxx+=x[i]*x[i]; syy+=y[i]*y[i];
        sxy+=x[i]*y[i]; cnt++;
    }
    double mx=sx/cnt, my=sy/cnt;
    double vx=sxx/cnt-mx*mx, vy=syy/cnt-my*my;
    double cv=sxy/cnt-mx*my;
    return (vx>0&&vy>0) ? cv/sqrt(vx*vy) : 0;
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
        if (!sieve[p] || gcd(p,b)!=1) continue;
        int a = p%m;
        if (has_S[a]) continue;
        int C=0;
        for(int r=1;r<p;r++){
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
        int a=units[i];
        if(!has_S[a])continue;
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

    /* |s_hat| */
    double sh_mag[1000];
    for(int c=0;c<n_odd;c++){
        int j=odd_j[c];
        double re=0,im=0;
        for(int i=0;i<n_units;i++){
            int a=units[i];
            if(!has_S[a])continue;
            double sc=S[a]-mean_R[(a-1)%b];
            double angle=-2*M_PI*j*dlog[a]/(double)n_units;
            re+=sc*cos(angle); im+=sc*sin(angle);
        }
        re/=n_units; im/=n_units;
        sh_mag[c]=sqrt(re*re+im*im);
    }

    /* |L(s, chi)| at s = 0.6, 0.7, 0.8, 1.0 */
    double L_06[1000], L_07[1000], L_08[1000], L_10[1000];
    memset(L_06,0,sizeof(double)*n_odd);
    memset(L_07,0,sizeof(double)*n_odd);
    memset(L_08,0,sizeof(double)*n_odd);
    memset(L_10,0,sizeof(double)*n_odd);

    for(int p=2;p<MAX_PRIME;p++){
        if(!sieve[p]||p==b)continue;
        int dl=dlog[p%m];
        if(dl<0)continue;
        double p06=pow((double)p,-0.6);
        double p07=pow((double)p,-0.7);
        double p08=pow((double)p,-0.8);
        double p10=pow((double)p,-1.0);

        for(int c=0;c<n_odd;c++){
            double angle=2*M_PI*odd_j[c]*dl/(double)n_units;
            double cr=cos(angle), ci=sin(angle);

            double re,im,mag2;

            re=1-cr*p06; im=-ci*p06; mag2=re*re+im*im;
            if(mag2>1e-30) L_06[c]-=0.5*log(mag2);

            re=1-cr*p07; im=-ci*p07; mag2=re*re+im*im;
            if(mag2>1e-30) L_07[c]-=0.5*log(mag2);

            re=1-cr*p08; im=-ci*p08; mag2=re*re+im*im;
            if(mag2>1e-30) L_08[c]-=0.5*log(mag2);

            re=1-cr*p10; im=-ci*p10; mag2=re*re+im*im;
            if(mag2>1e-30) L_10[c]-=0.5*log(mag2);
        }
    }

    for(int c=0;c<n_odd;c++){
        L_06[c]=exp(L_06[c]);
        L_07[c]=exp(L_07[c]);
        L_08[c]=exp(L_08[c]);
        L_10[c]=exp(L_10[c]);
    }

    double r06=pearson(sh_mag,L_06,n_odd);
    double r07=pearson(sh_mag,L_07,n_odd);
    double r08=pearson(sh_mag,L_08,n_odd);
    double r10=pearson(sh_mag,L_10,n_odd);

    printf("%5d %4d %+7.4f %+7.4f %+7.4f %+7.4f\n",
           b, n_odd, r06, r07, r08, r10);
}

int main(void) {
    build_sieve();

    printf("%5s %4s %7s %7s %7s %7s\n",
           "base","n","r(0.6)","r(0.7)","r(0.8)","r(1.0)");

    int bases[]={3,5,7,11,13,17,19,23,29,31,37};
    int nb=11;

    #pragma omp parallel for schedule(dynamic)
    for(int i=0;i<nb;i++)
        run_base(bases[i]);

    free(sieve);
    return 0;
}
