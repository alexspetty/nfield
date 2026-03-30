/*
 * corr_decay.c - Does corr(|P|, |L|) decay like 1/sqrt(b)?
 *
 * For each prime base b, compute:
 * - Pearson correlation between |P| and |L(1)|
 * - Check if corr * sqrt(b) is constant
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000

static char *sieve;
static void build_sieve(void) {
    sieve = calloc(MAX_PRIME+1,1);
    for(int i=2;i<=MAX_PRIME;i++) sieve[i]=1;
    for(int i=2;(long long)i*i<=MAX_PRIME;i++)
        if(sieve[i]) for(int j=i*i;j<=MAX_PRIME;j+=i) sieve[j]=0;
}

static int gcd(int a, int b) {
    while(b){int t=b;b=a%b;a=t;} return a;
}

void run_base(int b) {
    int m=b*b;
    int units[m], n_units=0;
    for(int a=1;a<m;a++) if(gcd(a,m)==1) units[n_units++]=a;

    int g=-1;
    for(int c=2;c<m;c++){
        if(gcd(c,m)!=1)continue;
        int v=1,o=0;
        do{v=(int)((long long)v*c%m);o++;}while(v!=1);
        if(o==n_units){g=c;break;}
    }
    if(g<0)return;

    int dlog[m];
    memset(dlog,-1,sizeof(int)*m);
    {int v=1;for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);}}

    int dl_m1=dlog[m-1];
    int odd_j[2000]; int n_odd=0;
    for(int j=0;j<n_units&&n_odd<2000;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))!=n_units)continue;
        odd_j[n_odd++]=j;
    }

    double P_mag[2000], L_mag[2000];
    for(int c=0;c<n_odd;c++){
        int j=odd_j[c]; double re=0,im=0;
        for(int k=1;k<=b-1;k++){
            if(dlog[k]<0)continue;
            double angle=-2*M_PI*j*dlog[k]/(double)n_units;
            re+=cos(angle); im+=sin(angle);
        }
        P_mag[c]=sqrt(re*re+im*im);
    }

    memset(L_mag,0,sizeof(double)*n_odd);
    for(int p=2;p<MAX_PRIME;p++){
        if(!sieve[p]||p==b)continue;
        int dl=dlog[p%m]; if(dl<0)continue;
        for(int c=0;c<n_odd;c++){
            double angle=2*M_PI*odd_j[c]*dl/(double)n_units;
            double re=1-cos(angle)/p, im=-sin(angle)/p;
            double mag2=re*re+im*im;
            if(mag2>1e-30) L_mag[c]-=0.5*log(mag2);
        }
    }
    for(int c=0;c<n_odd;c++) L_mag[c]=exp(L_mag[c]);

    /* Pearson correlation between |P| and |L| */
    double sx=0,sy=0,sxx=0,syy=0,sxy=0; int cnt=0;
    for(int c=0;c<n_odd;c++){
        if(P_mag[c]<1e-6||L_mag[c]<0.01)continue;
        sx+=P_mag[c]; sy+=L_mag[c];
        sxx+=P_mag[c]*P_mag[c]; syy+=L_mag[c]*L_mag[c];
        sxy+=P_mag[c]*L_mag[c]; cnt++;
    }
    double mx=sx/cnt, my=sy/cnt;
    double vx=sxx/cnt-mx*mx, vy=syy/cnt-my*my;
    double cv=sxy/cnt-mx*my;
    double corr=(vx>0&&vy>0)?cv/sqrt(vx*vy):0;

    /* Also: log-log correlation and slope */
    double lsx=0,lsy=0,lsxx=0,lsyy=0,lsxy=0; int lcnt=0;
    for(int c=0;c<n_odd;c++){
        if(P_mag[c]<1e-6||L_mag[c]<0.01)continue;
        double x=log(L_mag[c]), y=log(P_mag[c]);
        lsx+=x; lsy+=y; lsxx+=x*x; lsyy+=y*y; lsxy+=x*y; lcnt++;
    }
    double lmx=lsx/lcnt, lmy=lsy/lcnt;
    double lvx=lsxx/lcnt-lmx*lmx, lvy=lsyy/lcnt-lmy*lmy;
    double lcv=lsxy/lcnt-lmx*lmy;
    double log_slope=(lvx>0)?lcv/lvx:0;
    double log_corr=(lvx>0&&lvy>0)?lcv/sqrt(lvx*lvy):0;

    double corr_sqrtb = corr * sqrt(b);
    double corr_b = corr * b;
    double corr_logb = corr * log(b);

    printf("%5d %4d %+8.4f %+8.4f %8.4f %8.4f %8.4f %8.4f\n",
           b, cnt, corr, log_corr, log_slope,
           corr_sqrtb, corr_b, corr_logb);
}

int main(void) {
    build_sieve();

    printf("%5s %4s %8s %8s %8s %8s %8s %8s\n",
           "base", "n", "corr", "log_corr", "slope",
           "c*sqrtb", "c*b", "c*logb");

    int bases[]={5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71};
    int nb=18;
    for(int i=0;i<nb;i++) run_base(bases[i]);

    free(sieve);
    return 0;
}
