/*
 * running_exponent.c - Does the exponent converge as we add bases?
 *
 * Compute the log-log exponent of |s_hat| vs |L(1)| using
 * a growing pool of bases. If it converges, the limit is
 * the universal exponent.
 *
 * Also: track the standard error of the slope to see if
 * it tightens with more bases.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <omp.h>

#define MAX_PRIME 2000000
#define MAX_POINTS 10000

static char *sieve;
static void build_sieve(void) {
    sieve = calloc(MAX_PRIME+1, 1);
    for (int i=2;i<=MAX_PRIME;i++) sieve[i]=1;
    for (int i=2;(long long)i*i<=MAX_PRIME;i++)
        if(sieve[i]) for(int j=i*i;j<=MAX_PRIME;j+=i) sieve[j]=0;
}

static int gcd(int a, int b) {
    while(b){int t=b;b=a%b;a=t;} return a;
}

double all_x[MAX_POINTS], all_y[MAX_POINTS];
int n_all = 0;

/* per-base data for running average */
int base_start[100], base_count[100];
int n_bases_done = 0;

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

    int S[m],has_S[m];
    memset(has_S,0,sizeof(int)*m);
    for(int p=m+1;p<80000;p++){
        if(!sieve[p]||gcd(p,b)!=1)continue;
        int a=p%m; if(has_S[a])continue;
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

    double sh_mag[1000], L_mag[1000];
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

    int start = n_all;
    for(int c=0;c<n_odd;c++){
        if(sh_mag[c]<1e-8||L_mag[c]<0.01)continue;
        if(n_all>=MAX_POINTS)break;
        all_x[n_all]=log(L_mag[c]);
        all_y[n_all]=log(sh_mag[c]);
        n_all++;
    }
    base_start[n_bases_done] = start;
    base_count[n_bases_done] = n_all - start;
    n_bases_done++;
}

void fit(int n, double *slope, double *se, double *r2) {
    double sx=0,sy=0,sxx=0,syy=0,sxy=0;
    for(int i=0;i<n;i++){
        sx+=all_x[i]; sy+=all_y[i];
        sxx+=all_x[i]*all_x[i]; syy+=all_y[i]*all_y[i];
        sxy+=all_x[i]*all_y[i];
    }
    double mx=sx/n, my=sy/n;
    double vx=sxx/n-mx*mx, vy=syy/n-my*my;
    double cv=sxy/n-mx*my;
    *slope = cv/vx;
    *r2 = (cv*cv)/(vx*vy);

    double sse=0;
    double intercept = my - (*slope)*mx;
    for(int i=0;i<n;i++){
        double res = all_y[i] - (*slope)*all_x[i] - intercept;
        sse += res*res;
    }
    double rse = sqrt(sse/(n-2));
    *se = rse/sqrt(n*vx);
}

int main(void) {
    build_sieve();

    int bases[] = {5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61};
    int nb = 16;

    printf("Computing bases...\n");
    for(int i=0;i<nb;i++){
        run_base(bases[i]);
        printf("  base %d: %d points (total %d)\n",
               bases[i], base_count[i], n_all);
    }

    printf("\nRunning exponent as bases are added:\n");
    printf("%6s %6s %8s %8s %8s %10s\n",
           "bases", "points", "exponent", "SE", "R^2", "95% CI");

    int cumul = 0;
    for(int i=0;i<nb;i++){
        cumul += base_count[i];
        if(cumul < 5) continue;

        double slope, se, r2;
        fit(cumul, &slope, &se, &r2);

        printf("%6d %6d %8.4f %8.4f %8.4f [%.3f, %.3f]\n",
               i+1, cumul, slope, se, r2,
               slope-1.96*se, slope+1.96*se);
    }

    /* Key constants for comparison */
    printf("\nReference values:\n");
    printf("  9/5       = %.6f\n", 9.0/5);
    printf("  2-1/phi   = %.6f\n", 2-(sqrt(5)-1)/2);
    printf("  phi+1/phi = %.6f\n", (1+sqrt(5))/2 + 2/(1+sqrt(5)));
    printf("  e/pi+1    = %.6f\n", exp(1)/M_PI+1);
    printf("  2-1/5     = %.6f\n", 2-0.2);
    printf("  2-1/e     = %.6f\n", 2-1/exp(1));
    printf("  pi/sqrt(3)= %.6f\n", M_PI/sqrt(3));
    printf("  sqrt(pi)  = %.6f\n", sqrt(M_PI));

    free(sieve);
    return 0;
}
