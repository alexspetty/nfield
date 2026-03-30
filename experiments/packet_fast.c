/*
 * packet_fast.c - Fast packet computation with OpenMP.
 *
 * Key optimization: scan primes ONCE, accumulate all
 * (chi, xi) Euler products simultaneously.
 *
 * For each prime p:
 *   For each odd chi (index j):
 *     For each even xi (index jb):
 *       Update log|L(1, xi*chi_bar)| and arg
 *
 * Then compute Delta for each chi from the precomputed L values.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <omp.h>

#define MAX_PRIME 2000000

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

void run_base(int b) {
    int m = b * b;
    int phi_b = b - 1;
    int units[m], n_units = 0;
    for (int a=1;a<m;a++) if(gcd(a,m)==1) units[n_units++]=a;

    /* Generator mod m */
    int g = -1;
    for (int c=2;c<m;c++){
        if(gcd(c,m)!=1)continue;
        int v=1,o=0;
        do{v=(int)((long long)v*c%m);o++;}while(v!=1);
        if(o==n_units){g=c;break;}
    }
    if(g<0)return;

    int dlog[m];
    memset(dlog,-1,sizeof(int)*m);
    {int v=1;for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);}}

    /* Generator mod b */
    int h = -1;
    for (int c=2;c<b;c++){
        int v=1,o=0;
        do{v=v*c%b;o++;}while(v!=1);
        if(o==phi_b){h=c;break;}
    }
    if(h<0)return;

    int dlog_b[b];
    memset(dlog_b,-1,sizeof(dlog_b));
    {int v=1;for(int k=0;k<phi_b;k++){dlog_b[v]=k;v=v*h%b;}}

    int dl_m1 = dlog[m-1];
    int *odd_j = malloc(n_units * sizeof(int));
    int n_odd = 0;
    for(int j=0;j<n_units;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))==n_units) odd_j[n_odd++]=j;
    }

    /* Even xi indices mod b: jb = 0, 2, 4, ..., b-3 */
    int even_jb[100]; int ne = 0;
    for(int jb=0;jb<phi_b;jb+=2) even_jb[ne++]=jb;

    /* Gauss sums tau(xi_bar) for each even xi */
    double *tau_re = malloc(ne*sizeof(double));
    double *tau_im = malloc(ne*sizeof(double));
    for(int ei=0;ei<ne;ei++){
        int jb=even_jb[ei];
        double re=0,im=0;
        for(int a=1;a<b;a++){
            double angle=2*M_PI*jb*dlog_b[a]/(double)phi_b + 2*M_PI*a/(double)b;
            re+=cos(angle); im+=sin(angle);
        }
        tau_re[ei]=re; tau_im[ei]=im;
    }

    /* Allocate L-value arrays: L[ci][ei] for chi index ci, xi index ei */
    /* Store log|L| and arg separately for accumulation */
    double *logL_mag = calloc(n_odd * ne, sizeof(double));  /* [ci*ne + ei] */
    double *logL_arg = calloc(n_odd * ne, sizeof(double));

    /* Also L(1, chi) itself (ei=0 corresponds to trivial xi) */
    double *L_chi_re = calloc(n_odd, sizeof(double));
    double *L_chi_im = calloc(n_odd, sizeof(double));
    double *L_chi_logmag = calloc(n_odd, sizeof(double));
    double *L_chi_arg = calloc(n_odd, sizeof(double));

    /* Precompute: for each prime p, its dlog mod m and mod b */
    /* Then scan once and update all */

    /* Scan primes, update all Euler products */
    for (int p=2;p<MAX_PRIME;p++){
        if(!sieve[p]||p==b)continue;
        int dl=dlog[p%m]; if(dl<0)continue;
        int pb=p%b;
        int dlb=(pb>0&&dlog_b[pb]>=0)?dlog_b[pb]:-1;

        double inv_p = 1.0/p;

        /* For each odd chi */
        for(int ci=0;ci<n_odd;ci++){
            int j=odd_j[ci];
            double chi_angle = 2*M_PI*j*dl/(double)n_units;
            double chi_re = cos(chi_angle), chi_im = sin(chi_angle);

            /* L(1, chi): use chi directly */
            {
                double w_re=1-chi_re*inv_p, w_im=-chi_im*inv_p;
                double mag2=w_re*w_re+w_im*w_im;
                if(mag2>1e-30){
                    L_chi_logmag[ci]-=0.5*log(mag2);
                    L_chi_arg[ci]-=atan2(w_im,w_re);
                }
            }

            if(dlb<0)continue; /* p divides b, skip twisted L */

            /* chi_bar angle = -chi_angle */
            double cbar_re=cos(-chi_angle), cbar_im=sin(-chi_angle);

            /* For each even xi */
            for(int ei=1;ei<ne;ei++){ /* skip trivial xi (ei=0) */
                int jb=even_jb[ei];
                double xi_angle=2*M_PI*jb*dlb/(double)phi_b;
                double xi_re=cos(xi_angle), xi_im=sin(xi_angle);

                /* (xi * chi_bar)(p) */
                double xc_re=xi_re*cbar_re-xi_im*cbar_im;
                double xc_im=xi_re*cbar_im+xi_im*cbar_re;

                /* 1 - (xi*chi_bar)(p)/p */
                double w_re=1-xc_re*inv_p, w_im=-xc_im*inv_p;
                double mag2=w_re*w_re+w_im*w_im;
                if(mag2>1e-30){
                    int idx=ci*ne+ei;
                    logL_mag[idx]-=0.5*log(mag2);
                    logL_arg[idx]-=atan2(w_im,w_re);
                }
            }
        }
    }

    /* Convert L(1,chi) from log form */
    for(int ci=0;ci<n_odd;ci++){
        double mag=exp(L_chi_logmag[ci]);
        L_chi_re[ci]=mag*cos(L_chi_arg[ci]);
        L_chi_im[ci]=mag*sin(L_chi_arg[ci]);
    }

    /* For each chi, compute Delta and |Delta|/|L| */
    double sum_ratio=0, sum_ratio2=0;
    int cnt=0;

    #pragma omp parallel for reduction(+:sum_ratio,sum_ratio2,cnt)
    for(int ci=0;ci<n_odd;ci++){
        double L_mag=exp(L_chi_logmag[ci]);
        if(L_mag<0.01)continue;

        /* Delta = (i/phi_b) sum_{ei=1}^{ne-1} tau(xi_bar) * L(1, xi*chi_bar) */
        double D_re=0, D_im=0;

        for(int ei=1;ei<ne;ei++){
            int idx=ci*ne+ei;
            double Lt_mag=exp(logL_mag[idx]);
            double Lt_re=Lt_mag*cos(logL_arg[idx]);
            double Lt_im=Lt_mag*sin(logL_arg[idx]);

            /* tau_bar = conj(tau) */
            double tb_re=tau_re[ei], tb_im=-tau_im[ei];

            /* tau_bar * L_twisted */
            double prod_re=tb_re*Lt_re-tb_im*Lt_im;
            double prod_im=tb_re*Lt_im+tb_im*Lt_re;

            D_re+=prod_re;
            D_im+=prod_im;
        }

        /* Multiply by i/phi_b: i*(D_re+iD_im) = -D_im + iD_re */
        double scaled_re=-D_im/phi_b;
        double scaled_im=D_re/phi_b;

        double delta_mag=sqrt(scaled_re*scaled_re+scaled_im*scaled_im);
        double ratio=delta_mag/L_mag;

        sum_ratio+=ratio;
        sum_ratio2+=ratio*ratio;
        cnt++;
    }

    double mean=sum_ratio/cnt;
    double var=sum_ratio2/cnt-mean*mean;
    printf("Base %2d: mean|Delta|/|L| = %.4f, std=%.4f (%d chars) "
           "1/sqrt(b)=%.4f 1/log(b)=%.4f\n",
           b, mean, sqrt(var>0?var:0), cnt,
           1.0/sqrt(b), 1.0/log(b));

    free(odd_j); free(tau_re); free(tau_im);
    free(logL_mag); free(logL_arg);
    free(L_chi_re); free(L_chi_im);
    free(L_chi_logmag); free(L_chi_arg);
}

int main(void) {
    build_sieve();

    int bases[]={5,7,11,13,17,19,23,29,31,37,41,43};
    int nb=12;
    for(int i=0;i<nb;i++) run_base(bases[i]);

    free(sieve);
    return 0;
}
