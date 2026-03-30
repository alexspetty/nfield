/*
 * phase_concentration.c - Measure the phase alignment of Delta vs L(1).
 *
 * For each chi: compute theta = arg(Delta) - arg(L(1,chi_bar))
 * Then measure: mean cos(theta) across characters.
 *
 * If cos(theta) is concentrated (mean >> 0): P and L are aligned.
 * If cos(theta) is uniform (mean ~ 0): P and L are uncorrelated.
 *
 * The correlation corr(|P|, |L|) is controlled by the concentration
 * of cos(theta).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000

static char *sieve;
static void build_sieve(void) {
    sieve = calloc(MAX_PRIME+1, 1);
    for(int i=2;i<=MAX_PRIME;i++) sieve[i]=1;
    for(int i=2;(long long)i*i<=MAX_PRIME;i++)
        if(sieve[i]) for(int j=i*i;j<=MAX_PRIME;j+=i) sieve[j]=0;
}

static int gcd(int a, int b) {
    while(b){int t=b;b=a%b;a=t;} return a;
}

void run_base(int b) {
    int m=b*b, phi_b=b-1;
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

    int dlog[m]; memset(dlog,-1,sizeof(int)*m);
    {int v=1;for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);}}

    int h=-1;
    for(int c=2;c<b;c++){
        int v=1,o=0;
        do{v=v*c%b;o++;}while(v!=1);
        if(o==phi_b){h=c;break;}
    }
    if(h<0)return;

    int dlog_b[b]; memset(dlog_b,-1,sizeof(dlog_b));
    {int v=1;for(int k=0;k<phi_b;k++){dlog_b[v]=k;v=v*h%b;}}

    int dl_m1=dlog[m-1];
    int *odd_j=malloc(n_units*sizeof(int)); int n_odd=0;
    for(int j=0;j<n_units;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))==n_units) odd_j[n_odd++]=j;
    }

    int even_jb[100]; int ne=0;
    for(int jb=0;jb<phi_b;jb+=2) even_jb[ne++]=jb;

    double *tau_re=malloc(ne*sizeof(double));
    double *tau_im=malloc(ne*sizeof(double));
    for(int ei=0;ei<ne;ei++){
        int jb=even_jb[ei]; double re=0,im=0;
        for(int a=1;a<b;a++){
            double angle=2*M_PI*jb*dlog_b[a]/(double)phi_b+2*M_PI*a/(double)b;
            re+=cos(angle); im+=sin(angle);
        }
        tau_re[ei]=re; tau_im[ei]=im;
    }

    /* Accumulate all L-values */
    double *Lchi_logmag=calloc(n_odd,sizeof(double));
    double *Lchi_arg=calloc(n_odd,sizeof(double));
    double *Lt_logmag=calloc(n_odd*ne,sizeof(double));
    double *Lt_arg=calloc(n_odd*ne,sizeof(double));

    for(int p=2;p<MAX_PRIME;p++){
        if(!sieve[p]||p==b)continue;
        int dl=dlog[p%m]; if(dl<0)continue;
        int pb=p%b;
        int dlb=(pb>0&&dlog_b[pb]>=0)?dlog_b[pb]:-1;
        double inv_p=1.0/p;

        for(int ci=0;ci<n_odd;ci++){
            int j=odd_j[ci];
            double chi_a=2*M_PI*j*dl/(double)n_units;
            double cr=cos(chi_a),ci2=sin(chi_a);
            {
                double wr=1-cr*inv_p, wi=-ci2*inv_p;
                double m2=wr*wr+wi*wi;
                if(m2>1e-30){Lchi_logmag[ci]-=0.5*log(m2);Lchi_arg[ci]-=atan2(wi,wr);}
            }
            if(dlb<0)continue;
            double cbr=cos(-chi_a),cbi=sin(-chi_a);
            for(int ei=1;ei<ne;ei++){
                int jb=even_jb[ei];
                double xa=2*M_PI*jb*dlb/(double)phi_b;
                double xr=cos(xa),xi=sin(xa);
                double xc_r=xr*cbr-xi*cbi, xc_i=xr*cbi+xi*cbr;
                double wr=1-xc_r*inv_p,wi=-xc_i*inv_p;
                double m2=wr*wr+wi*wi;
                if(m2>1e-30){int idx=ci*ne+ei;Lt_logmag[idx]-=0.5*log(m2);Lt_arg[idx]-=atan2(wi,wr);}
            }
        }
    }

    /* Compute Delta and relative phase for each chi */
    double sum_cos=0, sum_cos2=0;
    double sum_Ptilde_over_L=0;
    int cnt=0;

    for(int ci=0;ci<n_odd;ci++){
        double Lmag=exp(Lchi_logmag[ci]);
        if(Lmag<0.01)continue;
        double La=Lchi_arg[ci];

        double D_re=0,D_im=0;
        for(int ei=1;ei<ne;ei++){
            int idx=ci*ne+ei;
            double Ltm=exp(Lt_logmag[idx]);
            double Ltr=Ltm*cos(Lt_arg[idx]), Lti=Ltm*sin(Lt_arg[idx]);
            double tbr=tau_re[ei],tbi=-tau_im[ei];
            D_re+=tbr*Ltr-tbi*Lti;
            D_im+=tbr*Lti+tbi*Ltr;
        }
        double sr=-D_im/phi_b, si=D_re/phi_b;
        double delta_arg=atan2(si,sr);

        /* Relative phase */
        double theta=delta_arg-La;
        double ct=cos(theta);
        sum_cos+=ct;
        sum_cos2+=ct*ct;

        /* |P_tilde| = |L + Delta| */
        double Lr=Lmag*cos(La), Li=Lmag*sin(La);
        double Pr=Lr+sr, Pi=Li+si;
        double Pmag=sqrt(Pr*Pr+Pi*Pi);
        sum_Ptilde_over_L+=Pmag/Lmag;

        cnt++;
    }

    double mean_cos=sum_cos/cnt;
    double var_cos=sum_cos2/cnt-mean_cos*mean_cos;
    double mean_PL=sum_Ptilde_over_L/cnt;

    printf("Base %2d: <cos(theta)>=%+.4f std=%.4f <|P|/|L|>=%.4f "
           "n=%d 1/logb=%.4f\n",
           b, mean_cos, sqrt(var_cos>0?var_cos:0), mean_PL,
           cnt, 1.0/log(b));

    free(odd_j);free(tau_re);free(tau_im);
    free(Lchi_logmag);free(Lchi_arg);free(Lt_logmag);free(Lt_arg);
}

int main(void){
    build_sieve();
    printf("Phase concentration of Delta relative to L(1):\n\n");
    int bases[]={5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71};
    for(int i=0;i<18;i++) run_base(bases[i]);
    free(sieve);
    return 0;
}
