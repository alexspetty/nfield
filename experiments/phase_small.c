/* Quick phase concentration: bases 5-31, 500K primes */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 500000

static char sieve[MAX_PRIME+1];
static void build_sieve(void){
    memset(sieve,1,sizeof(sieve)); sieve[0]=sieve[1]=0;
    for(int i=2;(long long)i*i<=MAX_PRIME;i++)
        if(sieve[i]) for(int j=i*i;j<=MAX_PRIME;j+=i) sieve[j]=0;
}
static int gcd(int a,int b){while(b){int t=b;b=a%b;a=t;}return a;}

void run_base(int b){
    int m=b*b, phi_b=b-1;
    int n_units=0;
    for(int a=1;a<m;a++) if(gcd(a,m)==1) n_units++;

    int g=-1;
    for(int c=2;c<m;c++){
        if(gcd(c,m)!=1)continue;
        int v=1,o=0;
        do{v=(int)((long long)v*c%m);o++;}while(v!=1);
        if(o==n_units){g=c;break;}
    }
    if(g<0)return;

    int *dlog=calloc(m,sizeof(int));
    memset(dlog,-1,sizeof(int)*m);
    {int v=1;for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);}}

    int h=-1;
    for(int c=2;c<b;c++){int v=1,o=0;do{v=v*c%b;o++;}while(v!=1);if(o==phi_b){h=c;break;}}
    if(h<0){free(dlog);return;}

    int dlog_b[64]; memset(dlog_b,-1,sizeof(dlog_b));
    {int v=1;for(int k=0;k<phi_b;k++){dlog_b[v]=k;v=v*h%b;}}

    int dl_m1=dlog[m-1];
    int *odd_j=malloc(n_units*sizeof(int)); int n_odd=0;
    for(int j=0;j<n_units;j++){
        long long t=2LL*j*dl_m1;
        if((int)(t%(2*n_units))==n_units) odd_j[n_odd++]=j;
    }

    int even_jb[64]; int ne=0;
    for(int jb=0;jb<phi_b;jb+=2) even_jb[ne++]=jb;

    double tau_re[64],tau_im[64];
    for(int ei=0;ei<ne;ei++){
        int jb=even_jb[ei];double re=0,im=0;
        for(int a=1;a<b;a++){
            double angle=2*M_PI*jb*dlog_b[a]/(double)phi_b+2*M_PI*a/(double)b;
            re+=cos(angle);im+=sin(angle);
        }
        tau_re[ei]=re;tau_im[ei]=im;
    }

    double *Lm=calloc(n_odd,sizeof(double));
    double *La=calloc(n_odd,sizeof(double));
    double *Tlm=calloc(n_odd*ne,sizeof(double));
    double *Tla=calloc(n_odd*ne,sizeof(double));

    for(int p=2;p<MAX_PRIME;p++){
        if(!sieve[p]||p==b)continue;
        int dl=dlog[p%m];if(dl<0)continue;
        int pb=p%b;int dlb=(pb>0&&pb<b&&dlog_b[pb]>=0)?dlog_b[pb]:-1;
        double ip=1.0/p;
        for(int ci=0;ci<n_odd;ci++){
            int j=odd_j[ci];
            double ca=2*M_PI*j*dl/(double)n_units;
            double cr=cos(ca),si=sin(ca);
            double wr=1-cr*ip,wi=-si*ip;
            double m2=wr*wr+wi*wi;
            if(m2>1e-30){Lm[ci]-=0.5*log(m2);La[ci]-=atan2(wi,wr);}
            if(dlb<0)continue;
            double cbr=cos(-ca),cbi=sin(-ca);
            for(int ei=1;ei<ne;ei++){
                int jb=even_jb[ei];
                double xa=2*M_PI*jb*dlb/(double)phi_b;
                double xr=cos(xa),xi=sin(xa);
                double xcr=xr*cbr-xi*cbi,xci=xr*cbi+xi*cbr;
                double wr2=1-xcr*ip,wi2=-xci*ip;
                double m3=wr2*wr2+wi2*wi2;
                if(m3>1e-30){int idx=ci*ne+ei;Tlm[idx]-=0.5*log(m3);Tla[idx]-=atan2(wi2,wr2);}
            }
        }
    }

    double sum_cos=0;int cnt=0;
    for(int ci=0;ci<n_odd;ci++){
        double Lmag=exp(Lm[ci]);if(Lmag<0.01)continue;
        double Larg=La[ci];
        double Dr=0,Di=0;
        for(int ei=1;ei<ne;ei++){
            int idx=ci*ne+ei;
            double tm=exp(Tlm[idx]);
            double tr=tm*cos(Tla[idx]),ti=tm*sin(Tla[idx]);
            double tbr=tau_re[ei],tbi=-tau_im[ei];
            Dr+=tbr*tr-tbi*ti;Di+=tbr*ti+tbi*tr;
        }
        double sr=-Di/phi_b,si2=Dr/phi_b;
        double theta=atan2(si2,sr)-Larg;
        sum_cos+=cos(theta);cnt++;
    }
    printf("Base %2d: <cos(theta)>=%+.4f  n=%d  1/logb=%.4f\n",
           b,sum_cos/cnt,cnt,1.0/log(b));
    free(dlog);free(odd_j);free(Lm);free(La);free(Tlm);free(Tla);
}

int main(void){
    build_sieve();
    int bases[]={5,7,11,13,17,19,23,29,31};
    for(int i=0;i<9;i++) run_base(bases[i]);
    return 0;
}
