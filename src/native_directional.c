/* Complete native clock projections of adjacent polarity differences and
 * address indicators. Numerical matrix ranks are explicitly reported as such. */
#include "native_directional.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>

extern void dsyev_(const char *,const char *,const int *,double *,const int *,
                   double *,double *,const int *,int *);
static unsigned gcd_d(unsigned a,unsigned b)
{ while(b) { unsigned r=a%b;a=b;b=r; }return a; }
static long double psi_d(long double x)
{
    long double correction=0;
    while(x<16) { correction-=1/x;x+=1; }
    long double z=1/(x*x);
    return correction+logl(x)-.5L/x-z*(1.L/12-z*(1.L/120-z*(1.L/252-z*(1.L/240-z*(1.L/132-z*691.L/32760)))));
}
static int polarity_d(unsigned n,unsigned b)
{ unsigned h=n/(b*b),u=(n/b)%b,v=n%b;return ((h+u+v)/(b-1))%2?-1:1; }
static int cholesky(unsigned n,const double *G,unsigned stride,double *L)
{
    for(unsigned i=0;i<n;++i)for(unsigned j=0;j<=i;++j) {
        long double x=G[i*stride+j];for(unsigned k=0;k<j;++k)x-=(long double)L[i*n+k]*L[j*n+k];
        if(i==j) { if(!(x>0)||!isfinite(x))return 0;L[i*n+j]=sqrt((double)x); }
        else L[i*n+j]=(double)(x/L[j*n+j]);
    }
    return 1;
}
static void solve_d(unsigned n,const double *L,const double *rhs,double *x)
{
    for(unsigned i=0;i<n;++i) { long double v=rhs[i];for(unsigned k=0;k<i;++k)v-=(long double)L[i*n+k]*x[k];x[i]=(double)(v/L[i*n+i]); }
    for(unsigned i=n;i-- >0;) { long double v=x[i];for(unsigned k=i+1;k<n;++k)v-=(long double)L[k*n+i]*x[k];x[i]=(double)(v/L[i*n+i]); }
}
static double dot_d(unsigned n,const double *a,const double *b)
{ long double sum=0;for(unsigned i=0;i<n;++i)sum+=(long double)a[i]*b[i];return (double)sum; }
static int capture_d(unsigned first,unsigned count,unsigned total,const double *K,const double *response,double *value,unsigned *rank,double *smallest)
{
    double matrix[18*18],eigen[18],work[1024];
    for(unsigned i=0;i<count;++i)for(unsigned j=0;j<count;++j)matrix[i+count*j]=K[(i+first)*total+j+first];
    int n=(int)count,lwork=1024,info=0;dsyev_("V","U",&n,matrix,&n,eigen,work,&lwork,&info);
    if(info||!isfinite(eigen[count-1])||eigen[count-1]<=0)return 0;
    *smallest=eigen[0];*rank=0;*value=0;double tolerance=eigen[count-1]*1e-12;
    if(eigen[0]<-eigen[count-1]*1e-8)return 0;
    for(unsigned j=0;j<count;++j)if(eigen[j]>tolerance) {
        long double reading=0;for(unsigned i=0;i<count;++i)reading+=(long double)matrix[i+count*j]*response[first+i];
        *value+=(double)(reading*reading/eigen[j]);++*rank;
    }
    return isfinite(*value);
}
int native_directional_capture(unsigned first,unsigned last,unsigned base,FILE *out)
{
    if(first<2||last<=first||last>200||base<2||base>10||!out)return 1;
    unsigned n=last-1,old=first-1,spokes=base-1,probes=2*spokes,period=2*base*base*spokes,stride=last+1;
    long double *shorts=calloc((size_t)stride*stride,sizeof *shorts);
    double *G=calloc((size_t)n*n,sizeof *G),*L=calloc((size_t)n*n,sizeof *L),*LN=calloc((size_t)old*old,sizeof *LN);
    double *rhs=calloc((size_t)(probes+1)*n,sizeof *rhs),*fine=calloc((size_t)(probes+1)*n,sizeof *fine),*coarse=calloc((size_t)(probes+1)*old,sizeof *coarse);
    signed char *mask=calloc((size_t)period*spokes,sizeof *mask);
    if(!shorts||!G||!L||!LN||!rhs||!fine||!coarse||!mask) { free(shorts);free(G);free(L);free(LN);free(rhs);free(fine);free(coarse);free(mask);return 1; }
    long double table[201],psi1=psi_d(1);
    for(unsigned d=1;d<=last;++d) {
        for(unsigned r=1;r<d;++r)table[r]=psi_d((long double)r/d);
        for(unsigned a=1;a<d;++a) { long double sum=0;for(unsigned r=1;r<d;++r)sum+=((a*r)%d)*table[r];shorts[d*stride+a]=sum/d; }
    }
    for(unsigned j=2;j<=last;++j)for(unsigned k=2;k<=j;++k) {
        unsigned g=gcd_d(j,k),h=k/g,t=j/g;
        long double inner=(shorts[j*stride+1]+shorts[k*stride+1]-logl(h)*(j-1)/2-logl(t)*(k-1)/2+psi1+logl(g))/g;
        long double value=(shorts[h*stride+t%h]+shorts[t*stride+h%t]+psi1-inner)/(j*k/g);
        G[(j-2)*n+k-2]=G[(k-2)*n+j-2]=(double)value;
    }
    for(unsigned r=0;r<period;++r)for(unsigned s=0;s<spokes;++s)mask[r*spokes+s]=(signed char)((polarity_d(r+s+1,base)-polarity_d(r+s,base))/2);
    for(unsigned j=2;j<=last;++j) {
        unsigned length=period/gcd_d(period,j)*j;long double sums[9]={0},previous=psi_d(1.L/length);
        for(unsigned r=1;r<=length;++r) {
            long double next=psi_d((long double)(r+1)/length),weight=(next-previous)*(r%j)/((long double)length*j);previous=next;
            for(unsigned s=0;s<spokes;++s)sums[s]+=mask[(r%period)*spokes+s]*weight;
        }
        for(unsigned s=0;s<spokes;++s) {
            rhs[s*n+j-2]=(double)sums[s];unsigned address=s+1;rhs[(spokes+s)*n+j-2]=(double)(address%j)/((double)j*address*(address+1));
        }
        rhs[probes*n+j-2]=log((double)j)/j;
    }
    int ok=cholesky(n,G,n,L)&&cholesky(old,G,n,LN);
    if(ok)for(unsigned i=0;i<=probes;++i) { solve_d(n,L,rhs+i*n,fine+i*n);solve_d(old,LN,rhs+i*n,coarse+i*old); }
    double DN=0,DM=0,gain=0,K[18*18],response[18],captures[3],smallest[3];unsigned ranks[3];
    if(ok) {
        DN=1-dot_d(old,rhs+probes*n,coarse+probes*old);DM=1-dot_d(n,rhs+probes*n,fine+probes*n);gain=DN-DM;ok=isfinite(gain)&&gain>0&&DM>0;
        for(unsigned i=0;i<probes;++i) {
            response[i]=dot_d(n,rhs+i*n,fine+probes*n)-dot_d(old,rhs+i*n,coarse+probes*old);
            for(unsigned j=0;j<=i;++j) {
                double left=dot_d(n,rhs+i*n,fine+j*n)-dot_d(old,rhs+i*n,coarse+j*old);
                double right=dot_d(n,rhs+j*n,fine+i*n)-dot_d(old,rhs+j*n,coarse+i*old);
                K[i*probes+j]=K[j*probes+i]=(left+right)/2;
            }
        }
        ok=ok&&capture_d(0,spokes,probes,K,response,captures,ranks,smallest)&&capture_d(spokes,spokes,probes,K,response,captures+1,ranks+1,smallest+1)&&capture_d(0,probes,probes,K,response,captures+2,ranks+2,smallest+2);
        for(unsigned i=0;i<3&&ok;++i)ok=captures[i]>=0&&captures[i]<=gain*(1+1e-6);
    }
    if(ok) {
        fprintf(out,"Complete native directional controls (numerical)\ncoarse_cutoff=%u\nfine_cutoff=%u\nbase=%u\nmask_count=%u\naddress_count=%u\nresidual=%.15g\nfine_residual=%.15g\navailable_gain=%.15g\n",first,last,base,spokes,spokes,DN,DM,gain);
        const char *names[]={"masks","addresses","joint"};
        for(unsigned i=0;i<3;++i)fprintf(out,"%s_capture=%.15g\n%s_fraction=%.15g\n%s_numerical_rank=%u\n%s_smallest_eigenvalue=%.15g\n",names[i],captures[i],names[i],captures[i]/gain,names[i],ranks[i],names[i],smallest[i]);
        fprintf(out,"mask_updated_error=%.15g\n",DN-captures[0]);
        fputs("Complete residue periods and infinite native weights; no address truncation.\nDouble-precision solves, relative pseudoinverse cutoff 1e-12; values and ranks are numerical, not interval-certified.\n",out);
    } else fputs("Directional controls could not resolve the requested numerical projection.\n",stderr);
    free(shorts);free(G);free(L);free(LN);free(rhs);free(fine);free(coarse);free(mask);return !ok;
}
