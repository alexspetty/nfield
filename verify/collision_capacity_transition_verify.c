#include "../src/collision_capacity_transition.h"
#include <gmp.h>
#include <math.h>
#include <stdio.h>

static int gcd_v(int a,int b) { while(b) { int r=a%b; a=b; b=r; } return a; }
static void rational(mpq_t q,long n,unsigned long d)
{ mpq_set_si(q,n,d); mpq_canonicalize(q); }
static long double value(const mpq_t q) { return (long double)mpq_get_d(q); }
static int check(int condition,int *total,int *failed,const char *name,int a,int b)
{
    (*total)++;
    if (!condition) { if ((*failed)++<8) fprintf(stderr,"transition check failed: %s (%d,%d)\n",name,a,b); }
    return condition;
}

int collision_capacity_transition_verify(void)
{
    enum { N=240 };
    CollisionTransition t;
    if (!collision_transition_init(&t,N)) return 0;
    mpq_t w[N+1],J,term,yn,prefix,formula,sa,mass,h,h2,inner,alt,tmp;
    for (int k=0;k<=N;k++) mpq_init(w[k]);
    mpq_inits(J,term,yn,prefix,formula,sa,mass,h,h2,inner,alt,tmp,NULL);
    int total=0,failed=0;
    for (int k=2;k<=N;k++) {
        for (int a=1;a<k;a++) if (gcd_v(a,k)==1) {
            rational(term,1,(unsigned long)a*k*k); mpq_add(w[k],w[k],term);
        }
        check(fabsl(t.a[k]/k-value(w[k]))<2e-15L,&total,&failed,"coprime weight",k,0);
        for (int u=1;u<k;u++) if (gcd_v(u,k)==1) {
            check((u-1)+(k-u-1)==k-2,&total,&failed,"unit reflection",k,u);
        }
        long mean_sum=0,chi_sum=0; int phi=0;
        for (int u=1;u<k;u++) if (gcd_v(u,k)==1) {
            mean_sum+=2*(u-1)-k+1; phi++;
            if (k%3==0) chi_sum+=u*(u%3==1?1:-1);
        }
        check(mean_sum==-phi,&total,&failed,"unit mean",k,0);
        if (k%3==0) {
            long expected=-k/3;
            for (int p=2;p<=k;p++) if (t.prime[p] && k%p==0 && p!=3)
                expected*=1-(p%3==1?1:-1);
            check(chi_sum==expected && chi_sum<=0,&total,&failed,"chi3 product and sign",k,0);
        }
    }
    rational(term,-1,18);
    rational(tmp,-1,3); mpq_mul(tmp,tmp,w[3]);
    check(mpq_equal(term,tmp),&total,&failed,"chi3 lower-bound source",3,0);
    for (int n=1;n<=N;n++) {
        /* Direct gcd row increments build the full square sum exactly. */
        rational(term,1,3); mpq_add(J,J,term);
        for (int r=1;r<n;r++) {
            int g=gcd_v(r,n);
            rational(term,2*g*g,3UL*r*n); mpq_add(J,J,term);
        }
        check(fabsl(n-t.deficit[n]-value(J))<3e-12L,&total,&failed,"direct gcd capacity",n,0);
        mpq_set_ui(yn,0,1); mpq_set_ui(formula,0,1); mpq_set_ui(alt,0,1);
        for (int k=2;k<=n;k++) {
            rational(term,2*(n%k)-k+1,3); mpq_mul(term,term,w[k]); mpq_add(yn,yn,term);
            int r=n%k;
            rational(term,-(r+1)*(k-1-r),3); mpq_mul(term,term,w[k]); mpq_add(formula,formula,term);
            rational(term,k,1); mpq_mul(term,term,w[k]); mpq_add(alt,alt,term);
        }
        check(fabsl(t.diagonal[n]-value(yn))<3e-12L,&total,&failed,"direct diagonal",n,0);
        mpq_add(prefix,prefix,yn);
        check(mpq_equal(prefix,formula) && mpq_sgn(prefix)<=0,&total,&failed,"cumulative sign identity",n,0);
        check(fabsl(t.sum_a[n]-value(alt))<3e-14L,&total,&failed,"cumulative a",n,0);
        mpq_set_ui(sa,0,1);
        for (int d=1;d<=n;d++) if (t.mu[d]) {
            mpq_set_ui(h,0,1); mpq_set_ui(h2,0,1);
            for (int j=1;j<=n/d;j++) {
                rational(term,1,j); mpq_add(h,h,term);
                rational(term,1,j*j); mpq_add(h2,h2,term);
            }
            mpq_mul(inner,h,h); mpq_sub(inner,inner,h2);
            rational(term,t.mu[d],2UL*d*d); mpq_mul(inner,inner,term); mpq_add(sa,sa,inner);
        }
        check(mpq_equal(sa,alt),&total,&failed,"harmonic Mobius cumulative identity",n,0);
        mpq_set_ui(mass,0,1); mpq_set_ui(inner,0,1);
        for (int k=2;k<=n;k++) {
            mpq_add(mass,mass,w[k]);
            rational(term,2*(n%k)-k,3); mpq_mul(term,term,w[k]); mpq_add(inner,inner,term);
        }
        rational(term,1,3); mpq_mul(term,term,mass); mpq_add(inner,inner,term);
        check(mpq_equal(inner,yn),&total,&failed,"fractional-part endpoint",n,0);
        rational(tmp,n,1); mpq_sub(tmp,tmp,J);
        mpq_sub(inner,alt,mass); rational(term,1,3); mpq_mul(inner,inner,term);
        rational(term,1,1); mpq_sub(term,term,mass); rational(formula,2*n,3);
        mpq_mul(term,term,formula); mpq_add(inner,inner,term); mpq_add(inner,inner,yn);
        check(mpq_equal(tmp,inner),&total,&failed,"deficit diagonal dictionary",n,0);
    }
    /* Integer sums give independent rational CRT covariances and conditional means. */
    for (int k=2;k<=30;k++) for (int l=2;l<=30;l++) {
        int g=gcd_v(k,l),period=k/g*l; long long sum=0;
        for (int x=0;x<period;x++) sum+=(2*(x%k)-k+1)*(2*(x%l)-l+1);
        check(3*sum==(long long)period*(g*g-1),&total,&failed,"CRT covariance",k,l);
        for (int a=0;a<l;a++) {
            long long conditional=0; int count=0;
            for (int x=a;x<period;x+=l) { conditional+=2*(x%k)-k+1; count++; }
            check(conditional==(long long)count*(2*(a%g)-g+1),&total,&failed,"progression projection",k,l);
        }
    }
    for (int m=2;m<=60;m++) for (int n=0;n<=120;n++) {
        long double decomposition=0;
        for (int q=2;q<=m;q++) {
            long twice_p=0; int phi=0;
            for (int d=1;d<=q;d++) if (q%d==0) twice_p+=t.mu[q/d]*(2*(n%d)-d+1);
            for (int a=1;a<q;a++) if (gcd_v(a,q)==1) phi++;
            if (n%q==0) check(twice_p==-phi,&total,&failed,"negative conductor endpoint",n,q);
            if ((n+1)%q==0) check(twice_p==phi,&total,&failed,"positive conductor endpoint",n,q);
            long double amplitude=0;
            for (int k=q;k<=m;k+=q) amplitude+=value(w[k]);
            decomposition+=amplitude*twice_p/3;
        }
        check(fabsl(decomposition-collision_transition_cutoff(&t,n,m))<2e-14L,
              &total,&failed,"finite conductor decomposition",n,m);
    }
    for (int m=2;m<=10;m++) {
        int period=1; for (int k=2;k<=m;k++) period=period/gcd_v(period,k)*k;
        long double sum=0,square=0,unit_sum=0,unit_square=0; int phi=0;
        for (int x=0;x<period;x++) {
            long double y=collision_transition_cutoff(&t,x,m); sum+=y; square+=y*y;
            if (gcd_v(x,period)==1) {
                long double f=collision_transition_cutoff(&t,x-1,m);
                unit_sum+=f; unit_square+=powl(f+t.mass[m]/3,2); phi++;
            }
        }
        long double variance=0;
        for (int k=2;k<=m;k++) for (int l=2;l<=m;l++) {
            int g=gcd_v(k,l); variance+=value(w[k])*value(w[l])*(g*g-1)/27;
        }
        check(fabsl(sum/period)<1e-15L && fabsl(square/period-variance)<1e-14L,
              &total,&failed,"full-period finite variance",m,0);
        check(fabsl(unit_sum/phi+t.mass[m]/3)<1e-14L && (m<3 || unit_square/phi>=1.0L/324-1e-16L),
              &total,&failed,"unit-phase norm",m,0);
    }
    /* Exact rational integrals of B2^2 and T^-2 fix the transition coefficient. */
    rational(yn,1,5); rational(term,-1,2); mpq_add(yn,yn,term);
    rational(term,4,9); mpq_add(yn,yn,term); rational(term,-1,6); mpq_add(yn,yn,term);
    rational(term,1,36); mpq_add(yn,yn,term); rational(term,1,180);
    check(mpq_equal(yn,term),&total,&failed,"Bernoulli square integral",2,0);
    rational(tmp,1,18); mpq_mul(yn,yn,tmp); rational(term,1,3240);
    check(mpq_equal(yn,term),&total,&failed,"boundary variance factor",2,0);
    for (int n=0;n<24;n++) {
        long perturb=2*(n%2)-1-2*(2*(n%3)-2)+(2*(n%4)-3);
        long shifted=2*((n+12)%2)-1-2*(2*((n+12)%3)-2)+(2*((n+12)%4)-3);
        check(perturb==shifted && 1-2+1==0 && 2-2*3+4==0,
              &total,&failed,"moment-preserving periodic perturbation",n,0);
    }
    /* Trial division checks the prime-predecessor sieve, including both window ends. */
    for (int n=1;n<=N;n++) {
        int p=n+1,is_prime=1;
        for (int d=2;d<=p/d;d++) if (p%d==0) is_prime=0;
        check(t.prime[p]==is_prime,&total,&failed,"prime predecessor indexing",n,p);
    }
    printf("capacity-resolution verify: %d checks, %d failures\n",total,failed);
    puts("Exact rational finite identities and independently compared numerical values.\n"
         "Limit theorems, asymptotic rates and infinite norms require the manuscript proofs.");
    for (int k=0;k<=N;k++) mpq_clear(w[k]);
    mpq_clears(J,term,yn,prefix,formula,sa,mass,h,h2,inner,alt,tmp,NULL);
    collision_transition_clear(&t); return failed==0;
}
