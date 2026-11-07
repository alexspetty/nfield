#include "collision_capacity_transition.h"
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Rounded from zeta-derivative formulas evaluated at 80-digit precision.
 * These constants are numerical approximations. */
static const long double ALPHA = 0.6079271018540266286632767792583658334262L;
static const long double BETA = 0.6973997810101360840584026216412933419767L;
static const long double CA = -0.3688298639487917399892080502961228762403L;
static const long double DRIFT_B = -0.03285297505394647442498403842308841072276L;
static const long double DRIFT_C = -0.03640007885475813429186624869533144894394L;
static const long double CAP_B = 0.6048983531854499727033346882962532588869L;
static const long double CAP_C = 0.3775412217384197608595173351390670425779L;
enum { MAX_RESOLUTION = 2000000, MAX_SAMPLES = 5000 };

static int gcd_int(int a, int b) { while (b) { int r=a%b; a=b; b=r; } return a; }
static long double b2(long double u) { return u*u-u+1.0L/6; }

void collision_transition_clear(CollisionTransition *t)
{
    if (!t) return;
    free(t->mu); free(t->prime); free(t->a); free(t->mass);
    free(t->sum_a); free(t->deficit); free(t->diagonal);
    memset(t,0,sizeof(*t));
}

int collision_transition_init(CollisionTransition *t, int limit)
{
    if (!t) return 0;
    memset(t,0,sizeof(*t));
    if (limit<1 || limit>MAX_RESOLUTION) return 0;
    size_t size=(size_t)limit+2;
    t->limit=limit;
    t->mu=calloc(size,sizeof(int)); t->prime=calloc(size,1);
    t->a=calloc(size,sizeof(long double)); t->mass=calloc(size,sizeof(long double));
    t->sum_a=calloc(size,sizeof(long double)); t->deficit=calloc(size,sizeof(long double));
    t->diagonal=calloc(size,sizeof(long double));
    long double *reset=calloc(size,sizeof(long double));
    if (!t->mu || !t->prime || !t->a || !t->mass || !t->sum_a ||
        !t->deficit || !t->diagonal || !reset) {
        free(reset); collision_transition_clear(t); return 0;
    }
    /* One extra sieve point is needed for the event that n+1 is prime. */
    for (int n=1;n<=limit+1;n++) { t->mu[n]=1; t->prime[n]=(n>=2); }
    for (int p=2;p<=limit+1;p++) if (t->prime[p]) {
        for (int j=p;j<=limit+1;j+=p) t->mu[j]=-t->mu[j];
        for (int j=2*p;j<=limit+1;j+=p) t->prime[j]=0;
        if (p<=(limit+1)/p)
            for (int j=p*p;j<=limit+1;j+=p*p) t->mu[j]=0;
    }
    /* Temporarily use the deficit array for ordinary harmonic numbers. */
    for (int j=1;j<=limit;j++) t->deficit[j]=t->deficit[j-1]+1.0L/j;
    for (int d=1;d<=limit/2;d++) if (t->mu[d]) {
        long double scale=(long double)t->mu[d]/((long double)d*d);
        for (int j=2;j<=limit/d;j++)
            t->a[d*j]+=scale*t->deficit[j-1]/j;
    }
    for (int k=2;k<=limit;k++)
        for (int n=k;n<=limit;n+=k) reset[n]+=t->a[k];
    t->deficit[0]=0;
    for (int n=1;n<=limit;n++) {
        t->mass[n]=t->mass[n-1]+t->a[n]/n;
        t->sum_a[n]=t->sum_a[n-1]+t->a[n];
        t->deficit[n]=t->deficit[n-1]+2.0L/3*(1-reset[n]);
        t->diagonal[n]=t->deficit[n]-(t->sum_a[n]-t->mass[n])/3
                        -2.0L/3*n*(1-t->mass[n]);
    }
    free(reset); return 1;
}

long double collision_transition_cutoff(const CollisionTransition *t, int n, int m)
{
    if (!t || n<0 || m<1 || m>t->limit) return NAN;
    long double value=0;
    for (int k=2;k<=m;k++) value+=t->a[k]/k*(2.0L*(n%k)-k+1)/3;
    return value;
}

long double collision_transition_centered(const CollisionTransition *t, int n)
{ return !t || n<1 || n>t->limit ? NAN : t->diagonal[n]-DRIFT_B*logl(n)-DRIFT_C; }

long double collision_transition_residual(const CollisionTransition *t, int n)
{
    if (!t || n<1 || n>t->limit) return NAN;
    long double l=logl(n);
    return t->deficit[n]-ALPHA*l*l/6-CAP_B*l-CAP_C;
}

static long double primitive_row_twice(const CollisionTransition *t, int q, int n)
{
    long double sum=0;
    for (int d=1;d<=q;d++) if (q%d==0)
        sum+=t->mu[q/d]*(2.0L*(n%d)-d+1);
    return sum;
}

static long double eta(const CollisionTransition *t, int q, int m)
{
    long double sum=0;
    for (int k=q;k<=m;k+=q) sum+=t->a[k]/k;
    return sum;
}

static int integer(const char *s, int low, int high, int *out)
{
    char *end=NULL; errno=0; long value=strtol(s,&end,10);
    if (errno || !*s || *end || value<low || value>high) return 0;
    *out=(int)value; return 1;
}

void collision_capacity_transition_help(void)
{
    puts("capacity-resolution\n"
         "  constants                         centering constants from zeta derivatives\n"
         "  inspect n [M]                     capacity, diagonal, residual, cutoff boundary\n"
         "  window X                          moments on X < n <= 2X and prime predecessors\n"
         "  sample X M count                  CSV across that window, including B2 correction\n"
         "  unit M                            finite unit-phase mean, variance and chi_3 moment\n"
         "  spectrum n M                      finite conductor and endpoint decomposition\n"
         "  progression X L a                 conditional mean on n = a modulo L\n"
         "  verify                            independent finite identity checks\n"
         "  n <= 2000000; X <= 1000000; unit M <= 60; spectrum M <= 2000.\n"
         "  sample count <= 5000 and M*count <= 100000000.\n"
         "  Long-double finite evaluations are numerical, not infinite-limit certificates.\n"
         "  Prime observations use continuous capacity at p-1, not finite digit-grid energy.");
}

static void constants(void)
{
    puts("name,value");
    printf("alpha,%.21Lg\nbeta,%.21Lg\nCa,%.21Lg\nb,%.21Lg\nc,%.21Lg\nB,%.21Lg\nC,%.21Lg\n",
           ALPHA,BETA,CA,DRIFT_B,DRIFT_C,CAP_B,CAP_C);
}

static void inspect(const CollisionTransition *t, int n, int m)
{
    long double z=collision_transition_centered(t,n), y=collision_transition_cutoff(t,n,m);
    long double boundary=(ALPHA*logl(m)+BETA)*m/(3*n)*b2((long double)(n%m)/m);
    puts("n,M,J,D,y,Z,R,Y_M,Z_minus_Y_M,B2_correction,corrected_difference");
    printf("%d,%d,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg\n",
           n,m,n-t->deficit[n],t->deficit[n],t->diagonal[n],z,
           collision_transition_residual(t,n),y,z-y,boundary,z-y-boundary);
}

static void window(const CollisionTransition *t, int x)
{
    long double totals[2][5]={{0}}; int count[2]={0};
    for (int n=x+1;n<=2*x;n++) {
        long double z=collision_transition_centered(t,n), r=collision_transition_residual(t,n);
        for (int sector=0;sector<2;sector++) if (!sector || t->prime[n+1]) {
            count[sector]++; totals[sector][0]+=t->diagonal[n]; totals[sector][1]+=z;
            totals[sector][2]+=z*z; totals[sector][3]+=r; totals[sector][4]+=r*r;
        }
    }
    puts("sector,X,count,mean_y,mean_Z,second_Z,mean_R,second_R,variance_Z");
    for (int s=0;s<2;s++) if (count[s]) {
        printf("%s,%d,%d",s?"prime_predecessors":"integers",x,count[s]);
        for (int j=0;j<5;j++) printf(",%.18Lg",totals[s][j]/count[s]);
        printf(",%.18Lg\n",totals[s][2]/count[s]-powl(totals[s][1]/count[s],2));
    }
}

static void sample(const CollisionTransition *t, int x, int m, int count)
{
    puts("n,phase,y,Z,R,Y_M,B2_correction,corrected_difference,prime_predecessor");
    for (int i=0;i<count;i++) {
        int n=x+1+(int)((long long)i*(x-1)/(count-1));
        long double phase=(long double)(n%m)/m, z=collision_transition_centered(t,n);
        long double ym=collision_transition_cutoff(t,n,m);
        long double boundary=(ALPHA*logl(m)+BETA)*m/(3*n)*b2(phase);
        printf("%d,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%d\n",n,phase,
               t->diagonal[n],z,collision_transition_residual(t,n),ym,boundary,z-ym-boundary,t->prime[n+1]);
    }
}

static void unit(const CollisionTransition *t, int m)
{
    long double variance=0, moment=0, haar=0;
    for (int k=2;k<=m;k++) {
        if (k%3==0) {
            long double sum=0; int phi=0;
            for (int u=1;u<k;u++) if (gcd_int(u,k)==1) {
                sum+=u*(u%3==1?1:-1); phi++;
            }
            moment+=2*t->a[k]/k*sum/(3*phi);
        }
        for (int l=2;l<=m;l++) {
            int g=gcd_int(k,l), period=k/g*l, phi=0;
            long double sum=0;
            for (int u=1;u<period;u++) if (gcd_int(u,period)==1) {
                sum+=(2.0L*(u%k)-k)*(2.0L*(u%l)-l); phi++;
            }
            variance+=t->a[k]/k*t->a[l]/l*sum/(9*phi);
            haar+=t->a[k]/k*t->a[l]/l*((long double)g*g-1)/27;
        }
    }
    puts("M,mass,unit_mean,unit_variance,chi3_moment,haar_variance");
    printf("%d,%.18Lg,%.18Lg,%.18Lg,%.18Lg,%.18Lg\n",m,t->mass[m],-t->mass[m]/3,variance,moment,haar);
}

static void spectrum(const CollisionTransition *t, int n, int m)
{
    puts("q,eta_q_M,P_q,contribution,endpoint");
    for (int q=2;q<=m;q++) {
        long double p=primitive_row_twice(t,q,n)/2, e=eta(t,q,m);
        printf("%d,%.18Lg,%.18Lg,%.18Lg,%s\n",q,e,p,2*e*p/3,
               n%q==0?"negative":(n+1)%q==0?"positive":"interior");
    }
}

static void progression(const CollisionTransition *t, int x, int l, int address)
{
    long double observed=0, conditional=0; int count=0;
    for (int n=x+1;n<=2*x;n++) if (n%l==address) {
        observed+=collision_transition_residual(t,n); count++;
    }
    for (int k=2;k<=t->limit;k++) {
        int g=gcd_int(k,l);
        conditional+=t->a[k]/k*(2.0L*(address%g)-g+1)/3;
    }
    /* w_k <= H_{k-1}/k^2; integral comparison bounds the omitted mean. */
    long double tail=(l-1.0L)*(logl(t->limit)+2)/(3*t->limit);
    puts("X,L,address,count,observed_mean_R,truncated_conditional_mean,conditional_tail_majorant");
    printf("%d,%d,%d,%d,%.18Lg,%.18Lg,%.18Lg\n",x,l,address,count,observed/count,conditional,tail);
}

int collision_capacity_transition_command(int argc, char **argv)
{
    if (!argc || (argc==1 && (!strcmp(argv[0],"help") || !strcmp(argv[0],"--help")))) {
        collision_capacity_transition_help(); return 0;
    }
    const char *action=argv[0]; int n=0,m=0,count=0,l=0,address=0,limit=0;
    if (!strcmp(action,"verify") && argc==1) return collision_capacity_transition_verify()?0:1;
    if (!strcmp(action,"constants") && argc==1) { constants(); return 0; }
    if (!strcmp(action,"inspect") && (argc==2 || argc==3)) {
        if (!integer(argv[1],1,MAX_RESOLUTION,&n)) goto invalid;
        m=n; if (argc==3 && !integer(argv[2],1,MAX_RESOLUTION,&m)) goto invalid;
        limit=n>m?n:m;
    } else if (!strcmp(action,"window") && argc==2) {
        if (!integer(argv[1],2,MAX_RESOLUTION/2,&n)) goto invalid;
        limit=2*n;
    } else if (!strcmp(action,"sample") && argc==4) {
        if (!integer(argv[1],2,MAX_RESOLUTION/2,&n) || !integer(argv[2],2,2*n,&m) ||
            !integer(argv[3],2,n<MAX_SAMPLES?n:MAX_SAMPLES,&count) ||
            (long long)m*count>100000000) goto invalid;
        limit=2*n;
    } else if (!strcmp(action,"unit") && argc==2) {
        if (!integer(argv[1],2,60,&m)) goto invalid;
        limit=m;
    } else if (!strcmp(action,"spectrum") && argc==3) {
        if (!integer(argv[1],0,MAX_RESOLUTION,&n) || !integer(argv[2],2,2000,&m)) goto invalid;
        limit=m;
    } else if (!strcmp(action,"progression") && argc==4) {
        if (!integer(argv[1],2,MAX_RESOLUTION/2,&n) || !integer(argv[2],1,(int)sqrt(n),&l) ||
            !integer(argv[3],0,l-1,&address)) goto invalid;
        limit=2*n;
    } else goto invalid;
    CollisionTransition t;
    if (!collision_transition_init(&t,limit)) { fputs("Could not allocate transition calculation.\n",stderr); return 1; }
    if (!strcmp(action,"inspect")) inspect(&t,n,m);
    else if (!strcmp(action,"window")) window(&t,n);
    else if (!strcmp(action,"sample")) sample(&t,n,m,count);
    else if (!strcmp(action,"unit")) unit(&t,m);
    else if (!strcmp(action,"spectrum")) spectrum(&t,n,m);
    else progression(&t,n,l,address);
    collision_transition_clear(&t); return 0;
invalid:
    fputs("Invalid capacity-resolution arguments. See focused help.\n",stderr);
    return 1;
}
