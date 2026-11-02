/* Signed count sources, shifted grids and stopped reciprocity. All arithmetic
 * here is exact. Finite readings do not certify uniform discrepancy bounds. */
static long cs_mod(long n,long k) { long r=n%k;return r<0?r+k:r; }
static long cs_delta(long Q,unsigned k,unsigned L)
{ unsigned a=(unsigned)cs_mod(Q,k),r=L%k;return a?(long)(a<=r)-(long)(k-a<=r):0; }
static long cs_source(unsigned N,unsigned k,long Q)
{ long v=0;for(unsigned r=1;r<=N/k;++r)v+=cs_delta(Q,k,N/r);return v; }
static void cs_reciprocity(mpq_t out,unsigned a,unsigned b)
{ cs_fraction(out,(long)a*a+(long)b*b+1-3L*a*b,12UL*a*b); }
static unsigned cs_nearest(unsigned a,unsigned b,int *orientation,unsigned *digit)
{
    unsigned r=a%b;*orientation=1;*digit=a/b;
    if(2*r>b) { r=b-r;*orientation=-1;++*digit; }
    return r;
}
static unsigned cs_stopped(mpq_t cost,mpq_t terminal,unsigned k,unsigned c,unsigned H,int report)
{
    unsigned a=k,b=c,steps=0;int delta=1;
    mpq_t term;mpq_init(term);mpq_set_ui(cost,0,1);
    for(;;) {
        int sign;unsigned digit,e=cs_nearest(a,b,&sign,&digit);
        if(!e || 2*e==b || e<=H) break;
        delta=-sign*delta;cs_reciprocity(term,e,b);cs_scale(term,term,-delta,1);mpq_add(cost,cost,term);
        if(report)printf("step=%u upper=%u lower=%u digit=%u orientation=%d next=%u determinant=%d\n",steps,a,b,digit,sign,e,delta);
        a=b;b=e;++steps;
    }
    collision_sampling_dedekind_q(terminal,b,a);cs_scale(terminal,terminal,delta,1);
    if(report)printf("steps=%u terminal_upper=%u terminal_lower=%u terminal_orientation=%d\n",steps,a,b,delta);
    mpq_clear(term);return steps;
}
static int cs_signed(const char *s,long *v)
{
    if(!s || !*s)return 0;
    const char *p=s;if(*p=='-')++p;if(!*p)return 0;
    for(;*p;++p)if(*p<'0'||*p>'9')return 0;
    errno=0;char *end;long n=strtol(s,&end,10);if(errno||*end||n< -1000000||n>1000000)return 0;*v=n;return 1;
}
static int cs_shift(const char *s,long *num,long *den)
{
    const char *slash=strchr(s,'/');char a[32],b[32];size_t size=slash?(size_t)(slash-s):strlen(s);
    if(!size||size>=sizeof a)return 0;
    memcpy(a,s,size);a[size]=0;
    if(slash) { if(strlen(slash+1)>=sizeof b)return 0;strcpy(b,slash+1); } else strcpy(b,"1");
    return cs_signed(a,num)&&cs_signed(b,den)&&*den>=1&&*den<=10000&&*num>=0&&*num<*den;
}
static int cs_golden(long A,long B)
{ return B>0? A*A-A*B-B*B>0 : B<0&&-2*B<A&&A*A+3*A*B+B*B>0; }
static int cs_prefix_row(unsigned A,long B,long *C,long *E,int *det)
{
    if(A<2||A>512||labs(B)>=A||!B||cs_gcd(A,(unsigned)labs(B))!=1||!cs_golden(A,B))return 0;
    if(labs(B)==1) { *C=1;*E=0;*det=-(int)B;return 1; }
    unsigned b=cs_inverse((unsigned)cs_mod(B,A),A);*C=b<A-b?b:A-b;*det=2*b<A?-1:1;*E=(*det+B**C)/(long)A;return 1;
}
static int cs_grid(unsigned N,unsigned q,long tn,long td)
{
    if(N<1||N>120||q<1||q>10000)return 1;
    mpq_t J,sample,defect,point,jump,curve,U,saw,B2,t,v,error;
    mpq_inits(J,sample,defect,point,jump,curve,U,saw,B2,t,v,error,NULL);
    collision_sampling_capacity_q(J,N);
    mpz_t total,z;mpz_inits(total,z,NULL);long modulus=(long)q*td;
    for(unsigned a=0;a<q;++a) {
        long sum=0;for(unsigned j=1;j<=N;++j) { long r=((long)j*((long)a*td+tn))%modulus;if(r)sum+=2*r-modulus; }
        mpz_set_si(z,sum);mpz_addmul(total,z,z);
    }
    mpq_set_z(sample,total);mpz_set_ui(mpq_denref(sample),(unsigned long)modulus);mpz_mul(mpq_denref(sample),mpq_denref(sample),mpq_denref(sample));mpz_mul_ui(mpq_denref(sample),mpq_denref(sample),q);mpq_canonicalize(sample);
    mpq_sub(defect,J,sample);
    /* k=1,a=0 is the origin; the other reduced fractions are counted once. */
    for(unsigned k=1;k<=N;++k)for(unsigned a=0;a<k;++a)if(cs_gcd(a,k)==1) {
        unsigned C=N/k;long den=(long)k*td,r=cs_mod((long)q*a*td-tn*k,den);
        if(!r) { cs_fraction(t,(long)C*C,q);mpq_add(point,point,t); }
        mpq_set_ui(U,0,1);
        for(unsigned j=1;j<=N;++j) { cs_saw(t,(j*a)%k,k);mpq_add(U,U,t); }
        cs_scale(U,U,2,1);cs_fraction(saw,r?2*r-den:0,2UL*den);
        mpq_mul(t,U,saw);cs_scale(t,t,4L*C,q);mpq_add(jump,jump,t);
        cs_fraction(B2,r,den);mpq_mul(t,B2,B2);mpq_sub(B2,t,B2);cs_fraction(t,1,6);mpq_add(B2,B2,t);
        cs_scale(t,B2,-2L*N*(N+1)*C,(unsigned long)q*q);mpq_add(curve,curve,t);
    }
    mpq_add(error,point,jump);mpq_add(error,error,curve);mpq_sub(error,error,defect);
    int failed=mpq_sgn(error)!=0;
    if(!failed) { cs_print("capacity",J);cs_print("sampled",sample);cs_print("defect",defect);cs_print("point",point);cs_print("jump",jump);cs_print("curvature",curve);cs_print("identity_error",error); }
    else fputs("shifted sampling identity failed\n",stderr);
    mpz_clears(total,z,NULL);mpq_clears(J,sample,defect,point,jump,curve,U,saw,B2,t,v,error,NULL);return failed;
}
static int cs_decomposition(unsigned p,unsigned H)
{
    if(!cs_prime(p)||!H||H>=p)return 1;
    enum {A,L,E,C,K,T,COUNT};mpq_t sums[COUNT],s,r,cost,terminal,t,error;
    for(unsigned i=0;i<COUNT;++i)mpq_init(sums[i]);
    mpq_inits(s,r,cost,terminal,t,error,NULL);
    unsigned N=p-1;long q=(long)p*p;
    for(unsigned k=2;k<=N;++k)for(unsigned c=1;2*c<k;++c)if(cs_gcd(c,k)==1) {
        long weight=2*cs_source(N,k,q*cs_inverse(c,k));collision_sampling_dedekind_q(s,k,c);
        cs_scale(t,s,weight,1);mpq_add(sums[A],sums[A],t);
        if(c<=H) { mpq_add(sums[L],sums[L],t);continue; }
        cs_reciprocity(r,c,k);cs_scale(t,r,weight,1);mpq_add(sums[E],sums[E],t);
        int sign;unsigned digit,d=cs_nearest(k,c,&sign,&digit);
        if(d<=H || 2*d==c) { collision_sampling_dedekind_q(s,c,k);cs_scale(t,s,-weight,1);mpq_add(sums[C],sums[C],t); }
        else { cs_stopped(cost,terminal,k,c,H,0);cs_scale(t,cost,-weight,1);mpq_add(sums[K],sums[K],t);cs_scale(t,terminal,-weight,1);mpq_add(sums[T],sums[T],t); }
    }
    for(unsigned i=1;i<COUNT;++i)mpq_add(error,error,sums[i]);
    mpq_sub(error,error,sums[A]);
    const char *names[]={"source_sum","small_pairs","first_cost","small_remainders","stopped_cost","terminal"};
    int failed=mpq_sgn(error)!=0;
    if(!failed) { for(unsigned i=0;i<COUNT;++i)cs_print(names[i],sums[i]);cs_print("identity_error",error);puts("All source signs and multiplicities are retained. This finite split does not certify an asymptotic rate."); }
    for(unsigned i=0;i<COUNT;++i)mpq_clear(sums[i]);
    mpq_clears(s,r,cost,terminal,t,error,NULL);return failed;
}
static int cs_rational(const char *s,mpq_t q)
{
    if(!s||!*s||strlen(s)>160)return 0;
    const char *p=s;if(*p=='-')++p;int digits=0,slash=0;
    for(;*p;++p) { if(*p>='0'&&*p<='9') { ++digits;continue; }if(*p=='/'&&digits&&!slash) { slash=1;digits=0;continue; }return 0; }
    if(!digits||mpq_set_str(q,s,10)||mpz_sgn(mpq_denref(q))<=0)return 0;
    if(mpz_sizeinbase(mpq_numref(q),2)>256||mpz_sizeinbase(mpq_denref(q),2)>256)return 0;
    mpq_canonicalize(q);return 1;
}
static int cs_phase_sum(int argc,char **argv)
{
    if(argc!=6)return 1;
    unsigned first,last;
    if(!cs_uint(argv[4],&first)||!cs_uint(argv[5],&last)||first<2||last<first||last>512)return 1;
    mpq_t gamma,X,beta,sum,arg,t,lo,hi,power;mpq_inits(gamma,X,beta,sum,arg,t,lo,hi,power,NULL);
    int ok=cs_rational(argv[1],gamma)&&cs_rational(argv[2],X)&&cs_rational(argv[3],beta);
    cs_fraction(t,first,1);mpq_add(lo,t,beta);if(mpq_sgn(lo)<=0)ok=0;
    mpz_t floor;mpz_init(floor);
    if(ok) {
        for(unsigned n=first;n<=last;++n) { cs_fraction(t,n,1);mpq_add(t,t,beta);mpq_div(arg,X,t);mpq_add(arg,arg,gamma);mpz_fdiv_q(floor,mpq_numref(arg),mpq_denref(arg));mpq_set_z(t,floor);mpq_sub(arg,arg,t);cs_fraction(t,1,2);mpq_sub(arg,arg,t);mpq_add(sum,sum,arg); }
        cs_print("literal_sawtooth_sum",sum);cs_fraction(t,last,1);mpq_add(hi,t,beta);mpq_abs(X,X);unsigned long factorial=1;
        for(unsigned j=1;j<=14;++j) {
            factorial*=j;if(j<2)continue;mpq_set(power,hi);for(unsigned k=0;k<j;++k)mpq_mul(power,power,hi);mpq_div(arg,X,power);cs_scale(arg,arg,(long)factorial,1);
            printf("derivative_order=%u\n",j);cs_print("absolute_derivative_lower",arg);
            mpq_set(power,lo);for(unsigned k=0;k<j;++k)mpq_mul(power,power,lo);mpq_div(arg,X,power);cs_scale(arg,arg,(long)factorial,1);cs_print("absolute_derivative_upper",arg);
        }
        puts("Integer phases use b(integer)=-1/2. Finite derivative ranges do not establish a uniform exponential-sum bound.");
    }
    mpz_clear(floor);mpq_clears(gamma,X,beta,sum,arg,t,lo,hi,power,NULL);return !ok;
}
static int cs_kernel_q(mpq_t out,unsigned Q,unsigned a,unsigned b)
{
    if(!a||!b||a>512||b>512||!Q||Q>1000000||cs_gcd(Q,a)!=1||cs_gcd(Q,b)!=1)return 0;
    mpq_t x,y;mpq_inits(x,y,NULL);collision_sampling_dedekind_q(x,b,(unsigned long long)a*cs_inverse(Q,b));
    collision_sampling_dedekind_q(y,a,(unsigned long long)b*cs_inverse(Q,a));mpq_add(out,x,y);mpq_clears(x,y,NULL);return 1;
}
static int cs_arithmetic_shells(unsigned Q,unsigned N)
{
    if(Q<1||Q>1000000||N<1||N>120)return 1;
    for(unsigned j=1;j<=N;++j)if(cs_gcd(Q,j)!=1)return 1;
    mpq_t P[121],prefix[121],logs[121],x,y;for(unsigned i=0;i<=120;++i) { mpq_init(P[i]);mpq_init(prefix[i]);mpq_init(logs[i]); }mpq_inits(x,y,NULL);
    for(unsigned m=2;m<=N;++m)for(unsigned k=1;k<m;++k)if(cs_gcd(k,m)==1) { cs_kernel_q(x,Q,k,m);cs_scale(x,x,2,1);mpq_add(P[m],P[m],x); }
    for(unsigned n=1;n<=N;++n)for(unsigned m=1;m<=n;++m) { cs_scale(x,P[m],n/m,1);mpq_add(prefix[n],prefix[n],x); }
    for(unsigned p=2;p<=N;++p) {
        int prime=1;for(unsigned d=2;d<=p/d;++d)if(p%d==0)prime=0;if(!prime)continue;
        for(unsigned m=1;m<=N;++m)for(unsigned power=p;power<=N/m;power*=p)mpq_add(logs[p],logs[p],P[m]);
    }
    for(unsigned m=1;m<=N;++m)gmp_printf("cutoff=%u primitive_shell=%Qd square_prefix=%Qd\n",m,P[m],prefix[m]);
    for(unsigned p=2;p<=N;++p)if(mpq_sgn(logs[p]))gmp_printf("log_prime=%u coefficient=%Qd\n",p,logs[p]);
    for(unsigned i=0;i<=120;++i) { mpq_clear(P[i]);mpq_clear(prefix[i]);mpq_clear(logs[i]); }mpq_clears(x,y,NULL);return 0;
}
#include "collision_sampling_prefix.inc"
/* -1 means this is an operation from the earlier carrier interface. */
static int collision_sampling_source_command(int argc,char **argv)
{
    if(!argc)return -1;
    const char *op=argv[0];if(!strcmp(op,"phase-sum"))return cs_phase_sum(argc,argv);
    if(!strcmp(op,"prefix-population") || !strcmp(op,"stopped-cost")) {
        unsigned first,last;
        if(argc!=3 || !cs_uint(argv[1],&first) || !cs_uint(argv[2],&last))return 1;
        return !strcmp(op,"prefix-population")?cs_prefix_population(first,last):cs_stopped_costs(first,last);
    }
    int known=!strcmp(op,"grid")||!strcmp(op,"source")||!strcmp(op,"decomposition")||!strcmp(op,"descent")||!strcmp(op,"prefix-word")||!strcmp(op,"fold")||!strcmp(op,"folded-source")||!strcmp(op,"rectangle")||!strcmp(op,"cubic")||!strcmp(op,"dedekind-mass")||!strcmp(op,"kernel")||!strcmp(op,"shells")||!strcmp(op,"interior")||!strcmp(op,"reciprocal")||!strcmp(op,"completion");
    if(!known)return -1;
    unsigned a=0,b=0,c=0,d=0,e=0;long sn=0,sd=1;
    if(argc<2||!cs_uint(argv[1],&a))goto bad;
    if(!strcmp(op,"shells")&&argc==3&&cs_uint(argv[2],&b))return cs_arithmetic_shells(a,b);
    if(!strcmp(op,"kernel")&&argc==4&&cs_uint(argv[2],&b)&&cs_uint(argv[3],&c)) {
        mpq_t x;mpq_init(x);int ok=cs_kernel_q(x,a,b,c);if(ok)cs_print("boundary_kernel",x);mpq_clear(x);return !ok;
    }
    if(!strcmp(op,"interior")&&argc==2&&a>=257&&a<=997) {
        int prime=1;for(unsigned j=2;j<=a/j;++j)if(a%j==0)prime=0;if(!prime)goto bad;
        unsigned r=1;while(4*(r+2)*(r+2)<=a)r+=2;unsigned left=r*r,right=(a+r)/2;
        mpq_t x,y;mpq_inits(x,y,NULL);int ok=cs_kernel_q(x,a*a,left,right);cs_fraction(y,a,64);ok=ok&&mpq_cmp(x,y)>=0;
        if(ok) { printf("left_index=%u\nright_index=%u\n",left,right);cs_print("absolute_mean_zero_rayleigh",x);cs_print("operator_lower",y);puts("The two coordinates lie on the required unit plateau. This is an operator obstruction, not an estimate of the prescribed scalar sum."); }
        mpq_clears(x,y,NULL);return !ok;
    }
    if(!strcmp(op,"reciprocal")&&argc==4&&cs_uint(argv[2],&b)&&cs_signed(argv[3],&sn)&&a>=2&&a<=10000&&b>=2&&b<=10000&&cs_gcd(a,b)==1) {
        mpq_t x,y,z,t;mpq_inits(x,y,z,t,NULL);cs_fraction(x,sn*cs_inverse(a,b),b);cs_fraction(y,-sn*cs_inverse(b,a),a);cs_fraction(z,sn,(unsigned long)a*b);mpq_add(t,y,z);mpq_sub(t,x,t);
        cs_print("original_phase",x);cs_print("adjacent_phase",y);cs_print("correction",z);cs_print("integer_phase_difference",t);int failed=mpz_cmp_ui(mpq_denref(t),1)!=0;mpq_clears(x,y,z,t,NULL);return failed;
    }
    if(!strcmp(op,"completion")&&argc==5&&cs_uint(argv[2],&b)&&cs_uint(argv[3],&c)&&a>=1&&a<=512&&b>=2&&b<=120&&c<=1000000) {
        mpq_t values[120],sum,variation,x,t;for(unsigned i=0;i<120;++i)mpq_init(values[i]);mpq_inits(sum,variation,x,t,NULL);unsigned count=0;int ok=1;const char *s=argv[4];
        while(*s&&ok) { const char *comma=strchr(s,',');size_t size=comma?(size_t)(comma-s):strlen(s);char token[162];if(!size||size>=sizeof token||count>=b) { ok=0;break; }memcpy(token,s,size);token[size]=0;ok=cs_rational(token,values[count++]);if(!comma)break;s=comma+1;if(!*s)ok=0; }
        ok=ok&&count==b&&!mpq_sgn(values[0]);
        if(ok) { for(unsigned i=0;i<b;++i) { mpq_sub(t,values[i],values[(i+b-1)%b]);mpq_abs(t,t);mpq_add(variation,variation,t);if(cs_gcd(i,b)==1) { cs_scale(t,values[i],cs_source(a,b,(long)c*cs_inverse(i,b)),1);mpq_add(sum,sum,t); } }cs_print("completed_source",sum);cs_print("cyclic_variation",variation); }
        for(unsigned i=0;i<120;++i)mpq_clear(values[i]);
        mpq_clears(sum,variation,x,t,NULL);return !ok;
    }
    if(!strcmp(op,"grid")&&argc==4&&cs_uint(argv[2],&b)&&cs_shift(argv[3],&sn,&sd))return cs_grid(a,b,sn,sd);
    if(!strcmp(op,"decomposition")&&argc==3&&cs_uint(argv[2],&b))return cs_decomposition(a,b);
    if(!strcmp(op,"source")&&argc==4&&cs_uint(argv[2],&b)&&cs_signed(argv[3],&sn)&&a>=1&&a<=512&&b>=2&&b<=512) {
        long mean=0,variation=0,peak=0,previous=cs_source(a,b,b-1);
        for(unsigned i=0;i<b;++i) { long x=cs_source(a,b,i);mean+=x;variation+=labs(x-previous);if(labs(x)>peak)peak=labs(x);previous=x; }
        printf("source=%ld\nresidue_sum=%ld\nabsolute_max=%ld\ncyclic_variation=%ld\namplitude_bound=%u\nvariation_bound=%u\n",cs_source(a,b,sn),mean,peak,variation,a/b,4*(a/b));return 0;
    }
    if(!strcmp(op,"descent")&&argc==4&&cs_uint(argv[2],&b)&&cs_uint(argv[3],&c)&&a>=3&&a<=512&&b>=1&&2*b<a&&cs_gcd(a,b)==1&&c>=1&&c<=a) {
        mpq_t x,y,z;mpq_inits(x,y,z,NULL);cs_stopped(x,y,a,b,c,1);cs_print("cost",x);cs_print("terminal",y);mpq_add(z,x,y);cs_print("dedekind",z);mpq_clears(x,y,z,NULL);return 0;
    }
    if(!strcmp(op,"prefix-word")&&argc==3&&cs_signed(argv[2],&sn)) {
        long C,E;int det;if(!cs_prefix_row(a,sn,&C,&E,&det))goto bad;
        printf("A=%u\nB=%ld\nC=%ld\nE=%ld\ndeterminant=%d\n",a,sn,C,E,det);
        unsigned digits[32];int signs[32];unsigned length=cs_prefix_word(a,sn,digits,signs);
        printf("length=%u\n",length);for(unsigned i=length;i>0;--i)printf("digit=%u orientation=%d\n",digits[i-1],signs[i-1]);return 0;
    }
    if(!strcmp(op,"fold")&&argc==7&&cs_signed(argv[2],&sn)&&cs_uint(argv[3],&b)&&cs_uint(argv[4],&c)&&cs_uint(argv[5],&d)&&cs_uint(argv[6],&e)&&b<=512&&c>=1&&2*c<b&&cs_gcd(b,c)==1&&d<=1000000&&e<=10000) {
        long C,E;int det;if(!cs_prefix_row(a,sn,&C,&E,&det))goto bad;
        long k=(long)a*b+sn*c,parent=C*b+E*c;unsigned f=c==1?0:cs_inverse(b,c);long v0=(1-(long)f*b)/(long)c,h=(long)a*v0-sn*f;
        long lhs=det*cs_delta((long)d*cs_inverse((unsigned)parent,(unsigned)k),(unsigned)k,e),rhs=cs_delta((long)d*h,(unsigned)k,e);
        printf("modulus=%ld\nparent=%ld\ninverse_orientation=%ld\nfolded_inverse=%ld\noriginal_count=%ld\nfolded_count=%ld\n",k,parent,cs_mod(parent*h,k),h,lhs,rhs);
        mpq_t left,right,gamma,zeta,X,t;mpq_inits(left,right,gamma,zeta,X,t,NULL);
        cs_fraction(gamma,(long)d*(1-(long)f*b),(unsigned long)c*b);cs_fraction(zeta,(long)c*sn,b);
        long shifts[]={0,-(long)e-1,(long)e};for(unsigned i=0;i<3;++i) {
            cs_fraction(left,(long)d*h+shifts[i],k);cs_fraction(X,(long)d*sn-shifts[i]*b,(unsigned long)b*b);
            cs_fraction(t,a,1);mpq_add(t,t,zeta);mpq_div(right,X,t);mpq_sub(right,gamma,right);
            if(!mpq_equal(left,right))lhs=rhs+1;
            printf("endpoint_shift=%ld\n",shifts[i]);cs_print("phase",left);cs_print("reciprocal_phase",right);
        }
        mpq_clears(left,right,gamma,zeta,X,t,NULL);return lhs!=rhs;
    }
    if(!strcmp(op,"folded-source")&&argc==6&&cs_uint(argv[2],&b)&&cs_uint(argv[3],&c)&&cs_uint(argv[4],&d)&&cs_uint(argv[5],&e)&&a>=1&&a<=512&&b<=1000000&&c>=2&&c<=128&&d<=512&&e>=1&&2*e<d&&cs_gcd(d,e)==1) {
        unsigned f=e==1?0:cs_inverse(d,e);long v0=(1-(long)f*d)/(long)e,total=0;unsigned terms=0;
        for(unsigned A=c;A<2*c;++A)for(long B=-(long)A+1;B<(long)A;++B)if(labs(B)>=2&&cs_gcd(A,(unsigned)labs(B))==1&&cs_golden(A,B)) {
            long k=(long)A*d+B*e;if(k>(long)a)continue;total+=cs_delta((long)b*((long)A*v0-B*f),(unsigned)k,a);++terms;
        }
        printf("joined_source=%ld\nprimitive_prefixes=%u\n",total,terms);return 0;
    }
    if(!strcmp(op,"rectangle")&&argc==5&&cs_uint(argv[2],&b)&&cs_uint(argv[3],&c)&&cs_uint(argv[4],&d)&&a<=1000000&&b>=1&&b<=120&&c>=1&&c<=120&&d<=2) {
        mpq_t total,x,y,z;mpq_inits(total,x,y,z,NULL);
        for(unsigned k=1;k<=b;++k)if(d!=1||(k&1))for(unsigned j=1;j<=c;++j)if(d!=2||(j&1))for(unsigned h=0;h<k;++h) { cs_saw(x,j*h,k);cs_saw(y,(unsigned)(((uint64_t)a*h)%k),k);mpq_mul(z,x,y);mpq_add(total,total,z); }
        cs_scale(total,total,2,1);cs_print("source_rectangle",total);mpq_clears(total,x,y,z,NULL);return 0;
    }
    if(!strcmp(op,"cubic")&&argc==2&&cs_prime(a)) {
        CollisionSampling state;collision_sampling_init(&state);int ok=collision_sampling_q(&state,a);
        if(ok) { mpq_t x,y,t;mpq_inits(x,y,t,NULL);mpq_neg(x,state.value[CS_DEFECT]);cs_scale(y,state.value[CS_DEFECT],1,2);cs_fraction(t,3L*(a-1),2UL*a*a);mpq_sub(y,y,t);cs_fraction(t,a-1,(unsigned long)a*a*a*a);mpq_add(y,y,t);cs_print("constant_eigenvalue_change",x);cs_print("transverse_eigenvalue_change",y);mpq_clears(x,y,t,NULL); }
        collision_sampling_clear(&state);return !ok;
    }
    if(!strcmp(op,"dedekind-mass")&&argc==2&&a>=1&&a<=512) {
        mpq_t mass,H,bound,t;mpq_inits(mass,H,bound,t,NULL);
        for(unsigned h=1;h<=a;++h) { cs_fraction(t,1,h);mpq_add(H,H,t);if(cs_gcd(h,a)==1) { collision_sampling_dedekind_q(t,a,h);mpq_abs(t,t);mpq_add(mass,mass,t); } }
        mpq_mul(bound,H,H);cs_scale(bound,bound,a,4);cs_print("absolute_mass",mass);cs_print("mass_bound",bound);int failed=mpq_cmp(mass,bound)>0;mpq_clears(mass,H,bound,t,NULL);return failed;
    }
bad: fputs("Invalid signed-source parameters; see collision-sampling help.\n",stderr);return 1;
}
