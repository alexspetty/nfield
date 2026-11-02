#include "collision_capacity_generation.h"
#include "collision_kernel_readout.h"
#include "weighted_remainder_exact.h"
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned gcd_u(unsigned a,unsigned b)
{ while(b){unsigned t=a%b;a=b;b=t;}return a; }
static int prime_u(unsigned n)
{ if(n<2)return 0;for(unsigned d=2;d<=n/d;d++)if(n%d==0)return 0;return 1; }
static int mu_u(unsigned n)
{ int m=1;for(unsigned p=2;p<=n/p;p++)if(n%p==0){n/=p;m=-m;if(n%p==0)return 0;}
  return n>1?-m:m; }
static void scale_q(mpq_t out,const mpq_t in,long num,unsigned long den)
{ mpq_t t;mpq_init(t);mpq_set_si(t,num,den);mpq_mul(out,in,t);mpq_clear(t); }
static int dimensions(unsigned b,unsigned lag,unsigned *q,unsigned *m)
{
    if(b<2||b>64||lag<1||lag>12)return 0;
    unsigned z=1;
    for(unsigned j=0;j<lag;j++){if(z>4096/b)return 0;z*=b;}
    if(z>4096/b)return 0;
    *q=z;*m=b*z;return 1;
}
int collision_generation_source_q(mpq_t cells,mpq_t rows,
    unsigned b,unsigned lag,unsigned phase)
{
    unsigned q,m;if(cells==rows||!dimensions(b,lag,&q,&m)||phase>=m)return 0;
    unsigned a=(unsigned)(((uint64_t)(m+1-q)*phase)%m);
    int64_t count=0,sum=0;
    for(unsigned d=0;d<b;d++)for(unsigned y=0;y<q/b;y++){
        unsigned n=d*(q+1)+b*y;
        count+=(int64_t)(n+1)*a/m-(int64_t)n*a/m;
    }
    for(unsigned r=1;r<q;r++){
        unsigned t=(r*phase)%m;
        if(t)sum+=2*(int64_t)t-m;
    }
    mpq_set_si(cells,count*b-a,b);mpq_canonicalize(cells);
    mpq_set_si(rows,sum,m);mpq_canonicalize(rows);return 1;
}
int collision_generation_carry_q(mpq_t variance,mpq_t carry,mpq_t parent,
    mpq_t left,mpq_t right,mpq_t defect,unsigned m,unsigned a,unsigned b)
{
    mpq_ptr outputs[]={variance,carry,parent,left,right,defect};
    for(int i=0;i<6;i++)for(int j=0;j<i;j++)if(outputs[i]==outputs[j])return 0;
    if(m<3||m>1023||!(m%2))return 0;
    a%=m;b%=m;unsigned c=(a+b)%m;
    if(gcd_u(a,m)!=1||gcd_u(b,m)!=1||gcd_u(c,m)!=1)return 0;
    int64_t vv=0,pp=0,ll=0,rr=0,dd=0,ck=0;
    for(unsigned x=0;x<m;x++){
        unsigned A=a*x%m,B=b*x%m,C=c*x%m;
        long u=2*(long)A-(m-1),v=2*(long)B-(m-1),w=2*(long)C-(m-1);
        long U=A?2*(long)A-m:0,V=B?2*(long)B-m:0,W=C?2*(long)C-m:0;
        vv+=u*u;pp+=u*v;ll+=u*w;rr+=w*v;dd+=U*V-U*W-W*V;ck+=(A+B)/m;
    }
    unsigned long denominator=4UL*m*m*m;
    mpq_set_si(variance,vv,denominator);mpq_set_si(parent,pp,denominator);
    mpq_set_si(left,ll,denominator);mpq_set_si(right,rr,denominator);
    mpq_set_si(defect,dd,denominator);mpq_set_si(carry,ck*(m-ck),(unsigned long)m*m);
    for(int j=0;j<6;j++)mpq_canonicalize(outputs[j]);
    return 1;
}
int collision_generation_recover_q(mpq_t out,unsigned n)
{
    if(n<1||n>COLLISION_GENERATION_MAX)return 0;
    mpq_t sum,j,k,t;mpq_inits(sum,j,k,t,NULL);
    for(unsigned d=1;d<=n;d++)if(n%d==0){
        weighted_remainder_capacity_q(j,d);weighted_remainder_capacity_q(k,d-1);
        mpq_sub(t,j,k);mpq_set_ui(k,1,3);mpq_sub(t,t,k);
        scale_q(t,t,3*mu_u(n/d),2);mpq_add(sum,sum,t);
    }
    scale_q(out,sum,1,n);mpq_clears(sum,j,k,t,NULL);return 1;
}
static int control_valid(unsigned r,unsigned s)
{ return r>=5&&s>r&&s<2*r&&s<=COLLISION_GENERATION_MAX&&prime_u(r)&&prime_u(s); }
static void delta_mass(mpq_t out,unsigned r,unsigned s,unsigned n)
{
    mpq_t t;mpq_init(t);mpq_set_ui(out,0,1);
    if(n%r==0){unsigned d=n/r;mpq_set_si(out,mu_u(d),(unsigned long)d*d*d);}
    if(n%s==0){unsigned d=n/s;mpq_set_si(t,mu_u(d),(unsigned long)d*d*d);mpq_sub(out,out,t);}
    scale_q(out,out,1,8UL*s*s*s);mpq_canonicalize(out);mpq_clear(t);
}
int collision_generation_control_q(mpq_t mass,mpq_t row,mpq_t capacity,
    unsigned r,unsigned s,unsigned n)
{
    if(mass==row||mass==capacity||row==capacity||!control_valid(r,s)||n<1||n>COLLISION_GENERATION_MAX)return 0;
    mpq_t t;mpq_init(t);delta_mass(mass,r,s,n);
    mpq_set_si(row,(n==r)-(n==s),8UL*s*s*s);mpq_canonicalize(row);
    mpq_set_ui(capacity,0,1);
    for(unsigned k=2;k<=n;k++){
        delta_mass(t,r,s,k);scale_q(t,t,2L*k*(n/k),3);mpq_add(capacity,capacity,t);
    }
    mpq_clear(t);return 1;
}
int collision_generation_current_q(mpq_t out,unsigned n,unsigned p,unsigned r,unsigned s)
{
    if(n<1||n>COLLISION_GENERATION_MAX||!prime_u(p)||p>COLLISION_GENERATION_MAX||
       !((r==0&&s==0)||control_valid(r,s)))return 0;
    mpq_t a[COLLISION_GENERATION_MAX+1],inv[COLLISION_GENERATION_MAX+1],t,sum;
    mpq_inits(t,sum,NULL);
    for(unsigned j=0;j<=n;j++){mpq_init(a[j]);mpq_init(inv[j]);}
    for(unsigned j=1;j<=n;j++){
        mpq_set_ui(a[j],1,j);
        if(r){long delta=(j+1==r)*(long)r*r-(j==r)*(long)r*r-
                         (j+1==s)*(long)s*s+(j==s)*(long)s*s;
            mpq_set_si(t,delta,8UL*s*s*s);mpq_add(a[j],a[j],t);}
    }
    mpq_set_ui(inv[1],1,1);
    for(unsigned j=2;j<=n;j++){
        for(unsigned d=2;d<=j;d++)if(j%d==0){mpq_mul(t,a[d],inv[j/d]);mpq_sub(inv[j],inv[j],t);}
    }
    for(unsigned d=1;d<=n;d++)if(n%d==0){
        unsigned k=d,v=0;while(k%p==0){v++;k/=p;}
        mpq_mul(t,a[d],inv[n/d]);scale_q(t,t,(long)n*v,1);mpq_add(sum,sum,t);
    }
    mpq_set(out,sum);
    for(unsigned j=0;j<=n;j++){mpq_clear(a[j]);mpq_clear(inv[j]);}
    mpq_clears(t,sum,NULL);return 1;
}
static int parse(const char *s,unsigned min,unsigned max,unsigned *out)
{ char *e;errno=0;if(!s||!*s||*s=='-')return 0;unsigned long n=strtoul(s,&e,10);
  if(errno||*e||n<min||n>max)return 0;
  *out=(unsigned)n;return 1; }
void collision_capacity_generation_help(void)
{
    puts("capacity-generation\n"
         "  source base lag [phase]           exact digit cells and straightened sawtooth rows\n"
         "  carry modulus a b                 centered covariance and midpoint defect\n"
         "  measurement m a b power amplitude local power and nonlocal quartic controls\n"
         "  ledger cutoff                     exact capacity, weights, finite recovery\n"
         "  refine a b                        Farey interval and calibrated child masses\n"
         "  control r s cutoff                smooth normalized prefix control\n"
         "  current cutoff [r s]              rational coefficients of log(prime)\n"
         "  seed q length                     rational enclosures of seed and selector\n"
         "  profile period lambda c0,c1,...    raw symmetric polynomial angular ledger\n"
         "  lattice x cutoff                  positive rational lattice seed and tail bound\n"
         "  verify                            finite exact identity checks\n"
         "  Source grid <=4096; odd carry modulus <=1023; ledger/current/control <=120.\n"
         "  Measurement uses odd m<=127, even power 2..12 and rational amplitude.\n"
         "  Control requires primes 5<=r<s<2r, with epsilon=1/(8*s^3).\n"
         "  Seed requires q*length<=240. Profile period<=120, at most 9 rational\n"
         "  coefficients for h(u)=sum c_j[u(1-u)]^j. Use none for h=0.\n"
         "  P(u)=lambda+2u(1-u)h(u) is raw, not asserted positive or normalized.\n"
         "  Lattice x must be positive rational; square cutoff<=64.\n"
         "  Finite checks do not certify all-amplitude rigidity, infinite inversion or limits.");
}
int collision_capacity_generation_command(int argc,char **argv)
{
    if(!argc||!strcmp(argv[0],"--help")){collision_capacity_generation_help();return 0;}
    if(argc==1&&!strcmp(argv[0],"verify"))return collision_capacity_generation_verify()?0:1;
    if(argc&&(!strcmp(argv[0],"measurement")||!strcmp(argv[0],"seed")||!strcmp(argv[0],"profile")||!strcmp(argv[0],"lattice")))
        return collision_kernel_readout_command(argc,argv);
    unsigned a,b,n=0;mpq_t x,y,z,l,r,d;mpq_inits(x,y,z,l,r,d,NULL);int ok=0;
    if(!strcmp(argv[0],"source")&&(argc==3||argc==4)&&parse(argv[1],2,64,&a)&&parse(argv[2],1,12,&b)){
        unsigned q,m;if(!dimensions(a,b,&q,&m))goto done;
        if(argc==4&&!parse(argv[3],0,m-1,&n))goto done;
        puts("base,lag,modulus,cutoff,phase,cell_response,affine_sample");
        for(unsigned phase=n;phase<(argc==4?n+1:m);phase++){
            collision_generation_source_q(x,y,a,b,phase);
            gmp_printf("%u,%u,%u,%u,%u,%Qd,%Qd\n",a,b,m,q-1,phase,x,y);
        }ok=1;
    }else if(!strcmp(argv[0],"carry")&&argc==4&&parse(argv[1],3,1023,&n)&&parse(argv[2],0,1023,&a)&&parse(argv[3],0,1023,&b)){
        if(!collision_generation_carry_q(x,y,z,l,r,d,n,a,b))goto done;
        puts("modulus,a,b,row_variance,carry_variance,parent,left,right,midpoint_defect");
        gmp_printf("%u,%u,%u,%Qd,%Qd,%Qd,%Qd,%Qd,%Qd\n",n,a,b,x,y,z,l,r,d);ok=1;
    }else if(!strcmp(argv[0],"ledger")&&argc==2&&parse(argv[1],1,COLLISION_GENERATION_MAX,&n)){
        puts("n,capacity,weight,recovered_weight,unprimitive_row,increment");
        for(unsigned k=1;k<=n;k++){
            weighted_remainder_capacity_q(x,k);weighted_remainder_weight_q(y,k);
            collision_generation_recover_q(z,k);mpq_set_ui(l,0,1);
            for(unsigned j=1;j<k;j++){mpq_set_ui(d,1,j);mpq_add(l,l,d);}
            scale_q(l,l,1,(unsigned long)k*k);mpq_set_ui(r,1,k);
            gmp_printf("%u,%Qd,%Qd,%Qd,%Qd,%Qd\n",k,x,y,z,l,r);
        }ok=1;
    }else if(!strcmp(argv[0],"refine")&&argc==3&&parse(argv[1],1,120,&a)&&parse(argv[2],1,120,&b)&&gcd_u(a,b)==1){
        unsigned k=a+b,h=1;while(a*h%k!=1)h++;unsigned u=(a*h-1)/k,v=h-u;
        mpq_set_ui(x,u,a);mpq_canonicalize(x);mpq_set_ui(y,v,b);mpq_canonicalize(y);
        mpq_set_ui(z,1,2UL*a*b);mpq_set_ui(l,1,2UL*a*k);mpq_set_ui(r,1,2UL*k*b);
        puts("a,b,address,left_numerator,left_denominator,mediant_numerator,right_numerator,right_denominator,parent_mass,left_mass,right_mass");
        gmp_printf("%u,%u,%u,%u,%u,%u,%u,%u,%Qd,%Qd,%Qd\n",a,b,k,u,a,h,v,b,z,l,r);ok=1;
    }else if(!strcmp(argv[0],"control")&&argc==4&&parse(argv[1],5,120,&a)&&parse(argv[2],5,120,&b)&&parse(argv[3],1,120,&n)&&control_valid(a,b)){
        puts("n,delta_mass,delta_row,delta_capacity");
        for(unsigned k=1;k<=n;k++){
            collision_generation_control_q(x,y,z,a,b,k);gmp_printf("%u,%Qd,%Qd,%Qd\n",k,x,y,z);
        }ok=1;
    }else if(!strcmp(argv[0],"current")&&(argc==2||argc==4)&&parse(argv[1],1,120,&n)){
        a=b=0;if(argc==4&&(!parse(argv[2],5,120,&a)||!parse(argv[3],5,120,&b)||!control_valid(a,b)))goto done;
        puts("n,prime,log_coefficient");
        for(unsigned k=1;k<=n;k++)for(unsigned p=2;p<=k;p++)if(prime_u(p)){
            collision_generation_current_q(x,k,p,a,b);if(mpq_sgn(x))gmp_printf("%u,%u,%Qd\n",k,p,x);
        }ok=1;
    }
done:
    mpq_clears(x,y,z,l,r,d,NULL);
    if(!ok)fputs("capacity-generation: invalid command or arguments; see help\n",stderr);
    return ok?0:1;
}
