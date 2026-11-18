/* Exact finite checks for source selection. */
#include "../src/reset_source.h"
#include <stdlib.h>
#include "reset_forest_contracts_source_ids.inc"
#include "reset_forest_contracts_source_kinds.inc"

#define FS_SOURCE_DOMAIN "N in {0,1,2,4,7,12,31,64}; zero, unit, signed fractional, sparse and nonnegative fractional sources; Omega in {0,1,2,6,30,101,10^40+39}; source coordinates 1..N and reset indices 0..N+2 where applicable"
#define FS_UNIT_DOMAIN "N in {0,1,2,4,7,12,31,64}; unit sources only; Omega in {0,1,2,6,30,101,10^40+39}; source coordinates 0..N+2 and reset indices 0..N+2 where applicable"
#define FS_NONNEG_DOMAIN "N in {0,1,2,4,7,12,31,64}; zero, unit and nonnegative fractional sources only; Omega in {0,1,2,6,30,101,10^40+39}; source coordinates 0..N+2"
#define FS_COLUMN_DOMAIN "N in {1,2,4,7,12,31,64}; every basis source and every output coordinate; Omega in {0,1,2,6,30,101,10^40+39}"
#define FS_MASK_DOMAIN "N in {0,1,2,4,7,12,31,64}; zero, unit, signed fractional, sparse and nonnegative fractional sources plus every basis source at listed cutoffs through N=12; four Boolean masks: empty, all, odd indices, and indices congruent to 1 modulo 3"
#define FS_ADD_DOMAIN FS_MASK_DOMAIN "; second mask selects indices divisible by 3 outside the first mask, so supports are disjoint"
#define FS_COMPOSE_DOMAIN FS_MASK_DOMAIN "; second mask selects indices divisible by 3; native sequential projections are compared with intersection"
#define FS_INVERSE_DOMAIN "N in {0,1,2,4,7,12,31,64}; zero, unit, signed fractional, sparse and nonnegative fractional sources plus every basis source at listed cutoffs through N=12; all-one mask only"
#define FS_RIGHT_INVERSE_DOMAIN "N in {0,1,2,4,7,12,31,64}; desired reset masses use five rational patterns and every basis vector at listed cutoffs through N=12; source obtained independently by triangular inversion; all-one mask only"
#define FS_WORK_DOMAIN "N in {0,1,2,3,5,8}; zero, unit, signed fractional, sparse and nonnegative fractional sources; four masks: empty, all, odd indices, and 1 modulo 3; one grid per case, cycling {1,2,4,9,25,49} by (cutoff-index+source-index+mask-index) modulo 6, not their Cartesian product; first source is original, selected or complementary; second source remains original"
#define FS_SATURATED_WORK_DOMAIN "N in {0,1,2,3,5,8}; five rational source patterns; carriers {0,2,6,30}; one grid per case, cycling {1,2,4,9,25,49} by (cutoff-index+source-index+carrier-index) modulo 6; first source is original, collapsed or complementary; second source remains original"
#define FS_CLOCK_DOMAIN "Every N=1..8, every basis source j=1..N, every clock d=1..N and each grid in {1,2,4,9,25,49}; all-one reset mask"
#define FS_ENERGY_DOMAIN FS_WORK_DOMAIN "; continuous energy of all three components checked by exact affine-interval integration"
#define FS_SAMPLED_ENTRY_DOMAIN "Every N=1..8, every basis pair 1<=i<=j<=N and each grid in {1,2,4,9,25,49}; unnormalized sampled Gram entries recovered by polarization and compared with literal grid sums"
#define FS_PRIME_DOMAIN "p in {2,3,5,7,11}; N=p-1,Q=p^2; five rational source patterns; complete source energy, all primitive reset work, common contact and curvature retained"
#define FS_SEED_DOMAIN "N=30,Q=961,unit source; literal seed clocks {23,22,19,24,20}, packet {23,22,19} and fringe {24,20}; exact declared rational value"

static void fs_scale(mpq_t out,const mpq_t in,long num,unsigned long den)
{mpq_t t;mpq_init(t);mpq_set_si(t,num,den);mpq_canonicalize(t);mpq_mul(out,in,t);mpq_clear(t);}
static void fs_assert(ContractResult *r,int ok)
{r->assertions++;if(!ok)r->failures++;}
static void fs_init_vector(mpq_t *c)
{for(unsigned j=0;j<=RESET_SOURCE_MAX_CUTOFF;j++)mpq_init(c[j]);}
static void fs_clear_vector(mpq_t *c)
{for(unsigned j=0;j<=RESET_SOURCE_MAX_CUTOFF;j++)mpq_clear(c[j]);}
static void fs_source(mpq_t *c,unsigned n,unsigned pattern)
{
    for(unsigned j=0;j<=RESET_SOURCE_MAX_CUTOFF;j++){
        if(!j||j>n||pattern==0)mpq_set_ui(c[j],0,1);
        else if(pattern==1)mpq_set_ui(c[j],1,1);
        else if(pattern==2)mpq_set_si(c[j],j%2?-(long)j:(long)j,j+1);
        else if(pattern==3)mpq_set_si(c[j],j==1?3:j==n?-5:0,7);
        else mpq_set_ui(c[j],(j*j+1)%7,j%5+1);
        mpq_canonicalize(c[j]);
    }
}
static void fs_mask(unsigned char *mask,unsigned n,unsigned pattern)
{memset(mask,0,RESET_SOURCE_MAX_CUTOFF+1);for(unsigned k=1;k<=n;k++)mask[k]=(unsigned char)(pattern==1?1:pattern==2?k%2:pattern==3?(k%3==1):0);}
static void fs_mass(mpq_t out,const mpq_t *c,unsigned n,unsigned k)
{mpq_set_ui(out,0,1);for(unsigned j=1;j<=n;j++)if(k&&j%k==0)mpq_add(out,out,c[j]);}
/* Descending triangular elimination is independent of the utility's explicit
 * Mobius-sum inverse and gives a second exact source reconstruction. */
static void fs_invert(mpq_t *b,const mpq_t *m,unsigned n)
{
    for(unsigned j=0;j<=RESET_SOURCE_MAX_CUTOFF;j++)mpq_set_ui(b[j],0,1);
    for(unsigned d=n;d;d--){mpq_set(b[d],m[d]);for(unsigned j=d+1;j<=n;j++)if(j%d==0)mpq_sub(b[d],b[d],b[j]);}
}
static unsigned fs_gcd(unsigned a,unsigned b)
{while(b){unsigned c=a%b;a=b;b=c;}return a;}
static void fs_collapse(mpq_t *b,const mpq_t *c,unsigned n,const mpz_t omega)
{
    for(unsigned j=0;j<=RESET_SOURCE_MAX_CUTOFF;j++)mpq_set_ui(b[j],0,1);
    for(unsigned j=1;j<=n;j++){unsigned d=(unsigned)mpz_gcd_ui(NULL,omega,j);mpq_add(b[d],b[d],c[j]);}
}
static void fs_omega(mpz_t omega,unsigned choice)
{static const unsigned values[]={0,1,2,6,30,101};if(choice<6)mpz_set_ui(omega,values[choice]);else mpz_set_str(omega,"10000000000000000000000000000000000000039",10);}

/* Literal rational sawtooth evaluation uses floor of a rational, rather than
 * the modular integer loop used in the utility. Integer arguments read zero. */
static void fs_field(mpq_t out,const mpq_t *c,unsigned n,const mpq_t x)
{
    mpq_t y,t,z;mpz_t floor;
    mpq_inits(y,t,z,NULL);mpz_init(floor);mpq_set_ui(out,0,1);
    for(unsigned j=1;j<=n;j++){
        fs_scale(y,x,j,1);mpz_fdiv_q(floor,mpq_numref(y),mpq_denref(y));
        mpq_set_z(t,floor);mpq_sub(y,y,t);
        if(mpq_sgn(y)==0)continue;
        fs_scale(y,y,2,1);mpq_set_ui(t,1,1);mpq_sub(y,y,t);
        mpq_mul(z,y,c[j]);mpq_add(out,out,z);
    }
    mpz_clear(floor);mpq_clears(y,t,z,NULL);
}
static int fs_qcmp(const void *a,const void *b)
{return mpq_cmp((mpq_srcptr)a,(mpq_srcptr)b);}
static void fs_integral(mpq_t out,const mpq_t *c,unsigned n)
{
    mpq_t edges[2114],lo,hi,len,mid,value,slope,t,u;
    unsigned count=0;mpq_inits(lo,hi,len,mid,value,slope,t,u,NULL);
    mpq_init(edges[count]);mpq_set_ui(edges[count++],0,1);
    for(unsigned j=1;j<=n;j++)for(unsigned a=1;a<=j;a++){
        mpq_init(edges[count]);mpq_set_ui(edges[count],a,j);mpq_canonicalize(edges[count]);count++;
    }
    if(!n){mpq_init(edges[count]);mpq_set_ui(edges[count++],1,1);}
    qsort(edges,count,sizeof(mpq_t),fs_qcmp);
    mpq_set_ui(out,0,1);mpq_set_ui(slope,0,1);
    for(unsigned j=1;j<=n;j++){fs_scale(t,c[j],2L*j,1);mpq_add(slope,slope,t);}
    for(unsigned i=1;i<count;i++){
        if(mpq_equal(edges[i-1],edges[i]))continue;
        mpq_sub(len,edges[i],edges[i-1]);mpq_add(mid,edges[i],edges[i-1]);fs_scale(mid,mid,1,2);
        fs_field(value,c,n,mid);mpq_mul(t,value,value);mpq_mul(t,t,len);
        mpq_mul(u,len,len);mpq_mul(u,u,len);mpq_mul(u,u,slope);mpq_mul(u,u,slope);fs_scale(u,u,1,12);
        mpq_add(t,t,u);mpq_add(out,out,t);
    }
    for(unsigned i=0;i<count;i++)mpq_clear(edges[i]);
    mpq_clears(lo,hi,len,mid,value,slope,t,u,NULL);
}
static void fs_sample(mpq_t out,const mpq_t *c,const mpq_t *e,unsigned n,unsigned q)
{
    mpq_t x,a,b,t;mpq_inits(x,a,b,t,NULL);mpq_set_ui(out,0,1);
    for(unsigned j=0;j<q;j++){
        mpq_set_ui(x,j,q);mpq_canonicalize(x);fs_field(a,c,n,x);fs_field(b,e,n,x);
        mpq_mul(t,a,b);mpq_add(out,out,t);
    }
    fs_scale(out,out,1,q);mpq_clears(x,a,b,t,NULL);
}
static void fs_clock(mpq_t primitive,mpq_t clock,const mpq_t *c,unsigned n,unsigned q,unsigned k)
{
    mpq_t x,y,field,psi,t;mpq_inits(x,y,field,psi,t,NULL);mpq_set_ui(primitive,0,1);mpq_set_ui(clock,0,1);
    for(unsigned a=1;a<k;a++){
        mpq_set_ui(x,a,k);mpq_canonicalize(x);fs_field(field,c,n,x);
        unsigned r=(q*a)%k;mpq_set_si(psi,r?2L*r-(long)k:0,2UL*k);mpq_canonicalize(psi);
        mpq_mul(t,field,psi);mpq_add(clock,clock,t);
        if(fs_gcd(a,k)==1)mpq_add(primitive,primitive,t);
    }
    fs_scale(clock,clock,1,2);mpq_clears(x,y,field,psi,t,NULL);
}

static ContractResult fs_coordinates(unsigned kind)
{
    static const unsigned cutoffs[]={0,1,2,4,7,12,31,64};
    ContractResult r={0,0,0};ResetSource f,g;reset_source_init(&f);reset_source_init(&g);
    mpq_t c[65],expected[65],mass[65],inverse[65],a,b,total;mpz_t omega;
    fs_init_vector(c);fs_init_vector(expected);fs_init_vector(mass);fs_init_vector(inverse);
    mpq_inits(a,b,total,NULL);mpz_init(omega);
    for(unsigned ni=0;ni<8;ni++)for(unsigned pattern=0;pattern<5;pattern++)for(unsigned oi=0;oi<7;oi++){
        unsigned n=cutoffs[ni];
        int unit=kind==FS_UNIT_MASS||kind==FS_UNIT_LE||kind==FS_UNIT_GE||kind==FS_POPULATION||kind==FS_UNIT_TOTAL;
        if(unit&&pattern!=1)continue;
        if(kind==FS_NONNEG&&(pattern==2||pattern==3))continue;
        fs_source(c,n,pattern);fs_omega(omega,oi);fs_collapse(expected,c,n,omega);
        int ok=reset_source_collapse(&f,n,c,omega,0);fs_assert(&r,ok);r.cases++;if(!ok)continue;
        mpq_set_ui(total,0,1);for(unsigned j=1;j<=n;j++)mpq_add(total,total,c[j]);
        if(kind==FS_IDEMPOTENT){ok=reset_source_collapse(&g,n,f.coefficient[RS_SELECTED],omega,0);fs_assert(&r,ok);}
        if(kind==FS_TOTAL||kind==FS_UNIT_TOTAL){
            fs_assert(&r,mpq_equal(f.total[RS_SELECTED],total));
            for(unsigned d=1;d<=n;d++)fs_assert(&r,mpq_equal(f.coefficient[RS_SELECTED][d],expected[d]));
        }else if(kind==FS_RESET_MASS||kind==FS_UNIT_MASS||kind==FS_MATRIX_MASK){
            for(unsigned k=0;k<=n+2;k++){
                reset_source_mass(a,kind==FS_UNIT_MASS?c:f.coefficient[RS_SELECTED],n,k);fs_mass(b,c,n,k);
                if(kind!=FS_UNIT_MASS && !(k?mpz_divisible_ui_p(omega,k):mpz_sgn(omega)==0))mpq_set_ui(b,0,1);
                if(kind==FS_UNIT_MASS){mpq_set_ui(b,k?n/k:0,1);}
                fs_assert(&r,mpq_equal(a,b));
                if(k<=n&&kind!=FS_UNIT_MASS)fs_assert(&r,mpq_equal(f.mass[RS_SELECTED][k],b));
            }
        }else if(kind==FS_GCD||kind==FS_ROOT_IFF){
            for(unsigned j=1;j<=n;j++){
                unsigned d=f.destination[j];fs_assert(&r,d>=1&&d<=n);
                fs_assert(&r,d==mpz_gcd_ui(NULL,omega,j));
                if(kind==FS_ROOT_IFF)for(unsigned i=1;i<=n;i++)fs_assert(&r,(i==d)==(i==mpz_gcd_ui(NULL,omega,j)));
            }
        }else if(kind==FS_INJECTIVE){
            for(unsigned k=1;k<=n;k++)reset_source_mass(mass[k],f.coefficient[RS_SELECTED],n,k);
            fs_invert(inverse,mass,n);
            for(unsigned j=1;j<=n;j++)fs_assert(&r,mpq_equal(inverse[j],f.coefficient[RS_SELECTED][j]));
        }else for(unsigned d=0;d<=n+2;d++){
            if(d>n)mpq_set_ui(a,0,1);else mpq_set(a,f.coefficient[RS_SELECTED][d]);
            switch(kind){
            case FS_SUPPORT:case FS_OUTSIDE_ROW:
                if(!(d?mpz_divisible_ui_p(omega,d):mpz_sgn(omega)==0))fs_assert(&r,mpq_sgn(a)==0);
                break;
            case FS_NONNEG:fs_assert(&r,mpq_sgn(a)>=0);
                break;
            case FS_UNIT_LE:mpq_set_ui(b,d?n/d:0,1);fs_assert(&r,mpq_cmp(a,b)<=0);
                break;
            case FS_UNIT_GE:if(d&&d<=n&&mpz_divisible_ui_p(omega,d))fs_assert(&r,mpq_cmp_ui(a,1,1)>=0);
                break;
            case FS_IDEMPOTENT:if(d<=n&&ok)fs_assert(&r,mpq_equal(a,g.coefficient[RS_SELECTED][d]));
                break;
            case FS_UNIQUE:
                if(d<=n){fs_mass(b,expected,n,d);fs_assert(&r,mpq_equal(b,f.mass[RS_SELECTED][d]));fs_assert(&r,mpq_equal(a,expected[d]));}break;
            default:if(d<=n)fs_assert(&r,mpq_equal(a,expected[d]));
                break;
            }
        }
    }
    fs_clear_vector(c);fs_clear_vector(expected);fs_clear_vector(mass);fs_clear_vector(inverse);
    mpq_clears(a,b,total,NULL);mpz_clear(omega);reset_source_clear(&f);reset_source_clear(&g);return r;
}

static ContractResult fs_masks(unsigned kind)
{
    static const unsigned cutoffs[]={0,1,2,4,7,12,31,64};
    ContractResult r={0,0,0};ResetSource f,g,h;reset_source_init(&f);reset_source_init(&g);reset_source_init(&h);
    mpq_t c[65],mass[65],b[65],a,t;fs_init_vector(c);fs_init_vector(mass);fs_init_vector(b);mpq_inits(a,t,NULL);
    unsigned char mask[65],tau[65],combo[65];
    for(unsigned ni=0;ni<8;ni++)for(unsigned pattern=0;pattern<5+(cutoffs[ni]<=12?cutoffs[ni]:0);pattern++)for(unsigned mi=0;mi<4;mi++){
        unsigned n=cutoffs[ni];fs_source(c,n,pattern);fs_mask(mask,n,mi);
        if(pattern>=5){fs_source(c,n,0);mpq_set_ui(c[pattern-4],1,1);}
        if(kind==FS_MASK_ONE||kind==FS_MOBIUS_LEFT||kind==FS_MOBIUS_RIGHT||kind==FS_MATRIX_INVERSE||kind==FS_MASK_INJECTIVE)fs_mask(mask,n,1);
        for(unsigned k=1;k<=n;k++){fs_mass(mass[k],c,n,k);if(!mask[k])mpq_set_ui(mass[k],0,1);}
        fs_invert(b,mass,n);
        if(kind==FS_MOBIUS_RIGHT){
            /* Arbitrary desired reset data, then an independent triangular
             * inverse constructs the input to the native reset transform. */
            for(unsigned k=1;k<=n;k++)mpq_set(mass[k],c[k]);
            fs_invert(b,mass,n);
            for(unsigned k=1;k<=n;k++)mpq_set(c[k],b[k]);
        }
        int ok=reset_source_project(&f,n,c,mask,0);fs_assert(&r,ok);r.cases++;if(!ok)continue;
        if(kind==FS_MASK_COMPLEMENT||kind==FS_MASK_ADD||kind==FS_MASK_COMPOSE){
            for(unsigned k=1;k<=n;k++){
                fs_assert(&r,mpq_equal(f.coefficient[RS_SELECTED][k],b[k]));
                fs_assert(&r,mpq_equal(f.mass[RS_SELECTED][k],mass[k]));
            }
        }
        if(kind==FS_MASK_COMPOSE||kind==FS_MASK_ADD){
            for(unsigned k=1;k<=n;k++){
                tau[k]=(unsigned char)(kind==FS_MASK_ADD?(!mask[k]&&k%3==0):(k%3==0));
                combo[k]=(unsigned char)(kind==FS_MASK_ADD?(mask[k]||tau[k]):(mask[k]&&tau[k]));
            }
            ok=reset_source_project(&g,n,kind==FS_MASK_COMPOSE?f.coefficient[RS_SELECTED]:c,tau,0);fs_assert(&r,ok);
            ok=reset_source_project(&h,n,c,combo,0);fs_assert(&r,ok);
        }
        if(kind==FS_MASK_COMPLEMENT){
            for(unsigned k=1;k<=n;k++)tau[k]=(unsigned char)!mask[k];
            ok=reset_source_project(&g,n,c,tau,0);fs_assert(&r,ok);
        }
        for(unsigned k=0;k<=n+2;k++){
            switch(kind){
            case FS_MASS_WEIGHT:case FS_MULTIPLES:case FS_MATRIX_READING:
                reset_source_mass(a,c,n,k);fs_mass(t,c,n,k);fs_assert(&r,mpq_equal(a,t));
                if(k<=n)fs_assert(&r,mpq_equal(a,f.mass[RS_ORIGINAL][k]));
                break;
            case FS_MASK_MASS:case FS_MASK_IDENTITY:case FS_MASK_READING:
                if(k&&k<=n){reset_source_mass(a,f.coefficient[RS_SELECTED],n,k);fs_assert(&r,mpq_equal(a,mass[k]));fs_assert(&r,mpq_equal(a,f.mass[RS_SELECTED][k]));}break;
            case FS_MASK_COMPLEMENT:
                if(k<=n){
                    fs_assert(&r,mpq_equal(f.coefficient[RS_COMPLEMENT][k],g.coefficient[RS_SELECTED][k]));
                    fs_assert(&r,mpq_equal(f.mass[RS_COMPLEMENT][k],g.mass[RS_SELECTED][k]));
                    mpq_add(a,f.coefficient[RS_SELECTED][k],g.coefficient[RS_SELECTED][k]);fs_assert(&r,mpq_equal(a,c[k]));
                    mpq_add(a,f.mass[RS_SELECTED][k],g.mass[RS_SELECTED][k]);fs_assert(&r,mpq_equal(a,f.mass[RS_ORIGINAL][k]));
                }break;
            case FS_MASK_ONE:case FS_MOBIUS_LEFT:case FS_MATRIX_INVERSE:case FS_MASK_INJECTIVE:
                if(k<=n)fs_assert(&r,mpq_equal(f.coefficient[RS_SELECTED][k],c[k]));
                break;
            case FS_MOBIUS_RIGHT:
                if(k<=n){fs_assert(&r,mpq_equal(f.mass[RS_ORIGINAL][k],mass[k]));
                    fs_assert(&r,mpq_equal(f.coefficient[RS_SELECTED][k],b[k]));}
                break;
            case FS_MASK_ADD:
                if(k<=n){mpq_add(a,f.coefficient[RS_SELECTED][k],g.coefficient[RS_SELECTED][k]);fs_assert(&r,mpq_equal(a,h.coefficient[RS_SELECTED][k]));}break;
            case FS_MASK_COMPOSE:
                if(k<=n)fs_assert(&r,mpq_equal(g.coefficient[RS_SELECTED][k],h.coefficient[RS_SELECTED][k]));
                break;
            default:
                if(k<=n){fs_assert(&r,mpq_equal(f.coefficient[RS_SELECTED][k],b[k]));
                    if(kind==FS_MASK_UNIQUE||kind==FS_MASK_MATRIX_UNIQUE){fs_mass(a,b,n,k);fs_assert(&r,mpq_equal(a,mass[k]));}}break;
            }
        }
    }
    fs_clear_vector(c);fs_clear_vector(mass);fs_clear_vector(b);mpq_clears(a,t,NULL);
    reset_source_clear(&f);reset_source_clear(&g);reset_source_clear(&h);return r;
}

static ContractResult fs_columns(void)
{
    static const unsigned cutoffs[]={1,2,4,7,12,31,64};
    ContractResult r={0,0,0};ResetSource f;reset_source_init(&f);
    mpq_t c[65],expected;fs_init_vector(c);mpq_init(expected);mpz_t omega;mpz_init(omega);
    for(unsigned ni=0;ni<7;ni++)for(unsigned oi=0;oi<7;oi++){
        unsigned n=cutoffs[ni];fs_omega(omega,oi);
        for(unsigned j=1;j<=n;j++){
            fs_source(c,n,0);mpq_set_ui(c[j],1,1);
            int ok=reset_source_collapse(&f,n,c,omega,0);fs_assert(&r,ok);r.cases++;if(!ok)continue;
            unsigned destination=(unsigned)mpz_gcd_ui(NULL,omega,j);
            fs_assert(&r,f.destination[j]==destination);
            for(unsigned i=1;i<=n;i++){
                mpq_set_ui(expected,i==destination,1);
                fs_assert(&r,mpq_equal(f.coefficient[RS_SELECTED][i],expected));
            }
        }
    }
    fs_clear_vector(c);mpq_clear(expected);mpz_clear(omega);reset_source_clear(&f);return r;
}

static ContractResult fs_clock_entries(void)
{
    ContractResult r={0,0,0};ResetSource f;reset_source_init(&f);
    mpq_t c[65],primitive,clock;fs_init_vector(c);mpq_inits(primitive,clock,NULL);
    unsigned char mask[65];static const unsigned grids[]={1,2,4,9,25,49};
    for(unsigned n=1;n<=8;n++)for(unsigned qi=0;qi<6;qi++)for(unsigned j=1;j<=n;j++){
        fs_source(c,n,0);mpq_set_ui(c[j],1,1);fs_mask(mask,n,1);
        int ok=reset_source_project(&f,n,c,mask,grids[qi]);fs_assert(&r,ok);r.cases++;if(!ok)continue;
        for(unsigned d=1;d<=n;d++){
            fs_clock(primitive,clock,c,n,grids[qi],d);
            fs_assert(&r,mpq_equal(clock,f.clock_work[d]));
        }
    }
    fs_clear_vector(c);mpq_clears(primitive,clock,NULL);reset_source_clear(&f);return r;
}

static ContractResult fs_work(unsigned kind)
{
    static const unsigned cutoffs[]={0,1,2,3,5,8},grids[]={1,2,4,9,25,49},primes[]={2,3,5,7,11};
    ContractResult r={0,0,0};ResetSource f,g;reset_source_init(&f);reset_source_init(&g);
    mpq_t c[65],b[3][65],m[65],a,t,u,primitive,clock,ordered[3],reset[3],continuous[3],sampled[3];
    fs_init_vector(c);fs_init_vector(m);for(unsigned s=0;s<3;s++)fs_init_vector(b[s]);
    mpq_inits(a,t,u,primitive,clock,NULL);mpz_t omega;mpz_init(omega);
    for(unsigned s=0;s<3;s++)mpq_inits(ordered[s],reset[s],continuous[s],sampled[s],NULL);
    unsigned char mask[65];unsigned ncount=kind==FS_WEIGHTED_IDENTITY?5:6;
    for(unsigned ni=0;ni<ncount;ni++)for(unsigned pattern=0;pattern<5;pattern++)for(unsigned mi=0;mi<4;mi++){
        unsigned n=kind==FS_WEIGHTED_IDENTITY?primes[ni]-1:cutoffs[ni];
        unsigned q=kind==FS_WEIGHTED_IDENTITY?primes[ni]*primes[ni]:grids[(ni+pattern+mi)%6];
        fs_source(c,n,pattern);fs_mask(mask,n,mi);
        int saturated=kind==FS_SATURATED_ORDERED||kind==FS_SATURATED_COEFFICIENTS;
        if(saturated){static const unsigned oms[]={0,2,6,30};mpz_set_ui(omega,oms[mi]);for(unsigned k=1;k<=n;k++)mask[k]=(unsigned char)(mpz_divisible_ui_p(omega,k)!=0);}
        for(unsigned k=1;k<=n;k++){fs_mass(m[k],c,n,k);if(!mask[k])mpq_set_ui(m[k],0,1);}
        fs_invert(b[RS_SELECTED],m,n);
        for(unsigned j=0;j<=64;j++){mpq_set(b[RS_ORIGINAL][j],c[j]);mpq_sub(b[RS_COMPLEMENT][j],c[j],b[RS_SELECTED][j]);}
        int ok=saturated?reset_source_collapse(&f,n,c,omega,q):reset_source_project(&f,n,c,mask,q);fs_assert(&r,ok);r.cases++;if(!ok)continue;
        for(unsigned s=0;s<3;s++){mpq_set_ui(ordered[s],0,1);mpq_set_ui(reset[s],0,1);}
        for(unsigned k=1;k<=n;k++){
            fs_clock(primitive,clock,c,n,q,k);
            if(kind==FS_CLOCK_ENTRY){fs_assert(&r,mpq_equal(clock,f.clock_work[k]));fs_assert(&r,mpq_equal(primitive,f.primitive_work[k]));}
            for(unsigned s=0;s<3;s++){
                fs_scale(t,b[s][k],2,1);mpq_mul(t,t,clock);mpq_add(ordered[s],ordered[s],t);
                fs_mass(t,b[s],n,k);mpq_mul(t,t,primitive);mpq_add(reset[s],reset[s],t);
            }
            if(kind==FS_MASS_INTERVAL){fs_mass(a,b[RS_SELECTED],n,k);fs_assert(&r,mpq_equal(a,f.mass[RS_SELECTED][k]));}
        }
        switch(kind){
        case FS_CONTINUOUS:
            for(unsigned s=0;s<3;s++){fs_integral(continuous[s],b[s],n);fs_assert(&r,mpq_equal(continuous[s],f.energy[RS_CONTINUOUS][s]));}
            mpq_sub(a,continuous[0],continuous[1]);mpq_sub(a,a,continuous[2]);fs_assert(&r,mpq_equal(a,f.mixed[RS_CONTINUOUS]));
                break;
        case FS_SOURCE_COMPLEMENT:
            for(unsigned k=1;k<=n;k++)mask[k]=(unsigned char)!mask[k];
            fs_assert(&r,reset_source_project(&g,n,c,mask,0));
            for(unsigned k=0;k<=n;k++){
                fs_assert(&r,mpq_equal(f.coefficient[2][k],g.coefficient[1][k]));
                fs_assert(&r,mpq_equal(f.coefficient[2][k],b[2][k]));
                mpq_add(a,f.coefficient[1][k],g.coefficient[1][k]);fs_assert(&r,mpq_equal(a,c[k]));
            }break;
        case FS_BOUNDARY_COMPLEMENT:
            for(unsigned s=1;s<3;s++){
                fs_assert(&r,mpq_equal(f.ordered_work[s],ordered[s]));
                fs_assert(&r,mpq_equal(f.reset_work[s],reset[s]));
            }
            mpq_add(a,f.ordered_work[1],f.ordered_work[2]);fs_assert(&r,mpq_equal(a,ordered[0]));
            mpq_add(a,f.reset_work[1],f.reset_work[2]);fs_assert(&r,mpq_equal(a,reset[0]));
                break;
        case FS_CLOCK_ENTRY:case FS_MASS_INTERVAL:break;
        case FS_WEIGHTED_IDENTITY:
            fs_integral(continuous[0],c,n);fs_sample(sampled[0],c,c,n,q);
            fs_assert(&r,mpq_equal(continuous[0],f.energy[0][0]));fs_assert(&r,mpq_equal(sampled[0],f.energy[1][0]));
            fs_assert(&r,mpq_equal(reset[0],f.reset_work[0]));
            mpq_sub(a,f.energy[0][0],f.energy[1][0]);mpq_mul(t,f.total[0],f.total[0]);fs_scale(u,f.reset_work[0],4,1);mpq_add(t,t,u);
            mpq_set_ui(primitive,0,1);mpq_set_ui(clock,0,1);
            for(unsigned j=1;j<=n;j++){fs_scale(u,c[j],j,1);mpq_add(primitive,primitive,u);fs_scale(u,c[j],1,j);mpq_add(clock,clock,u);}
            mpq_mul(u,primitive,clock);fs_scale(u,u,2,3UL*q);mpq_sub(t,t,u);fs_scale(t,t,1,q);fs_assert(&r,mpq_equal(a,t));
                break;
        default:
            for(unsigned s=0;s<3;s++){
                fs_assert(&r,mpq_equal(f.ordered_work[s],ordered[s]));fs_assert(&r,mpq_equal(f.reset_work[s],reset[s]));
                fs_assert(&r,mpq_equal(f.ordered_work[s],reset[s]));
            }break;
        }
    }
    fs_clear_vector(c);fs_clear_vector(m);for(unsigned s=0;s<3;s++){fs_clear_vector(b[s]);mpq_clears(ordered[s],reset[s],continuous[s],sampled[s],NULL);}
    mpq_clears(a,t,u,primitive,clock,NULL);mpz_clear(omega);reset_source_clear(&f);reset_source_clear(&g);return r;
}

static ContractResult fs_sampled_entries(void)
{
    ContractResult r={0,0,0};ResetSource f,g,h;reset_source_init(&f);reset_source_init(&g);reset_source_init(&h);
    mpq_t c[65],e[65],sum[65],a,b;fs_init_vector(c);fs_init_vector(e);fs_init_vector(sum);mpq_inits(a,b,NULL);
    unsigned char mask[65];static const unsigned grids[]={1,2,4,9,25,49};
    for(unsigned n=1;n<=8;n++)for(unsigned qi=0;qi<6;qi++)for(unsigned i=1;i<=n;i++)for(unsigned j=i;j<=n;j++){
        unsigned q=grids[qi];fs_source(c,n,0);fs_source(e,n,0);fs_source(sum,n,0);fs_mask(mask,n,1);
        mpq_set_ui(c[i],1,1);mpq_set_ui(e[j],1,1);mpq_add(sum[i],sum[i],c[i]);mpq_add(sum[j],sum[j],e[j]);
        int ok=reset_source_project(&f,n,c,mask,q)&&reset_source_project(&g,n,e,mask,q)&&reset_source_project(&h,n,sum,mask,q);fs_assert(&r,ok);r.cases++;if(!ok)continue;
        fs_sample(a,c,e,n,q);fs_scale(a,a,q,1); /* The sampled Gram convention here is an unnormalized sum. */
        mpq_sub(b,h.energy[RS_SAMPLED][0],f.energy[RS_SAMPLED][0]);mpq_sub(b,b,g.energy[RS_SAMPLED][0]);fs_scale(b,b,q,2);
        fs_assert(&r,mpq_equal(a,b));
    }
    fs_clear_vector(c);fs_clear_vector(e);fs_clear_vector(sum);mpq_clears(a,b,NULL);reset_source_clear(&f);reset_source_clear(&g);reset_source_clear(&h);return r;
}

static ContractResult fs_seed(unsigned kind)
{
    ContractResult r={0,0,0};ResetSource f;reset_source_init(&f);mpq_t c[65],expected,a,b,primitive,clock;
    fs_init_vector(c);mpq_inits(expected,a,b,primitive,clock,NULL);fs_source(c,30,1);unsigned char mask[65]={0};
    unsigned ks[]={23,22,19,24,20},start=0,end=5;long num=0;unsigned den=1;
    switch(kind){
    case FS_SEED_CLOCK23_WORK:end=1;num=-12;
                break;
    case FS_SEED_CLOCK22_WORK:start=1;end=2;num=-32;den=11;
                break;
    case FS_SEED_CLOCK19_WORK:start=2;end=3;num=-12;den=19;
                break;
    case FS_SEED_CLOCK24_WORK:start=3;end=4;num=53;den=3;
                break;
    case FS_SEED_CLOCK20_WORK:start=4;end=5;num=112;den=5;
                break;
    case FS_SEED_PACKET_COHERENT_WORK:case FS_SEED_NATIVE_PACKET_WORK:end=3;num=-3248;den=209;
                break;
    case FS_SEED_FRINGE_COHERENT_WORK:case FS_SEED_NATIVE_FRINGE_WORK:start=3;num=601;den=15;
                break;
    default:num=76889;den=3135;
                break;
    }
    for(unsigned i=start;i<end;i++)mask[ks[i]]=1;
    int ok=reset_source_project(&f,30,c,mask,961);fs_assert(&r,ok);r.cases=1;
    if(ok){
        mpq_set_si(expected,num,den);mpq_canonicalize(expected);fs_scale(a,f.reset_work[RS_SELECTED],4,1);fs_assert(&r,mpq_equal(a,expected));
        mpq_set_ui(b,0,1);for(unsigned i=start;i<end;i++){unsigned k=ks[i];fs_clock(primitive,clock,c,30,961,k);fs_scale(primitive,primitive,4L*(30/k),1);mpq_add(b,b,primitive);}
        fs_assert(&r,mpq_equal(b,expected));
    }
    fs_clear_vector(c);mpq_clears(expected,a,b,primitive,clock,NULL);reset_source_clear(&f);return r;
}

static ContractResult forest_source_run(unsigned kind)
{
    if(kind>=FS_SEED_CLOCK23_WORK)return fs_seed(kind);
    if(kind==FS_SAMPLED_ENTRY)return fs_sampled_entries();
    if(kind==FS_COLUMN||kind==FS_SATURATED_COLUMN)return fs_columns();
    if(kind==FS_CLOCK_ENTRY)return fs_clock_entries();
    if(kind>=FS_ORDERED)return fs_work(kind);
    if(kind>=FS_MASS_WEIGHT&&kind<=FS_MASK_MATRIX_UNIQUE)return fs_masks(kind);
    return fs_coordinates(kind);
}
