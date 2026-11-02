#include "boundary_spectrum.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <errno.h>
#include <limits.h>

static unsigned bs_gcd(unsigned a,unsigned b)
{ while(b) { unsigned t=a%b;a=b;b=t; }return a; }
static long double bs_saw(unsigned r,unsigned m)
{ r%=m; return r?(long double)r/m-0.5L:0; }
static unsigned bs_power(unsigned m,unsigned *depth)
{
    unsigned p=2; while(p<=m/p && m%p) p++;
    if(m%p) p=m;
    *depth=0; while(m%p==0) { m/=p;(*depth)++; }
    return m==1?p:0;
}
void boundary_spectrum_free(BoundarySpectrum *out)
{
    if(!out) return;
    finite_character_table_free(&out->characters);
    free(out->boundary); free(out->response); free(out->flux);
    free(out->transform); free(out->factored); free(out->conductor_energy);
    memset(out,0,sizeof *out);
}
static long double complex bs_lift(const FiniteCharacterTable *t,unsigned ch,
                                    unsigned q,unsigned r)
{
    r%=q; if(bs_gcd(r,q)!=1) return 0;
    for(unsigned a=r;a<(unsigned)t->modulus;a+=q) if(bs_gcd(a,t->modulus)==1)
        return finite_character_table_value(t,ch,a);
    return 0;
}
static long double complex bs_eta(const FiniteCharacterTable *t,unsigned ch,
    unsigned q,unsigned p,unsigned depth,unsigned x)
{
    if(!x) return 0;
    unsigned v=0,scale=1,qdepth=0,copy=q;
    while(copy>1) { copy/=p; qdepth++; }
    while(x%p==0) { x/=p; scale*=p; v++; }
    return v<=depth-qdepth?scale*bs_lift(t,ch,q,x):0;
}
int boundary_spectrum_build(unsigned m,const long double complex *weights,
                             unsigned count,BoundarySpectrum *out)
{
    if(!weights || !out || out->boundary || out->characters.phase || m<2 ||
       m>FINITE_CHARACTER_TABLE_MAX_MODULUS || count!=m) return 0;
    for(unsigned i=0;i<m;i++) if(!isfinite(creall(weights[i])) ||
       !isfinite(cimagl(weights[i])) || cabsl(weights[i])>1000) return 0;
    BoundarySpectrum z={0};
    if(!finite_character_table_build((int)m,&z.characters)) return 0;
    unsigned phi=(unsigned)z.characters.count,depth;
    unsigned p=bs_power(m,&depth); z.prime_power=(int)p;
    z.boundary=calloc(m,sizeof *z.boundary); z.response=calloc(m,sizeof *z.response);
    z.flux=calloc(phi,sizeof *z.flux); z.transform=calloc(phi,sizeof *z.transform);
    z.factored=calloc(phi,sizeof *z.factored); z.conductor_energy=calloc(m+1,sizeof *z.conductor_energy);
    if(!z.boundary||!z.response||!z.flux||!z.transform||!z.factored||!z.conductor_energy) goto fail;
    for(unsigned x=0;x<m;x++) z.boundary[x]=weights[(x+m-1)%m]-weights[x];
    for(unsigned a=0;a<m;a++) {
        long double complex pairing=0;
        for(unsigned x=0;x<m;x++) {
            z.response[a]-=weights[x]*(bs_saw(((x+1)*a)%m,m)-bs_saw((x*a)%m,m));
            pairing-=z.boundary[x]*bs_saw((x*a)%m,m);
        }
        long double error=cabsl(pairing-z.response[a]);
        if(error>z.boundary_pairing_error) z.boundary_pairing_error=error;
        if(bs_gcd(a,m)==1) {
            z.direct_energy+=creall(z.response[a]*conjl(z.response[a]));
            z.ordinary_flux_energy+=creall(z.boundary[a]*conjl(z.boundary[a]));
        }
    }
    for(unsigned ch=0;ch<phi;ch++) {
        unsigned q=(unsigned)z.characters.conductor[ch];
        long double complex bernoulli=0,depth_flux=0;
        for(unsigned a=0;a<m;a++) {
            long double complex value=finite_character_table_value(&z.characters,ch,a);
            z.flux[ch]+=z.boundary[a]*value;
            z.transform[ch]+=z.response[a]*conjl(value);
            if(q==m) bernoulli+=bs_saw(a,m)*conjl(value);
        }
        if(q==m) {
            z.factored[ch]=-bernoulli*z.flux[ch]; z.primitive_channels++;
            long double error=cabsl(z.factored[ch]-z.transform[ch]);
            if(error>z.primitive_error) z.primitive_error=error;
        } else if(p && q>1) {
            for(unsigned a=1;a<q;a++) if(bs_gcd(a,q)==1)
                bernoulli+=bs_saw(a,q)*conjl(bs_lift(&z.characters,ch,q,a));
            for(unsigned x=0;x<m;x++)
                depth_flux+=z.boundary[x]*bs_eta(&z.characters,ch,q,p,depth,x);
            z.factored[ch]=-bernoulli*depth_flux; z.depth_channels++;
            long double error=cabsl(z.factored[ch]-z.transform[ch]);
            if(error>z.depth_error) z.depth_error=error;
        }
        long double energy=creall(z.transform[ch]*conjl(z.transform[ch]))/phi;
        z.spectral_energy+=energy; z.conductor_energy[q]+=energy;
    }
    for(unsigned a=0;a<m;a++) if(bs_gcd(a,m)==1) {
        long double complex f=0,mu=0;
        for(unsigned ch=0;ch<phi;ch++) {
            long double complex value=finite_character_table_value(&z.characters,ch,a);
            f+=z.transform[ch]*value/phi; mu+=z.flux[ch]*conjl(value)/phi;
        }
        long double error=cabsl(f-z.response[a]); if(error>z.inversion_error) z.inversion_error=error;
        error=cabsl(mu-z.boundary[a]); if(error>z.unit_reconstruction_error) z.unit_reconstruction_error=error;
    }
    z.energy_error=fabsl(z.direct_energy-z.spectral_energy); *out=z; return 1;
fail:
    boundary_spectrum_free(&z); return 0;
}
static int bs_number(const char *s,unsigned *out)
{
    if(!s||!*s) return 0;
    for(const char *c=s;*c;c++) if(*c<'0'||*c>'9') return 0;
    errno=0; char *end; unsigned long x=strtoul(s,&end,10);
    if(errno||*end||x>UINT_MAX) return 0;
    *out=(unsigned)x; return 1;
}
static int bs_support(const char *s,unsigned m,long double complex *w)
{
    if(!strcmp(s,"none")) return 1;
    while(*s) {
        const char *end=strchr(s,','); size_t n=end?(size_t)(end-s):strlen(s);
        char token[16]; unsigned x;
        if(!n||n>=sizeof token) return 0;
        memcpy(token,s,n); token[n]=0;
        if(!bs_number(token,&x)||x>=m||creall(w[x])!=0) return 0;
        w[x]=1; if(!end) return 1; s=end+1; if(!*s) return 0;
    }
    return 0;
}
static int bs_weights(const char *s,unsigned m,long double complex *w)
{
    unsigned char seen[FINITE_CHARACTER_TABLE_MAX_MODULUS]={0};
    if(!strcmp(s,"none")) return 1;
    while(*s) {
        const char *end=strchr(s,','); size_t n=end?(size_t)(end-s):strlen(s);
        char token[128]; unsigned x; if(!n||n>=sizeof token) return 0;
        memcpy(token,s,n); token[n]=0; char *eq=strchr(token,'=');
        if(!eq) return 0;
        *eq=0; if(!bs_number(token,&x)||x>=m||seen[x]) return 0;
        seen[x]=1; char *colon=strchr(eq+1,':'); if(!colon) return 0;
        *colon=0; char *stop; errno=0; long double re=strtold(eq+1,&stop);
        if(errno||stop==eq+1||*stop||!isfinite(re)) return 0;
        errno=0; long double im=strtold(colon+1,&stop);
        if(errno||stop==colon+1||*stop||!isfinite(im)) return 0;
        w[x]=re+I*im; if(cabsl(w[x])>1000) return 0;
        if(!end) return 1;
        s=end+1; if(!*s) return 0;
    }
    return 0;
}
void boundary_spectrum_help(void)
{
    puts("Boundary spectrum on a complete unit group\n\n"
         "  nfield boundary-spectrum inspect <modulus> --support <cells|none>\n"
         "  nfield boundary-spectrum channel <modulus> <index> --support <cells|none>\n"
         "  Replace --support by --weights <cell=real:imag,...> for signed or complex weights.\n"
         "  nfield boundary-spectrum verify\n\n"
         "Moduli 2..512, including composite and noncyclic unit groups.\n"
         "Character indices use mixed-radix CRT coordinates. Integer phases,\n"
         "parities, conductors and support are exact. Complex transforms and\n"
         "energies use long-double arithmetic, not a rounding enclosure.\n"
         "Primitive factorization is checked at every modulus. Induced depth\n"
         "factorization is checked at prime powers; at other composite moduli\n"
         "the direct transform is reported without a false ordinary-flux factorization.\n"
         "The library also accepts arbitrary bounded complex cell weights.");
}
int boundary_spectrum_command(int argc,char **argv)
{
    if(!argc || (argc==1 && (!strcmp(argv[0],"help")||!strcmp(argv[0],"--help")))) {
        boundary_spectrum_help(); return 0;
    }
    if(argc==1&&!strcmp(argv[0],"verify")) return !boundary_spectrum_verify();
    unsigned m,ch=0; int channel=argc==5&&!strcmp(argv[0],"channel");
    if((!channel && (argc!=4||strcmp(argv[0],"inspect"))) || !bs_number(argv[1],&m) ||
       m<2||m>FINITE_CHARACTER_TABLE_MAX_MODULUS || (channel&&!bs_number(argv[2],&ch)) ||
       (strcmp(argv[argc-2],"--support") && strcmp(argv[argc-2],"--weights"))) goto bad;
    long double complex w[FINITE_CHARACTER_TABLE_MAX_MODULUS]={0};
    if(!strcmp(argv[argc-2],"--support")) { if(!bs_support(argv[argc-1],m,w)) goto bad; }
    else if(!bs_weights(argv[argc-1],m,w)) goto bad;
    BoundarySpectrum z={0}; if(!boundary_spectrum_build(m,w,m,&z)) goto bad;
    if(channel && ch>=(unsigned)z.characters.count) { boundary_spectrum_free(&z); goto bad; }
    printf("modulus=%u\ncharacters=%d\n",m,z.characters.count);
    if(channel) {
        printf("index=%u\nconductor=%d\nodd=%u\n",ch,z.characters.conductor[ch],z.characters.odd[ch]);
        printf("flux_real=%.18Lg\nflux_imag=%.18Lg\ntransform_real=%.18Lg\ntransform_imag=%.18Lg\n",
            creall(z.flux[ch]),cimagl(z.flux[ch]),creall(z.transform[ch]),cimagl(z.transform[ch]));
        printf("factored_available=%d\n",z.characters.conductor[ch]==(int)m || (z.prime_power && z.characters.conductor[ch]>1));
        if(z.characters.conductor[ch]==(int)m || (z.prime_power && z.characters.conductor[ch]>1))
            printf("factored_real=%.18Lg\nfactored_imag=%.18Lg\n",creall(z.factored[ch]),cimagl(z.factored[ch]));
    } else {
        printf("direct_energy=%.18Lg\nspectral_energy=%.18Lg\nordinary_flux_energy=%.18Lg\n",
            z.direct_energy,z.spectral_energy,z.ordinary_flux_energy);
        printf("primitive_channels=%d\ndepth_channels=%d\nprimitive_error=%.6Lg\ndepth_error=%.6Lg\ninversion_error=%.6Lg\nunit_reconstruction_error=%.6Lg\nenergy_error=%.6Lg\nboundary_pairing_error=%.6Lg\n",
            z.primitive_channels,z.depth_channels,z.primitive_error,z.depth_error,
            z.inversion_error,z.unit_reconstruction_error,z.energy_error,z.boundary_pairing_error);
        for(unsigned q=1;q<=m;q++) if(m%q==0)
            printf("conductor_%u_energy=%.18Lg\n",q,z.conductor_energy[q]);
    }
    boundary_spectrum_free(&z); return 0;
bad:
    fputs("Invalid boundary-spectrum action or parameters; see boundary-spectrum help.\n",stderr); return 1;
}
