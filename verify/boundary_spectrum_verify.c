#include "../src/boundary_spectrum.h"
#include <stdio.h>
#include <math.h>

static unsigned gcd(unsigned a,unsigned b)
{ while(b) { unsigned t=a%b;a=b;b=t;}return a; }
int boundary_spectrum_verify(void)
{
    unsigned checks=0,failures=0;
#define CHECK(c) do { checks++; if(!(c)) { failures++; \
    fprintf(stderr,"boundary-spectrum check failed at line %d\n",__LINE__); } } while(0)
    for(unsigned m=2;m<=64;m++) {
        FiniteCharacterTable t={0}; CHECK(finite_character_table_build(m,&t));
        for(int ch=0;ch<t.count;ch++) {
            for(unsigned a=0;a<m;a++) {
                int pa=t.phase[(size_t)ch*m+a]; CHECK((pa<0)==(gcd(a,m)!=1));
                if(pa<0) continue;
                for(unsigned b=1;b<m;b++) if(gcd(b,m)==1) {
                    int pb=t.phase[(size_t)ch*m+b];
                    CHECK((pa+pb)%t.denominator==t.phase[(size_t)ch*m+(a*b)%m]);
                }
            }
            CHECK(t.conductor[ch]>0 && m%(unsigned)t.conductor[ch]==0);
            for(int other=0;other<ch;other++) {
                int distinct=0; for(unsigned a=1;a<m;a++)
                    if(t.phase[(size_t)ch*m+a]!=t.phase[(size_t)other*m+a]) distinct=1;
                CHECK(distinct);
            }
        }
        finite_character_table_free(&t);
        long double complex w[64];
        for(unsigned i=0;i<m;i++) w[i]=((int)(i%5)-2)+I*((int)(i%3)-1);
        BoundarySpectrum z={0}; CHECK(boundary_spectrum_build(m,w,m,&z));
        CHECK(z.primitive_error<5e-9L && z.depth_error<5e-9L);
        CHECK(z.inversion_error<5e-9L && z.unit_reconstruction_error<5e-9L);
        CHECK(z.energy_error<5e-9L && z.boundary_pairing_error<5e-9L);
        long double complex total=0;
        for(unsigned a=0;a<m;a++) total+=z.boundary[a];
        CHECK(cabsl(total)<1e-12L);
        for(int ch=0;ch<z.characters.count;ch++) if(!z.characters.odd[ch])
            CHECK(cabsl(z.transform[ch])<5e-9L);
        boundary_spectrum_free(&z);
    }
    for(unsigned m=125;m<=512;m+=129) {
        long double complex w[512]={0}; w[0]=1;w[m/2]=1;
        BoundarySpectrum z={0}; CHECK(boundary_spectrum_build(m,w,m,&z));
        CHECK(z.primitive_error<5e-9L && z.depth_error<5e-9L && z.energy_error<5e-9L);
        boundary_spectrum_free(&z);
    }
    long double complex nine[9]={1,0,0,0,1,0,0,0,1}; BoundarySpectrum z={0};
    CHECK(boundary_spectrum_build(9,nine,9,&z));
    CHECK(fabsl(z.direct_energy-16.0L/3)<1e-12L);
    CHECK(fabsl(z.conductor_energy[3])<1e-12L && fabsl(z.conductor_energy[9]-16.0L/3)<1e-12L);
    boundary_spectrum_free(&z);
    long double complex six[6]={1,1,0,0,0,0};
    CHECK(boundary_spectrum_build(6,six,6,&z));
    CHECK(cabsl(z.flux[1])<1e-12L && cabsl(z.transform[1]-1.0L/3)<1e-12L);
    boundary_spectrum_free(&z);
    CHECK(!boundary_spectrum_build(1,nine,9,&z));
    CHECK(!boundary_spectrum_build(513,nine,9,&z));
    CHECK(!boundary_spectrum_build(9,nine,8,&z));
    nine[0]=NAN; CHECK(!boundary_spectrum_build(9,nine,9,&z));
    CHECK(!z.boundary && !z.characters.phase);
    printf("Boundary spectrum verification: %u checks, %u failures\n",checks,failures);
    puts("Exact unit-group phases and conductors; numerical complex transforms at tolerance 5e-9.\n"
         "Includes composite and noncyclic groups, complex weights and induced nonunit response.");
    return failures==0;
#undef CHECK
}
