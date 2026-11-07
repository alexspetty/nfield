/* C caller-contract tests for sampling, spectra and kernels. */
#include "../src/collision_sampling.h"
#include "../src/boundary_spectrum.h"
#include "../src/collision_kernel_readout.h"
#include <stdio.h>
#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

int main(int argc,char **argv)
{
    if(argc==3&&!strcmp(argv[1],"table")) {
        FiniteCharacterTable table={0}; int m=atoi(argv[2]);
        if(!finite_character_table_build(m,&table)) return 1;
        puts("character,conductor,odd,denominator,phases");
        for(int ch=0;ch<table.count;ch++) {
            printf("%d,%d,%u,%d,",ch,table.conductor[ch],table.odd[ch],table.denominator);
            for(int a=0;a<m;a++) printf("%s%d",a?":":"",table.phase[(size_t)ch*m+a]);
            putchar('\n');
        }
        finite_character_table_free(&table); return 0;
    }
    if(argc!=1) return 1;
    unsigned checks=0,failed=0;
#define CHECK(c) do { checks++; if(!(c)) { failed++; fprintf(stderr,"caller-contract failure at %d\n",__LINE__); } } while(0)
    mpq_t a,b,c,d; mpq_inits(a,b,c,d,NULL); mpq_set_si(a,-13,7);
    mpq_set(b,a);mpq_set(c,a);mpq_set(d,a);
    CHECK(!collision_sampling_capacity_q(a,UINT_MAX)&&mpq_equal(a,b));
    CHECK(!collision_sampling_energy_q(a,10009)&&mpq_equal(a,b));
    CHECK(!collision_sampling_energy_q(a,15)&&mpq_equal(a,b));
    CHECK(!collision_sampling_dedekind_q(a,UINT_MAX,ULLONG_MAX)&&mpq_equal(a,b));
    CHECK(collision_sampling_dedekind_q(a,31,ULLONG_MAX));
    CHECK(collision_sampling_dedekind_q(b,31,ULLONG_MAX%31)&&mpq_equal(a,b));
    CHECK(collision_sampling_correlation_q(a,31,7,ULLONG_MAX));
    CHECK(collision_sampling_correlation_q(b,31,7,ULLONG_MAX%31)&&mpq_equal(a,b));
    mpq_set(b,a);
    CHECK(!collision_sampling_carrier_q(a,a,c,d,7,3)&&mpq_equal(a,b));
    CHECK(!collision_sampling_state_q(a,a,7,3,NULL,0)&&mpq_equal(a,b));
    CHECK(!collision_sampling_convolution_q(a,a,c,7,3)&&mpq_equal(a,b));
    CHECK(!collision_sampling_inverse_q(a,a,c,7,3,4)&&mpq_equal(a,b));
    CHECK(!collision_sampling_inverse_q(a,c,d,7,3,4097)&&mpq_equal(a,b));
    CHECK(!collision_sampling_collar_q(a,a,7,2)&&mpq_equal(a,b));
    CollisionSampling z; collision_sampling_init(&z);
    mpq_set_si(z.value[0],-13,7);
    CHECK(!collision_sampling_q(&z,UINT_MAX)&&mpq_cmp_si(z.value[0],-13,7)==0);
    CHECK(!collision_sampling_q(NULL,7)); collision_sampling_clear(&z);
    CollisionSwitching sw; collision_switching_init(&sw);
    unsigned char mask[7]={0,0,1,0,1,0,0};
    CHECK(collision_sampling_switching_q(&sw,7,mask,7));
    mpq_set(a,sw.value[0]);mask[0]=1;
    CHECK(!collision_sampling_switching_q(&sw,7,mask,7)&&mpq_equal(a,sw.value[0]));
    CHECK(!collision_sampling_switching_q(&sw,7,mask,6)); collision_switching_clear(&sw);
    long double complex weights[16]={1,2*I,0,-1};BoundarySpectrum spectrum={0};
    CHECK(boundary_spectrum_build(16,weights,16,&spectrum));
    void *pointer=spectrum.boundary;
    CHECK(!boundary_spectrum_build(16,weights,16,&spectrum)&&spectrum.boundary==pointer);
    boundary_spectrum_free(&spectrum); boundary_spectrum_free(&spectrum);
    weights[0]=INFINITY;
    CHECK(!boundary_spectrum_build(16,weights,16,&spectrum)&&!spectrum.boundary);
    weights[0]=1001;
    CHECK(!boundary_spectrum_build(16,weights,16,&spectrum)&&!spectrum.boundary);
    weights[0]=1;
    CHECK(!boundary_spectrum_build(16,weights,15,&spectrum));
    FiniteCharacterTable table={0}; CHECK(finite_character_table_build(2,&table));
    CHECK(table.count==1&&table.phase[0]==-1&&table.phase[1]==0&&table.conductor[0]==1);
    CHECK(!finite_character_table_build(2,&table));finite_character_table_free(&table);
    CHECK(!finite_character_table_build(513,&table)&&!table.phase);
    CollisionKernelSeed seed;collision_kernel_seed_init(&seed);mpq_set_si(seed.value[0],-13,7);
    CHECK(!collision_kernel_seed_q(&seed,241,1)&&mpq_cmp_si(seed.value[0],-13,7)==0);
    CHECK(!collision_kernel_seed_q(&seed,2,121));collision_kernel_seed_clear(&seed);
    mpq_set_ui(d,1,1);
    CHECK(!collision_kernel_profile_q(a,a,c,d,NULL,0,7));
    CHECK(!collision_kernel_profile_q(a,b,c,d,NULL,1,7));
    CHECK(!collision_kernel_profile_q(a,b,c,d,NULL,0,121));
    CHECK(!collision_kernel_lattice_q(a,a,c,d,4));
    CHECK(!collision_kernel_lattice_q(a,b,c,d,65));
    mpq_set_si(d,-1,2);CHECK(!collision_kernel_lattice_q(a,b,c,d,4));
    CollisionCarryMeasurement measurement;collision_measurement_init(&measurement);
    mpq_set_si(measurement.value[0],-13,7);
    CHECK(!collision_kernel_measurement_q(&measurement,5,1,4,2,d)&&mpq_cmp_si(measurement.value[0],-13,7)==0);
    CHECK(!collision_kernel_measurement_q(&measurement,129,1,1,2,d));
    CHECK(!collision_kernel_measurement_q(&measurement,5,1,1,14,d));
    collision_measurement_clear(&measurement);
    mpq_clears(a,b,c,d,NULL);
    printf("Sampling and spectrum C caller contracts: %u checks, %u failures\n",checks,failed);
    return failed?1:0;
#undef CHECK
}
