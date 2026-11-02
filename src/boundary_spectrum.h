#ifndef NFIELD_BOUNDARY_SPECTRUM_H
#define NFIELD_BOUNDARY_SPECTRUM_H
#include "finite_character_core.h"
#include <complex.h>
/* Any complex cell weights, modulus 2..512, each component |w|<=1000.
 * Integer phases/conductors are exact. Transforms use long-double complex
 * arithmetic; diagnostics use 5e-9 times the larger energy/magnitude scale.
 * Initialize out to zero; failures preserve it. Nonunits are retained in F
 * but excluded from ordinary character flux and its reconstruction. */
typedef struct {
    FiniteCharacterTable characters;
    long double complex *boundary,*response,*flux,*transform,*factored;
    long double *conductor_energy;
    long double direct_energy, spectral_energy, ordinary_flux_energy;
    long double primitive_error, depth_error, inversion_error, energy_error;
    long double boundary_pairing_error, unit_reconstruction_error;
    int prime_power, depth_channels, primitive_channels;
} BoundarySpectrum;
int boundary_spectrum_build(unsigned modulus,const long double complex *weights,
    unsigned count,BoundarySpectrum *out);
void boundary_spectrum_free(BoundarySpectrum *out);
int boundary_spectrum_command(int argc,char **argv);
int boundary_spectrum_verify(void);
void boundary_spectrum_help(void);
#endif
