#ifndef NFIELD_COLLISION_SAMPLING_H
#define NFIELD_COLLISION_SAMPLING_H

#include <gmp.h>
#include <complex.h>

/* Exact finite sampling and carrier calculus. All rational outputs must be
 * initialized by the caller. Invalid input leaves them unchanged. Structs
 * below must be initialized/cleared with the matching functions. Bounds are
 * computational limits, not restrictions on the manuscript identities. */
#define COLLISION_SAMPLING_MAX_PRIME 251u
#define COLLISION_SAMPLING_MAX_MODULUS 512u

enum {
    CS_CAPACITY, CS_SAMPLED, CS_DEFECT, CS_ENDPOINT, CS_X, CS_RESERVOIR,
    CS_ALIAS_A, CS_ALIAS_C, CS_X_TERM, CS_RESERVOIR_TERM,
    CS_ALIAS_A_TERM, CS_ALIAS_C_TERM, CS_BRIDGE, CS_ALIAS,
    CS_BRIDGE_ERROR, CS_ALIAS_ERROR, CS_FIELD_COUNT
};
typedef struct { mpq_t value[CS_FIELD_COUNT]; } CollisionSampling;
extern const char *const collision_sampling_names[CS_FIELD_COUNT];
void collision_sampling_init(CollisionSampling *out);
void collision_sampling_clear(CollisionSampling *out);
int collision_sampling_q(CollisionSampling *out, unsigned prime);
/* Exact E_p/p^2 from the original digit-floor count, for odd primes<=10007.
 * This larger range does not extend the full carrier-ledger range above. */
int collision_sampling_energy_q(mpq_t sampled, unsigned prime);

enum { CSP_DIAGONAL, CSP_OFF_DIAGONAL, CSP_MAIN, CSP_R0, CSP_RA, CSP_RK,
       CSP_FOUR_WAY_ERROR, CSP_ENERGY_ERROR, CSP_FIELD_COUNT };
typedef struct { mpq_t value[CSP_FIELD_COUNT]; } CollisionPoles;
extern const char *const collision_poles_names[CSP_FIELD_COUNT];
void collision_poles_init(CollisionPoles *out);
void collision_poles_clear(CollisionPoles *out);
int collision_sampling_poles_q(CollisionPoles *out, unsigned prime);
/* Normalized absolute and signed square-lock masses, counting only carriers
 * 0<|c_p(k)|<=C. The origin and k=1 never enter. Distinct initialized outputs. */
int collision_sampling_collar_q(mpq_t absolute, mpq_t signed_mass,
    unsigned prime, unsigned displacement_cutoff);

/* Extended Dedekind sum at every slope. Modulus 1..251^2. Slope is reduced
 * before products; h=0 is allowed. Reciprocity and gcd descent are exact. */
int collision_sampling_dedekind_q(mpq_t out, unsigned modulus,
                                  unsigned long long slope);
int collision_sampling_capacity_q(mpq_t out, unsigned cutoff);
/* Carrier k=1..p-1. The first two outputs are its X and R^(k) contributions;
 * the latter two include floor((p-1)/k), but not the curvature at the origin.
 * Outputs must be distinct. The modulus-one reservoir and jump terms are 0. */
int collision_sampling_carrier_q(mpq_t x, mpq_t reservoir,
    mpq_t alias_a, mpq_t alias_c, unsigned prime, unsigned carrier);
/* Delta_{k,p}(X), including complete blocks, with 2<=k<p and 0<=X<=p-1. */
int collision_sampling_prefix_q(mpq_t out, unsigned prime,
                                  unsigned carrier, unsigned cutoff);
/* V_{k,s}(c) at any residue c, including nonunits and 0. */
int collision_sampling_correlation_q(mpq_t out, unsigned modulus,
    unsigned prefix, unsigned long long slope);

enum {
    CSS_RESERVOIR, CSS_DWELL_AREA, CSS_FRESH_AREA, CSS_ENERGY,
    CSS_INCREMENT_ENERGY, CSS_CHARGE, CSS_RELEASE, CSS_MEAN,
    CSS_COHERENT_ENERGY, CSS_VARIANCE, CSS_TRIANGLE, CSS_TRIANGLE_BRIDGE,
    CSS_FIELD_COUNT
};
typedef struct { mpq_t value[CSS_FIELD_COUNT]; } CollisionSwitching;
extern const char *const collision_switching_names[CSS_FIELD_COUNT];
void collision_switching_init(CollisionSwitching *out);
void collision_switching_clear(CollisionSwitching *out);
/* mask is NULL for every carrier, otherwise exactly p entries, each 0 or 1,
 * supported in 2..p-2. The triangle fields describe the full carrier set
 * independently of mask. They are never presented as its selected reservoir. */
int collision_sampling_switching_q(CollisionSwitching *out, unsigned prime,
                                      const unsigned char *mask, unsigned length);
int collision_sampling_state_q(mpq_t burden, mpq_t fresh, unsigned prime,
    unsigned state, const unsigned char *mask, unsigned length);
/* C_m(X), A_m(X), and E_p(X). X=1 is zero; E_p is defined only for X>=3
 * and is reported as zero at 1,2. Includes the essential X=2 diagonal. */
int collision_sampling_convolution_q(mpq_t primitive, mpq_t full,
    mpq_t elementary, unsigned prime, unsigned state);

/* Finite additive Fourier transforms use long-double complex arithmetic.
 * Underlying Dedekind values and inverse prefixes are exact rationals.
 * errors compare independent finite representations; they are diagnostics,
 * not interval certificates for libm rounding. Moduli 2..512. */
typedef struct {
    long double complex full, unit, full_from_inverse, unit_from_mobius;
    long double inverse_series, inverse_from_descent;
    long double full_error, unit_error, descent_error;
} CollisionInverseTransform;
int collision_sampling_transform(CollisionInverseTransform *out,
    unsigned modulus, unsigned long long frequency);
/* X<=4096; returns the unweighted inverse prefix, its harmonic prefix,
 * and the rigorous absolute bound q/(2(X+1)) for the remaining series.
 * The three outputs must be distinct. No numerical completion is assumed. */
int collision_sampling_inverse_q(mpq_t prefix, mpq_t harmonic, mpq_t tail_bound,
    unsigned modulus, unsigned long long frequency, unsigned cutoff);

int collision_sampling_command(int argc, char **argv);
int collision_sampling_verify(void);
void collision_sampling_help(void);
#endif
