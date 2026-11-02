#ifndef NFIELD_COLLISION_KERNEL_READOUT_H
#define NFIELD_COLLISION_KERNEL_READOUT_H
#include <gmp.h>
/* Exact finite readouts of the homogeneous kernel. Resource limits 1..120
 * for profile periods and q*length<=240 for the positive seed. Initialized,
 * distinct outputs are required. Failure preserves the outputs. */
enum { CK_B0, CK_B0_INVERSE, CK_F_LOWER, CK_F_UPPER, CK_ETA_LOWER, CK_ETA_UPPER,
       CK_SELECTOR_LOWER, CK_SELECTOR_UPPER, CK_ZETA_LOWER, CK_ZETA_UPPER, CK_COUNT };
typedef struct { mpq_t value[CK_COUNT]; } CollisionKernelSeed;
extern const char *const collision_kernel_seed_names[CK_COUNT];
void collision_kernel_seed_init(CollisionKernelSeed *out);
void collision_kernel_seed_clear(CollisionKernelSeed *out);
/* Bounds enclose the actual infinite positive sums, using a harmonic
 * majorant and integral comparison. They do not prove the selector identity. */
int collision_kernel_seed_q(CollisionKernelSeed *out,unsigned q,unsigned length);
/* h(u)=sum_j c_j [u(1-u)]^j, P(u)=lambda+2u(1-u)h(u).
 * No positivity or unit normalization is assumed or claimed for this raw
 * symmetric polynomial profile. length 0..9, coefficients can be signed.
 * Primitive output uses Mobius extraction; row uses direct angular grid. */
int collision_kernel_profile_q(mpq_t primitive,mpq_t row,mpq_t grid_sum,
    const mpq_t lambda,const mpq_t *coefficients,unsigned length,unsigned period);
/* Positive square lattice prefix of T(x), x>0 rational, cutoff 1..64.
 * upper is an enclosure of T(x). reciprocal is the separately evaluated
 * prefix T(1/x), so reciprocal=x*prefix can be checked without a limit. */
int collision_kernel_lattice_q(mpq_t prefix,mpq_t upper,mpq_t reciprocal,
    const mpq_t x,unsigned cutoff);
enum { CKM_PARENT, CKM_LEFT, CKM_RIGHT, CKM_DEFECT, CKM_NONLOCAL_PARENT,
       CKM_NONLOCAL_LEFT, CKM_NONLOCAL_RIGHT, CKM_NONLOCAL_DEFECT, CKM_COUNT };
typedef struct { mpq_t value[CKM_COUNT]; } CollisionCarryMeasurement;
extern const char *const collision_measurement_names[CKM_COUNT];
void collision_measurement_init(CollisionCarryMeasurement *out);
void collision_measurement_clear(CollisionCarryMeasurement *out);
/* Polarization of mean |f|^power versus (mean f^2)^2 on centered rows.
 * Odd modulus 3..127, an admissible unit triple, even power 2..12, and
 * arbitrary rational amplitude. This does not classify all continuous Phi. */
int collision_kernel_measurement_q(CollisionCarryMeasurement *out,unsigned m,
    unsigned a,unsigned b,unsigned power,const mpq_t amplitude);
int collision_kernel_readout_command(int argc,char **argv);
#endif
