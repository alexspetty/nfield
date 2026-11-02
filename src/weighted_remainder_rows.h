#ifndef NFIELD_WEIGHTED_REMAINDER_ROWS_H
#define NFIELD_WEIGHTED_REMAINDER_ROWS_H

#include "weighted_remainder_exact.h"

/* Exact primitive age P, midpoint odd carrier R, and Ramanujan c at an
 * arbitrary signed GMP address. The normalized squared norms are complete
 * period averages. radical_descent is (q/rad(q))*P_rad(q)(floor(n/(q/rad(q)))).
 * Conductor one is deliberately excluded: its inactive age rows do not
 * satisfy P=R-c/2. Initialize/clear once; failed calls preserve all fields. */
typedef struct {
    unsigned conductor, residue, radical, scale, totient, jordan_two;
    mpq_t primitive, odd, ramanujan, primitive_norm_squared;
    mpq_t odd_norm_squared, ramanujan_norm_squared, radical_descent;
} WeightedRemainderRows;

void weighted_remainder_rows_init(WeightedRemainderRows *out);
void weighted_remainder_rows_clear(WeightedRemainderRows *out);
/* 2<=q<=240. Address may alias an output rational limb: all input is
 * consumed before any output changes. Null output is rejected. */
int weighted_remainder_rows_compute(WeightedRemainderRows *out, unsigned q,
                                    const mpz_t address);

/* Actual inverse over multiples: sum_{1<=j<=M/k} mu(j)*xi[k*j].
 * The input is an initialized canonical rational array [0..M], xi[0]=xi[1]=0;
 * signed values are allowed. 2<=M,k<=240; k>M gives zero. This recovers
 * finite weights exactly when xi is their finite multiple transform.
 * It makes no infinite-tail assertion. Output/input aliasing is allowed;
 * invalid input preserves the initialized output. */
int weighted_remainder_mass_inverse_q(mpq_t out, const mpq_t *amplitudes,
                                      unsigned cutoff, unsigned period);

/* Full infinite collision-mass recovery from a finite conductor inverse.
 * beta endpoints enclose sum_{j<=Q/d} mu(j)*eta_(d*j), with each full eta
 * enclosed using periods through M. A separate proved inverse-tail error
 * is E=4*(b_d+2*b_J+3)/(d^2*J), J=floor(Q/d), 2*d<=2^b_d, 2*J<=2^b_J.
 * The resulting mass interval uses no direct evaluation of the target w_d.
 * It is conservative; increasing M reduces amplitude error, and increasing
 * Q reduces the analytic inverse remainder (not necessarily each endpoint).
 * 2<=d<=Q<=240, 2<=M<=240. Failed calls preserve initialized output. */
typedef struct {
    unsigned period, conductor_cutoff, period_cutoff, quotient;
    unsigned period_binary, quotient_binary;
    mpq_t beta_lower, beta_upper, inverse_tail_error, mass_lower, mass_upper;
} WeightedRemainderRecovery;

void weighted_remainder_recovery_init(WeightedRemainderRecovery *out);
void weighted_remainder_recovery_clear(WeightedRemainderRecovery *out);
int weighted_remainder_mass_recovery_compute(WeightedRemainderRecovery *out,
                                             unsigned d, unsigned Q, unsigned M);

int weighted_remainder_rows_command(int argc, char **argv);

#endif
