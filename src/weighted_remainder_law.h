#ifndef NFIELD_WEIGHTED_REMAINDER_LAW_H
#define NFIELD_WEIGHTED_REMAINDER_LAW_H
#include "weighted_remainder_clock.h"

typedef enum {
    WEIGHTED_LAW_MOMENT, WEIGHTED_LAW_CDF, WEIGHTED_LAW_WINDOW,
    WEIGHTED_LAW_CONCENTRATION, WEIGHTED_LAW_CHARACTERISTIC
} WeightedRemainderLawOperation;

/* Complete finite quotient, with multiplicities and no renormalization.
 * M=2..12 (LCM <=50000). Moment degree=0..16; CDF x=a; closed window
 * [a,b]; concentration width=a>=0; characteristic frequency=a. CDF,
 * window and concentration require margin>0. All rational inputs are
 * canonical with <=256 bits per component, including unused parameters.
 * finite is the signed moment/CDF/window/max-window probability; absolute
 * is the absolute moment. Characteristic uses real_lower/upper and exact
 * imaginary part zero by finite reflection. MPFR rounding and the squared
 * L2 cutoff budget are separate. Full probability bounds may be [0,1].
 * Initialize/clear once. Failure preserves all outputs; inputs may alias
 * output fields. Moment fields have no implicit full-moment certificate. */
typedef struct {
    unsigned cutoff, period, distinct, degree, binary_exponent;
    mpq_t finite, absolute, full_lower, full_upper, squared_l2_error;
    mpq_t probability_error, finite_expanded, real_lower, real_upper;
    mpq_t rounding_width, characteristic_error_upper;
} WeightedRemainderLaw;
void weighted_remainder_law_init(WeightedRemainderLaw *out);
void weighted_remainder_law_clear(WeightedRemainderLaw *out);
int weighted_remainder_law_compute(WeightedRemainderLaw *out,
    WeightedRemainderLawOperation operation, unsigned M, unsigned degree,
    const mpq_t a, const mpq_t b, const mpq_t margin);

/* Exact complete-period recurrence counts for a closed interval, M=2..12
 * and horizon=1..240. probabilities[0..horizon-1] are initialized distinct
 * outputs; index h is P(A intersect shift^-h A). The two scalar outputs
 * are distinct from each other and the array. second_moment is E[S^2]/H^2
 * for S=sum_{j=0}^{H-1}1_A(x+j); mean_square=P(A)^2. Invalid inputs
 * preserve all outputs. Interval inputs may alias outputs. */
int weighted_remainder_law_recurrence_q(mpq_t *probabilities,
    mpq_t mean_square, mpq_t second_moment, unsigned M, unsigned horizon,
    const mpq_t lower, const mpq_t upper);

int weighted_remainder_law_command(int argc, char **argv);
#endif
