#ifndef NFIELD_WEIGHTED_REMAINDER_ALIGNMENT_LOCAL_H
#define NFIELD_WEIGHTED_REMAINDER_ALIGNMENT_LOCAL_H
#include <gmp.h>
/* Exact local factors for the reset and full alignment observables.
 * Prime p=2..240 and valuation v=0..240. Exact rational fields include
 * the infinite geometric tail in the alignment numerator. Initialize
 * and clear once; rejected calls preserve the complete output. */
typedef struct {
    unsigned prime,valuation;
    mpq_t reset_factor,reset_numerator,reset_average;
    mpq_t alignment_factor,alignment_numerator,alignment_average;
    mpq_t alignment_tail,limiting_factor,limiting_average;
    mpq_t reset_factor_relative_loss,reset_average_loss;
    mpq_t alignment_factor_relative_loss,alignment_average_loss;
    mpq_t absent_factor,absent_average;
} WeightedRemainderAlignmentLocal;
void weighted_remainder_alignment_local_init(WeightedRemainderAlignmentLocal *s);
void weighted_remainder_alignment_local_clear(WeightedRemainderAlignmentLocal *s);
int weighted_remainder_alignment_local_compute(WeightedRemainderAlignmentLocal *out,unsigned p,unsigned v);
#endif
