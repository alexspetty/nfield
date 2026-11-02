#ifndef NFIELD_WEIGHTED_REMAINDER_STATE_H
#define NFIELD_WEIGHTED_REMAINDER_STATE_H

/* Finite cutoffs use the actual coprime harmonic weights. Infinite conductor
 * amplitudes and Haar-limit claims are deliberately not numerical outputs. */
typedef struct {
    int resolution;
    int cutoff;
    long double mass;
    long double stationary_age;
    long double centered_age;
    long double finite_increment;
    long double variance;
} WeightedRemainderState;

int weighted_remainder_state_compute(int resolution, int cutoff,
                                     WeightedRemainderState *state);
long double weighted_remainder_weight(int period);
long double weighted_remainder_covariance(int first, int second);
int weighted_remainder_state_inspect(int resolution, int cutoff);
int weighted_remainder_state_conductor(int conductor, int cutoff);
int weighted_remainder_state_verify(void);
void weighted_remainder_state_help(void);

#endif
