#ifndef NFIELD_RESET_FOREST_H
#define NFIELD_RESET_FOREST_H

#include <gmp.h>

/* Exact finite operations for the coherent field B_N = 2 sum_{h<=N} psi(hx),
 * with midpoint psi(integer)=0, N=p-1 and Q=p^2. Initialize before use.
 * The computational cutoff is independent of the theorem's hypotheses. */
#define RESET_FOREST_MAX_PRIME 251u
enum {
    RF_CONTINUOUS, RF_SAMPLED, RF_DEFECT, RF_CONTACT, RF_CORRECTED,
    RF_FOREST, RF_OTHER, RF_ABSOLUTE, RF_RESTORATION, RF_OTHER_CLOCKS,
    RF_CURVATURE, RF_SIGNED_BOUND, RF_VALUE_COUNT
};
extern const char *const reset_forest_names[RF_VALUE_COUNT];
typedef struct {
    unsigned prime, cutoff, grid, count;
    unsigned rough[RESET_FOREST_MAX_PRIME];
    unsigned selected[RESET_FOREST_MAX_PRIME];
    unsigned projection[RESET_FOREST_MAX_PRIME];
    unsigned population[RESET_FOREST_MAX_PRIME];
    mpq_t signed_work[RESET_FOREST_MAX_PRIME];
    mpq_t absolute_work[RESET_FOREST_MAX_PRIME];
    mpq_t clock_work[RESET_FOREST_MAX_PRIME];
    mpq_t value[RF_VALUE_COUNT];
    mpz_t divisor;
} ResetForest;

void reset_forest_init(ResetForest *out);
void reset_forest_clear(ResetForest *out);
/* Invalid inputs leave initialized outputs unchanged. Positive divisor may
 * be arbitrarily large. Work values are unnormalized A and W readings;
 * multiplication by 4/Q converts A to its contribution to the defect. */
int reset_forest_compute(ResetForest *out, unsigned prime, const mpz_t divisor);
int reset_forest_return_divisor(mpz_t out, unsigned prime, unsigned window);
int reset_forest_command(int argc, char **argv);
void reset_forest_help(void);
int reset_forest_verify(void);
#endif
