#ifndef NFIELD_RESET_SOURCE_H
#define NFIELD_RESET_SOURCE_H

#include <gmp.h>

#define RESET_SOURCE_MAX_CUTOFF 64u
#define RESET_SOURCE_MAX_GRID 65536u

enum { RS_ORIGINAL, RS_SELECTED, RS_COMPLEMENT, RS_COMPONENT_COUNT };
enum { RS_CONTINUOUS, RS_SAMPLED, RS_FORM_COUNT };

/* Coefficients use indices 1..cutoff; index zero is always zero.
 * A mask selects reset masses, not coefficients. Divisor inversion then
 * recovers the unique selected source, including its signed complement. */
typedef struct {
    unsigned cutoff, grid;
    unsigned char mask[RESET_SOURCE_MAX_CUTOFF + 1];
    unsigned destination[RESET_SOURCE_MAX_CUTOFF + 1];
    int saturated, has_work;
    mpz_t modulus;
    mpq_t coefficient[RS_COMPONENT_COUNT][RESET_SOURCE_MAX_CUTOFF + 1];
    mpq_t mass[RS_COMPONENT_COUNT][RESET_SOURCE_MAX_CUTOFF + 1];
    mpq_t total[RS_COMPONENT_COUNT];
    mpq_t energy[RS_FORM_COUNT][RS_COMPONENT_COUNT];
    mpq_t mixed[RS_FORM_COUNT]; /* twice the selected/complement pairing */
    mpq_t primitive_work[RESET_SOURCE_MAX_CUTOFF + 1];
    mpq_t clock_work[RESET_SOURCE_MAX_CUTOFF + 1];
    mpq_t ordered_work[RS_COMPONENT_COUNT];
    mpq_t reset_work[RS_COMPONENT_COUNT];
} ResetSource;

void reset_source_init(ResetSource *out);
void reset_source_clear(ResetSource *out);
/* The zero reset and resets beyond the finite support have mass zero. */
void reset_source_mass(mpq_t out, const mpq_t *coefficient,
                       unsigned cutoff, unsigned reset);
/* Grid zero requests source coordinates only. Positive grids additionally
 * return exact energies and ordered work for B_c=2 sum c_j psi(jx), with
 * psi(integer)=0. No coprimality or positivity of c is assumed. Invalid
 * input returns zero without changing an initialized output. */
int reset_source_project(ResetSource *out, unsigned cutoff,
                         const mpq_t *coefficient,
                         const unsigned char *mask, unsigned grid);
/* Nonnegative modulus; zero selects all positive reset indices and gives
 * the identity projection, since gcd(j,0)=j. */
int reset_source_collapse(ResetSource *out, unsigned cutoff,
                          const mpq_t *coefficient,
                          const mpz_t modulus, unsigned grid);
int reset_source_command(int argc, char **argv);
void reset_source_help(void);

#endif
