#ifndef NFIELD_COLLISION_CAPACITY_GENERATION_H
#define NFIELD_COLLISION_CAPACITY_GENERATION_H
#include <gmp.h>

/* Exact finite evaluations for Finite Generation of Collision Capacity.
 * Initialized outputs must be distinct. Invalid input leaves them unchanged.
 * The implementation checks finite identities, not their infinite limits. */
#define COLLISION_GENERATION_MAX 120
int collision_generation_source_q(mpq_t cells, mpq_t rows,
    unsigned base, unsigned lag, unsigned phase);
int collision_generation_carry_q(mpq_t row_variance, mpq_t carry_variance,
    mpq_t parent, mpq_t left, mpq_t right, mpq_t midpoint_defect,
    unsigned modulus, unsigned first, unsigned second);
int collision_generation_recover_q(mpq_t recovered, unsigned period);
/* The smooth control in Proposition 15 / Theorem 20, epsilon=1/(8*s^3).
 * Require primes 5<=r<s<2r and 1<=address<=120. */
int collision_generation_control_q(mpq_t delta_mass, mpq_t delta_row,
    mpq_t delta_capacity, unsigned r, unsigned s, unsigned address);
/* Coefficient of log(prime) in the signed current. r=s=0 selects collision;
 * otherwise use the same smooth control. n=1 has zero current. */
int collision_generation_current_q(mpq_t coefficient, unsigned address,
    unsigned prime, unsigned r, unsigned s);
void collision_capacity_generation_help(void);
int collision_capacity_generation_command(int argc, char **argv);
int collision_capacity_generation_verify(void);
#endif
