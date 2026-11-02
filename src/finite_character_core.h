#ifndef NFIELD_FINITE_CHARACTER_CORE_H
#define NFIELD_FINITE_CHARACTER_CORE_H

#include <complex.h>

#include "nfield.h"

enum {
    FINITE_CHARACTER_MAX_CUTOFF = 5000000,
    FINITE_CHARACTER_MAX_CUTOFFS = 6,
    FINITE_CHARACTER_MAX_FACTORS = 16,
    FINITE_CHARACTER_SPECTRUM_MAX_MODULUS = 4096
};

typedef struct {
    int positive;
    int negative;
    int zero_product;
    int correlation_defined;
    long double net;
    long double direct;
    long double decomposition_error;
    long double correlation;
} FiniteCharacterPairingStats;

typedef struct {
    int odd;
    int active;
    int inactive;
    int cutoff_count;
    int prime_count[FINITE_CHARACTER_MAX_CUTOFFS];
    FiniteCharacterPairingStats stats[FINITE_CHARACTER_MAX_CUTOFFS];
} FiniteCharacterPairingAudit;

int finite_character_is_prime(int value);
int *finite_character_primes(int limit, int *prime_count);
long double centered_collision_value(const CollisionCenteredTable *table,
                                     int residue);
int centered_collision_table_audit(const CollisionCenteredTable *table,
                                   int *reflection_cases,
                                   int *fiber_cases);
int finite_character_pairing_audit(const CollisionCenteredTable *table,
                                   const int *primes,
                                   int prime_count,
                                   const int *cutoffs,
                                   int cutoff_count,
                                   FiniteCharacterPairingAudit *audit);

typedef struct {
    int modulus;
    int character_count;
    int factor_count;
    int factor_modulus[FINITE_CHARACTER_MAX_FACTORS];
    int factor_order[FINITE_CHARACTER_MAX_FACTORS];
    int factor_generator[FINITE_CHARACTER_MAX_FACTORS];
    int even_count;
    int base_factored_count;
    int allowed_count;
    int resolved_active_count;
    int resolved_zero_count;
    int *coordinates;
    int *conjugate;
    int *conductor;
    unsigned char *odd;
    unsigned char *base_factored;
    unsigned char *resolved_active;
    long double complex *coefficient;
    long double tolerance;
    long double maximum_even_coefficient;
    long double maximum_base_factored_coefficient;
    long double inversion_error;
    long double parseval_error;
    long double conjugate_error;
} FiniteCharacterSpectrum;

int finite_character_spectrum_compute(
    const CollisionCenteredTable *table, FiniteCharacterSpectrum *spectrum);
void finite_character_spectrum_free(FiniteCharacterSpectrum *spectrum);

/* Reusable full unit-group table, including noncyclic groups. Phases are
 * exact integers modulo denominator, with -1 on nonunits. Character index
 * uses the same mixed-radix CRT coordinates as the collision spectrum.
 * Build into a zero-initialized table; failure leaves it unchanged. */
#define FINITE_CHARACTER_TABLE_MAX_MODULUS 512
typedef struct {
    int modulus, count, denominator;
    int *phase, *conductor;
    unsigned char *odd;
} FiniteCharacterTable;
int finite_character_table_build(int modulus, FiniteCharacterTable *out);
void finite_character_table_free(FiniteCharacterTable *table);
long double complex finite_character_table_value(const FiniteCharacterTable *table,
    unsigned character, unsigned residue);

#endif
