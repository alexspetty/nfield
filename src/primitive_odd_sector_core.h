#ifndef NFIELD_PRIMITIVE_ODD_SECTOR_CORE_H
#define NFIELD_PRIMITIVE_ODD_SECTOR_CORE_H

#include "nfield.h"

enum { PRIMITIVE_ODD_MAX_CUTOFFS = 6 };

typedef struct {
    int odd_characters;
    int active_characters;
    int inactive_characters;
    int conjugate_pairs;
    int z_defined;
    int conjugacy_ok;
    long double rho;
    long double relabeling_variance;
    long double z;
    long double collision_support;
    long double prime_support;
    long double primitive_occupancy;
    long double full_odd_rho;
    long double factorization_error;
    long double conjugate_error;
} PrimitiveOddSectorRow;

typedef struct {
    CollisionCenteredTable table;
    int primitive_root;
    int cutoff_count;
    long double maximum_even_energy_fraction;
    long double maximum_induced_energy_fraction;
    PrimitiveOddSectorRow row[PRIMITIVE_ODD_MAX_CUTOFFS];
} PrimitiveOddSectorResult;

int primitive_odd_sector_compute(int base,
                                 const int *primes,
                                 int prime_count,
                                 const int *cutoffs,
                                 int cutoff_count,
                                 PrimitiveOddSectorResult *result);
void primitive_odd_sector_result_free(PrimitiveOddSectorResult *result);

#endif
