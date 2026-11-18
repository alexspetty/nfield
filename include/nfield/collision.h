#ifndef NFIELD_PUBLIC_COLLISION_H
#define NFIELD_PUBLIC_COLLISION_H

#include <gmp.h>
#include <nfield/core.h>

#ifdef __cplusplus
extern "C" {
#endif

#define NFIELD_SOURCE_MAX_CUTOFF 64u
#define NFIELD_SOURCE_MAX_GRID 65536u
#define NFIELD_FOREST_MAX_PRIME 251u
#define NFIELD_FOREST_MIN_RETURN 3u
#define NFIELD_FOREST_MAX_RETURN 31u

/* Exact finite calculations for B_c(x)=2 sum c_j psi(j*x), psi(integer)=0.
 * All GMP arguments must be initialized. Input numbers are borrowed only
 * during the call. Rational getters COPY into caller-owned mpq_t outputs.
 * Recoverable errors leave existing results and output arguments unchanged.
 * GMP allocation failure follows GMP's allocator policy (normally abort).
 * Concurrent calls on distinct handles are supported. Do not mutate or free
 * a handle while another thread is using it. No function prints or launches
 * a process. Resource limits concern dimensions, not rational precision.
 */
typedef struct nfield_source nfield_source;
typedef struct nfield_forest nfield_forest;

typedef enum {
    NFIELD_ORIGINAL = 0, NFIELD_SELECTED = 1, NFIELD_COMPLEMENT = 2
} nfield_component;
typedef enum {
    NFIELD_CONTINUOUS = 0, NFIELD_SAMPLED = 1
} nfield_form;

/* Fixed-layout metadata for API version 1; result storage remains opaque. */
typedef struct {
    unsigned cutoff, grid;
    int has_work, has_modulus;
} nfield_source_info;
typedef struct {
    unsigned prime, cutoff, grid, selected_count;
} nfield_forest_info;
typedef struct {
    unsigned rough, selected, destination, population;
} nfield_forest_clock_info;

/* Set *out=NULL before creation. A non-NULL *out is rejected, not overwritten.
 * Destroy accepts NULL. A successful computation can replace an existing
 * computation on the same handle. Getters return ESTATE before the first one.
 */
nfield_status nfield_source_create(nfield_source **out);
void nfield_source_destroy(nfield_source *source);

/* weights[0..cutoff-1] corresponds to c_1..c_N. mask uses the same array
 * convention for reset indices 1..N and must contain only 0 or 1. Both arrays
 * may be NULL at N=0. Rational inputs may be unreduced, with either denominator
 * sign; zero denominators are rejected. A mask selects RESET MASSES, not
 * coefficients. Divisor inversion recovers the signed selected source.
 * Q=0 requests coordinates only; energy and work getters return ENODATA.
 */
nfield_status nfield_source_project(nfield_source *source, unsigned cutoff,
    const mpq_t *weights, const unsigned char *mask, unsigned grid);
/* Nonnegative M selects k dividing M. M=0 selects all resets (identity). */
nfield_status nfield_source_collapse(nfield_source *source, unsigned cutoff,
    const mpq_t *weights, const mpz_t modulus, unsigned grid);
/* Positive D uses M=N^N D, exactly as CLI --divisor. At N=0, N^N is 1. */
nfield_status nfield_source_divisor(nfield_source *source, unsigned cutoff,
    const mpq_t *weights, const mpz_t divisor, unsigned grid);

nfield_status nfield_source_get_info(const nfield_source *source,
    nfield_source_info *out);
/* k=1..N for all indexed getters; k=0 and k>N return ERANGE. */
nfield_status nfield_source_coefficient(const nfield_source *source,
    nfield_component component, unsigned k, mpq_t out);
nfield_status nfield_source_mass(const nfield_source *source,
    nfield_component component, unsigned k, mpq_t out);
nfield_status nfield_source_total(const nfield_source *source,
    nfield_component component, mpq_t out);
nfield_status nfield_source_energy(const nfield_source *source,
    nfield_form form, nfield_component component, mpq_t out);
/* Always TWICE the selected/complement pairing, including its sign. */
nfield_status nfield_source_mixed(const nfield_source *source,
    nfield_form form, mpq_t out);
/* Ordered readings always use the complete original field as receiver. */
nfield_status nfield_source_ordered_work(const nfield_source *source,
    nfield_component component, mpq_t out);
nfield_status nfield_source_reset_work(const nfield_source *source,
    nfield_component component, mpq_t out);
nfield_status nfield_source_clock_work(const nfield_source *source,
    unsigned k, mpq_t out);
nfield_status nfield_source_primitive_work(const nfield_source *source,
    unsigned k, mpq_t out);
nfield_status nfield_source_mask(const nfield_source *source,
    unsigned k, unsigned *out);
/* Arbitrary-mask results have no modulus/destination: ENODATA. */
nfield_status nfield_source_modulus(const nfield_source *source, mpz_t out);
nfield_status nfield_source_destination(const nfield_source *source,
    unsigned k, unsigned *out);

nfield_status nfield_forest_create(nfield_forest **out);
void nfield_forest_destroy(nfield_forest *forest);
/* Odd prime p=3..251; N=p-1, Q=p^2; positive arbitrary-precision D.
 * Selected k have their N-rough part dividing D. This is a finite operation;
 * it does not assert a uniform bound for the full complementary reading.
 */
nfield_status nfield_forest_compute(nfield_forest *forest, unsigned prime,
    const mpz_t divisor);
nfield_status nfield_forest_return_divisor(mpz_t out, unsigned prime,
    unsigned window);
nfield_status nfield_forest_get_info(const nfield_forest *forest,
    nfield_forest_info *out);
nfield_status nfield_forest_divisor(const nfield_forest *forest, mpz_t out);

typedef enum {
    NFIELD_FOREST_CONTINUOUS_ENERGY = 0, NFIELD_FOREST_SAMPLED_ENERGY = 1,
    NFIELD_FOREST_DEFECT = 2, NFIELD_FOREST_ORIGIN_CONTACT = 3,
    NFIELD_FOREST_CORRECTED_DEFECT = 4, NFIELD_FOREST_SIGNED_WORK = 5,
    NFIELD_FOREST_COMPLEMENT_WORK = 6, NFIELD_FOREST_ABSOLUTE_WORK = 7,
    NFIELD_FOREST_RESTORATION_WORK = 8, NFIELD_FOREST_COMPLEMENT_CLOCK_WORK = 9,
    NFIELD_FOREST_CURVATURE = 10, NFIELD_FOREST_SIGNED_WORK_BOUND = 11
} nfield_forest_quantity;
typedef enum {
    NFIELD_CLOCK_SIGNED_WORK = 0, NFIELD_CLOCK_ABSOLUTE_WORK = 1,
    NFIELD_CLOCK_ORDERED_WORK = 2
} nfield_clock_quantity;

/* Forest work is unnormalized A; multiply by 4/Q for its defect contribution.
 * The bound applies to the signed forest sum, not the absolute-work sum. */
nfield_status nfield_forest_value(const nfield_forest *forest,
    nfield_forest_quantity quantity, mpq_t out);
nfield_status nfield_forest_get_clock_info(const nfield_forest *forest,
    unsigned k, nfield_forest_clock_info *out);
/* Clock values are A_k, |A|_k and W_k respectively; see the library guide. */
nfield_status nfield_forest_clock_work(const nfield_forest *forest,
    nfield_clock_quantity quantity, unsigned k, mpq_t out);

#ifdef __cplusplus
}
#endif
#endif
