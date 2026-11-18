/* Existing arithmetic and field interfaces. See RESEARCH_LIBRARY.md for
 * numeric domains, ownership and rendering distinctions. */
#ifndef NFIELD_RESEARCH_ARITHMETIC_H
#define NFIELD_RESEARCH_ARITHMETIC_H

#include <stddef.h>
#include <stdint.h>
#include "weighted_remainder_state.h"
#include "collision_capacity_transition.h"
#include "collision_capacity_generation.h"
#include "weighted_remainder_exact.h"
#include "weighted_remainder_floor.h"
#include "weighted_remainder_clock.h"
#include "weighted_remainder_weights.h"
#include "weighted_remainder_rows.h"
#include "weighted_remainder_increment.h"
#include "weighted_remainder_fourier.h"
#include "weighted_remainder_amplitude.h"
#include "weighted_remainder_expansion.h"
#include "weighted_remainder_spectral.h"
#include "weighted_remainder_character.h"
#include "weighted_remainder_cotangent.h"
#include "weighted_remainder_harmonic_root.h"
#include "weighted_remainder_small_amplitude.h"
#include "weighted_remainder_dirichlet.h"
#include "weighted_remainder_primitive.h"
#include "weighted_remainder_sawtooth.h"
#include "weighted_remainder_pairing.h"
#include "weighted_remainder_joint.h"
#include "weighted_remainder_cylinder.h"
#include "weighted_remainder_conductor.h"
#include "weighted_remainder_activation.h"

#include "weighted_remainder_alignment_growth.h"
#include "weighted_remainder_law.h"


/* Certified finite native refinement; public declarations in its own header. */
#include "native_refinement.h"


/* ── Repetend ────────────────────────────────────────────── */

typedef struct {
    int  *digits;       /* full digit sequence (prefix + cycle)       */
    int   len;          /* total length of digits array               */
    int   cycle_start;  /* index where the cycle begins               */
    int   cycle_len;    /* length of repeating block (0 = terminates) */
} Repetend;

Repetend repetend_compute(int k, int n, int base);
int      repetend_digit_at(const Repetend *r, int position);
void     repetend_free(Repetend *r);

/* ── Row ─────────────────────────────────────────────────── */

typedef struct {
    int       k;
    Repetend  rep;
    int       rot_index;    /* rotation offset relative to base rep    */
    double    alignment;    /* fraction of matching cycle positions     */
    double    curvature;    /* mean |d[i] - d[i+1]| in cycle           */
} Row;

/* ── Field ───────────────────────────────────────────────── */

typedef struct {
    int       n;
    int       base;
    Repetend  base_rep;     /* repetend of 1/n                         */
    Row      *rows;         /* rows[0..n-2] for k = 1..n-1             */
    int       num_rows;
} Field;

Field field_build(int n, int base);
void  field_free(Field *f);

/* ── Invariants ──────────────────────────────────────────── */
/*
 * Primitive invariants:
 *   C(n)  curvature     mean adjacent-digit variation in the base repetend
 *   R(n)  coherence     dominance of the most common rotation index
 *   H3(n) harmonicity   1 if cycle length divisible by 3, else 0
 *   S(n)  structure     R/C + H3
 *   B(n)  burden        accumulated structural load
 *   D(n)  depth         1/S + B
 *
 * Alignment and collision manuscript invariants:
 *   alpha(n)  alignment       mean digit-match proportion across field
 *   sigma(n)  pairwise        mean digit-match among all pairs
 *   F(n)      focused         alpha - sigma
 *   Phi(k)    spectral power  digit-function Dirichlet kernel formula
 *   R(ell)    autocorrelation digit matches at lag ell
 *   C(g)      collision count residues sharing bin under multiplier g
 *   Gamma(ell) phase filter   autocorrelation spectral gate function
 */

typedef struct {
    int     n;
    int     base;
    int     cycle_length;   /* L: repetend length of 1/n               */
    double  curvature;      /* C(n)  (primitive)                       */
    double  coherence;      /* R(n)  (primitive)                       */
    int     harmonicity;    /* H3(n) (primitive)                       */
    double  structure;      /* S(n)  (primitive)                       */
    double  burden;         /* B(n)  (primitive)                       */
    double  depth;          /* D(n)  (primitive)                       */
    double  alignment;      /* mean alignment across the field         */
} Invariants;

Invariants invariants_compute(int n, int base);

/* ── Alignment ───────────────────────────────────────────── */

double alignment_exact(int n, int base);
double alignment_formula(int m, int p);
int    mult_order(int base, int p);
int    is_b_smooth(int n, int base);

/* ── Output ──────────────────────────────────────────────── */

void field_print(const Field *f);
void polar_print(int n, int base);
void invariants_print(const Invariants *inv);
void survey(int n_max, int base, int csv);
void survey_range(int n_min, int n_max, int base, int csv);
/* ── coherence decomposition ────────────────────── */

double sigma_exact(int n, int base);
int    decompose_print(int n, int base);

/* ── additive digit-bin spectral power ─────────── */

void   spectral_print(int p, int base);
int    spectral_power_bin_sizes(int p, int base, int *sizes,
                                int capacity, int *count);
int    spectral_power_values(int p, int base, double *values,
                             int capacity, int *count);
int    spectral_power_overlap_values(int p, int base, int *values,
                                     int capacity, int *count);
int    spectral_power_triangular_values(int p, int base, int *values,
                                        int capacity, int *count);
int    spectral_power_inspect(int p, int base);
int    spectral_power_overlap(int p, int base);


/* ── same-bin cross-spectrum and autocorrelation ───────── */

int    autocorrelation_collision_count(int p, int base, int multiplier,
                                       int *count);
int    autocorrelation_aggregate_values(int p, int base, int *values,
                                        int capacity, int *length);
int    autocorrelation_orbit_values(int p, int base, int coset,
                                    int *values, int capacity, int *length);
int    autocorrelation_inspect(int p, int base);
int    autocorrelation_slice(int p, int multiplier, int base);
int    autocorrelation_orbit(int p, int coset, int base);
int    autocorrelation_harmonics(int p, int coset, int base);


/* ── phase-filtered Ramanujan sums and spectral gate ───── */

int    phase_gate_components(int p, int base, int multiplier,
                             int *collision, double *sigma_real,
                             double *sigma_imag, double *mass,
                             double *gamma);
int    phase_gate_cell_count(int multiplier, int base, long long *count);
int    phase_gate_bin_word_values(int p, int base, int *sizes, int *word,
                                  int capacity, int *q, int *remainder);
int    phase_gate_inspect(int p, int multiplier, int base);
int    phase_gate_multipliers(int p, int base);
int    phase_gate_bin_word(int p, int base);
int    phase_gate_density(int multiplier, int base, int max_prime);
int    phase_gate_power_lag(int lag, int base, int max_prime);
int    phase_gate_prime_sum(int lag, int base, int max_prime);


/* -- bin derangements and gate width ----------------------- */

int    bin_derangements_collision_count(int p, int base, int multiplier,
                                         int *count);
int    bin_derangements_family_values(int p, int base, int *values,
                                       int capacity, int *count);
int    bin_derangements_mean_fraction(int p, int base,
                                       long long *numerator,
                                       long long *denominator);
int    bin_derangements_inspect(int p, int base);
int    bin_derangements_family(int p, int base);
int    bin_derangements_mean(int p, int base);
int    bin_derangements_lags(int p, int base);


/* -- finite collision-character decomposition --------------- */

int    collision_characters_prime_deviation(int p, int base, int lag,
                                             long long *numerator,
                                             long long *denominator,
                                             int *collision,
                                             int *multiplier);
int    collision_characters_prime(int p, int base, int lag);
int    collision_characters_inspect(int cutoff, int base, int lag,
                                     long double sigma, long double tau);
int    collision_characters_base_ten_row(int cutoff, int *prime_count,
                                          long double *component_real,
                                          long double *component_imag);


/* -- silent primes and exact collision variance --------------- */

int    silent_primes_collision_count(int p, int base, int multiplier,
                                      int *count);
int    silent_primes_repetend_count(int p, int base, int lag, int *count);
int    silent_primes_global_recipe_match(int p, int base, int lag,
                                          int *match);
int    silent_primes_variance_fraction(
           int p, int base,
           unsigned long long *mean_numerator,
           unsigned long long *mean_denominator,
           unsigned long long *variance_numerator,
           unsigned long long *variance_denominator);
int    silent_primes_recipe(int base, int lag);
int    silent_primes_prime(int p, int base, int lag);
int    silent_primes_variance(int p, int base);


/* -- exact collision residue tables shared by named companions ---- */

int    collision_table_gcd(int a, int b);
int    collision_table_modulus(int base, int lag, int *modulus);
int    collision_table_value(int base, int lag, int residue, int *value);
int    collision_table_direct_deviation(int n, int base, int lag,
                                        int *collision, int *deviation,
                                        int *multiplier);

typedef struct {
    int base;
    int lag;
    int modulus;
    int fiber_size;
    int phi;
    int *value;
    long long *fiber_sum;
    int *fiber_count;
    long long *centered_numerator;
} CollisionCenteredTable;

int    collision_centered_table_build(int base, int lag,
                                      CollisionCenteredTable *table);
void   collision_centered_table_free(CollisionCenteredTable *table);
int    collision_centered_table_fraction(
           const CollisionCenteredTable *table, int residue,
           long long *numerator, long long *denominator);

/* -- the collision fluctuation sum ------------------------------- */

int    collision_fluctuation_fraction(int p, int base,
                                      long long *numerator,
                                      long long *denominator,
                                      int *collision, int *integer_deviation);
int    collision_fluctuation_prime(int p, int base);
int    collision_fluctuation_table(int base);
int    collision_fluctuation_classes(int base);
int    collision_fluctuation_sum(int cutoff, int base);


/* -- all-lag collision centering -------------------------------- */

int    centered_collision_fraction(int base, int lag, int residue,
                                   long long *numerator,
                                   long long *denominator,
                                   int *table_value);
int    centered_collision_inspect(int n, int base, int lag);
int    centered_collision_table(int base, int lag);
int    centered_collision_fibers(int base, int lag);

int    centered_collision_sum(int cutoff, int base, int lag);


/* -- the collision periodic table ------------------------------- */

int    collision_periodic_value(int base, int residue, int *value);
int    collision_periodic_inspect(int n, int base);
int    collision_periodic_compare(int first, int second, int base);
int    collision_periodic_table(int base);
int    collision_periodic_summary(int base);


/* -- the collision transform and the critical strip ------------ */

int    collision_transform_prime_window(
           int lower, int upper, int base, int lag,
           const long double *exponents, int exponent_count,
           long double *sums, int *prime_count);
int    collision_transform_inspect(int n, int base, int lag);
int    collision_transform_table(int base, int lag);

int    collision_transform_spectrum(int base, int lag);
int    collision_transform_window(int lower, int upper, int base, int lag,
                                   long double sigma);


/* -- residue-three neutrality ---------------------------------- */

int    residue_three_neutrality_channel_sums(
           int base, int lag, int residue,
           long long *raw_sum, long long *centered_numerator_sum,
           int *count, int *joint_modulus);
int    residue_three_neutrality_prime_window(
           int lower, int upper, int base, int lag,
           const long double *exponents, int exponent_count,
           long double *class_one, long double *class_two,
           long double *total, long double *twist,
           int *class_one_count, int *class_two_count);
int    residue_three_neutrality_inspect(int n, int base, int lag);
int    residue_three_neutrality_canonical(int base, int lag);
int    residue_three_neutrality_channels(int base, int lag);
int    residue_three_neutrality_split(int lower, int upper, int base, int lag,
                                long double sigma);


/* -- compatible prime and squarefree residue channels ---------- */

int    compatible_residue_channels_inspect(int integer, int prime,
                                           int base, int lag);
int    compatible_residue_channels_internal(int prime, int base, int lag);
int    compatible_residue_channels_prime(int prime, int base, int lag);
int    compatible_residue_channels_squarefree(int squarefree, int base, int lag);
int    compatible_residue_channels_character_signs(int cutoff);
int    compatible_residue_channels_magnitude_correlations(int cutoff);
int    compatible_residue_channels_assignment_null(int cutoff);


/* -- centered tables and finite character objects --------------- */

int    centered_collision_table_inspect(int base, int lag, int residue);


int    finite_character_pairing_one(int base, int lag, int cutoff);
int    finite_character_pairing_declared_rows(int cutoff);


int    coprime_base_orthogonality_pair(int left_base, int left_lag,
                                       int right_base, int right_lag);
int    coprime_base_common_quotient(int left_base, int left_lag,
                                    int right_base, int right_lag);


int    natural_prime_sum_window_base_boundaries(int cutoff);
int    natural_prime_sum_window_common_tail(int lower, int cutoff);


/* -- primitive odd and additive reflection objects -------------- */

int    primitive_odd_sector_inspect(int base, int cutoff);


int    additive_reflection_well_inspect(int base);


int    reflected_prime_pair_sign_sweep(int base, int maximum_even);


/* -- collision-spectrum and special-value objects ---------------- */

int    collision_spectrum_factorization_inspect(
           int base, int character_index);
int    collision_spectrum_factorization_transform(
           int base, int character_index, int multiplier);


int    short_sum_bernoulli_correlation_moments(int base);


/* -- primitive cancellation and periodic-zeta objects ------------ */

int    primitive_character_cancellation_inspect(
           int base, int lag, int character_index);


int    periodic_zeta_factorization_inspect(
           int base, int lag, int character_index,
           long double sigma, long double tau);


int    collision_boundary_recovery_inspect(
           int base, int lag, int character_index);


int    active_collision_channel_inspect(
           int base, int lag, int character_index);
int    active_collision_channel_census(int base, int lag);


/* -- finite collision-coordinate and residue-table objects ------ */

int    collision_coordinate_values(
           int prime, int base, int multiplier,
           int *direct_count, int *formula_count, int *coordinate);
int    collision_coordinate_conjugation_values(
           int modulus, int base, int multiplier,
           int *direct_count, int *congruence_count, int *structure_ok);
int    collision_coordinate_conjugation(
           int modulus, int multiplier, int base);
int    collision_coordinate_inspect(int prime, int multiplier, int base);
int    collision_coordinate_gate(int prime, int base);


int    finite_determination_compare(
           int integer, int base, int lag,
           int *table_value, int *direct_value);
int    finite_determination_slice_values(
           int integer, int base, int lag,
           int *direct_collision, int *slice_collision,
           int *diagonal_count, int *structure_ok);
int    finite_determination_inspect(int integer, int base, int lag);
int    finite_determination_optimal(int base, int lag);


int    reflection_identity_pair_values(
           int base, int lag, int residue,
           int *value, int *reflected_value);
int    reflection_identity_local_values(
           int base, int lag, int residue,
           int *interior_count, int *structure_ok);
int    reflection_identity_inspect(int base, int lag, int residue);
int    reflection_identity_table(int base, int lag);


int    half_group_cardinality(
           int modulus, int index, int *wrapping_count, int *totient);
int    half_group_reflection_values(
           int modulus, int index, int *unit_count, int *structure_ok);
int    half_group_inspect(int modulus, int index);


/* -- all-prime labels and the finite spectral quotient ---------- */

int    all_prime_collision_label_value(
           int prime, int base, int lag,
           int *direct_label, int *table_label, int *uses_unit_table);
int    all_prime_collision_label_inspect(int prime, int base, int lag);


int    finite_spectral_quotient_metrics(
           int base, int lag, int prime_count, double tau,
           int *label_count, int *bulk_multiplicity,
           double *maximum_action_error);
int    finite_spectral_quotient_inspect(
           int base, int lag, int prime_count, double tau);


/* -- finite-prefix cylinder and carry-slice object -------------- */

int    finite_prefix_slice_identity(
           int denominator, int base, int depth,
           const int *weights, int weight_count,
           long long *intrinsic_count, long long *carry_count,
           long long *bulk_weight, long long *left_numerator,
           long long *right_numerator);
int    finite_prefix_slice_identity_all_denominators(
           int denominator, int base, int depth,
           const int *weights, int weight_count,
           long long *intrinsic_count, long long *boundary_count,
           long long *bulk_weight, long long *left_numerator,
           long long *right_numerator);
int    positional_transport_collapse(
           int denominator, int base,
           int *transient_denominator, int *persistent_denominator,
           int *collapse_depth, int *stable_kernel_size,
           int *stable_image_size);
int    finite_prefix_slice_inspect(
           int denominator, int base, int depth, const char *support);
int    finite_prefix_slice_inspect_all_denominators(
           int denominator, int base, int depth, const char *support);
int    positional_transport_collapse_inspect(int denominator, int base);
int    finite_prefix_slice_collision(int denominator, int base, int lag);


/* -- oriented comparison on the two-digit square carrier ------- */

int    oriented_digit_comparison_response_direct(
           int base, int phase, int *response);
int    oriented_digit_comparison_response_formula(
           int base, int phase, int *response);
int    oriented_digit_comparison_boundary_norm(
           int base, int *norm_squared);
int    oriented_digit_comparison_intrinsic_count(
           int denominator, int base, long long *count);
int    oriented_digit_comparison_inspect(int base, int phase);
int    oriented_digit_comparison_prime(int prime);
int    oriented_digit_comparison_trichotomy(
           int prime, int row_index, int height);


/* -- visible boundary and Bernoulli factorization object -------- */

enum { NFIELD_CARRY_BOUNDARY_MAX_DEPTH = 16 };

typedef struct {
    int prime;
    int depth;
    int modulus;
    int odd_channels;
    int conductor_channels[NFIELD_CARRY_BOUNDARY_MAX_DEPTH];
    long double direct_energy;
    long double spectral_energy;
    long double conductor_energy[NFIELD_CARRY_BOUNDARY_MAX_DEPTH];
    long double maximum_factorization_error;
    long double maximum_boundary_pairing_error;
    long double unit_reconstruction_error;
    long double energy_error;
} CarryBoundarySpectrumSummary;

int    boundary_bernoulli_factorization_compare(
           int prime, int depth, int character_exponent,
           const int *weights, int weight_count,
           long double *factorization_error, long double *boundary_error,
           int *visible_endpoints);
int    boundary_bernoulli_factorization_inspect(
           int prime, int depth, int character_exponent,
           const char *support);
int    boundary_bernoulli_factorization_terminal(
           int prime, int depth, int character_exponent);
int    boundary_bernoulli_conductor_spectrum(
           int prime, int depth, const int *weights, int weight_count,
           CarryBoundarySpectrumSummary *summary);
int    boundary_bernoulli_factorization_spectrum(
           int prime, int depth, const char *support);
int    boundary_sawtooth_correlation(
           int prime, int depth, int first, int second,
           long double *direct, long double *dedekind,
           long double *error);
int    boundary_sawtooth_correlation_inspect(
           int prime, int depth, int first, int second);


/* -- exact conductor ledger for arbitrary finite boundaries ----- */

enum { NFIELD_BOUNDARY_LEDGER_MAX_ROWS = 256 };

typedef struct {
    int divisor;
    int mobius;
    int totient;
    int pushdown_nonzero;
    long long diagonal;
    long long antipodal;
    long long difference;
    long long twice_contribution;
} BoundaryConductorLedgerRow;

typedef struct {
    int conductor;
    int primitive_odd_characters;
    long long energy;
} BoundaryConductorEnergyRow;

typedef struct {
    int modulus;
    int row_count;
    int energy_count;
    int primitive_odd_characters;
    int formal_boundary;
    int cyclic_boundary_points;
    int antipodal_odd;
    int conductor_balance;
    int proper_pushdowns_vanish;
    int top_concentrated;
    long long unit_norm;
    long long primitive_odd_moment;
    long long top_conductor_energy;
    long long proper_conductor_energy;
    long long full_odd_energy;
    long long mean_numerator;
    long long mean_denominator;
    BoundaryConductorLedgerRow row[NFIELD_BOUNDARY_LEDGER_MAX_ROWS];
    BoundaryConductorEnergyRow energy[NFIELD_BOUNDARY_LEDGER_MAX_ROWS];
} BoundaryConductorLedgerSummary;

int    boundary_conductor_ledger_compute(
           int modulus, const int *weights, int weight_count,
           BoundaryConductorLedgerSummary *summary);
int    boundary_conductor_ledger_inspect(
           int modulus, const char *support);
int    boundary_conductor_ledger_terminal(int base, int depth);


/* -- finite-state lifts of remainder orbits -------------------- */

enum { NFIELD_FINITE_STATE_MAX_CYCLE = 4096 };

typedef struct {
    int base;
    int modulus;
    int state_count;
    int start_remainder;
    int start_state;
    int state_space_size;
    int remainder_period;
    int transient_length;
    int cycle_length;
    int boolean_weight;
    int boundary_nonzero;
    long long cycle_weight_sum;
    long long boundary_sum;
    long long boundary_squared_norm;
    int cycle_remainder[NFIELD_FINITE_STATE_MAX_CYCLE];
    int cycle_state[NFIELD_FINITE_STATE_MAX_CYCLE];
    int cycle_digit[NFIELD_FINITE_STATE_MAX_CYCLE];
    int cycle_weight[NFIELD_FINITE_STATE_MAX_CYCLE];
    int dynamical_boundary[NFIELD_FINITE_STATE_MAX_CYCLE];
} FiniteStateOrbitBoundarySummary;

int    finite_state_orbit_boundary_compute(
           int base, int modulus, int state_count,
           int start_remainder, int start_state,
           const int *transition, int transition_count,
           const int *weights, int weight_count,
           FiniteStateOrbitBoundarySummary *summary);
int    finite_state_orbit_boundary_inspect(
           int base, int modulus, int state_count,
           int start_remainder, int start_state,
           const char *transition, const char *accepting,
           const char *state_weights);
int    finite_state_orbit_boundary_parity(
           int base, int modulus, int start_remainder);


/* -- additive boundaries of multiplicative remainder orbits ---- */

int    full_orbit_energy_values(
           int base, int prime, int depth,
           long long *kernel_energy, long long *closed_energy,
           int *orbit_size, int *thickness);
int    full_orbit_energy_inspect(int base, int prime, int depth);


int    quadratic_orbit_energy_values(
           int prime, long long *full_odd_energy,
           long long *resonant_energy, long long *off_resonance_energy,
           long long *closed_energy, int *off_resonance_characters);
int    quadratic_orbit_energy_inspect(int prime);


int    subgroup_jacobi_expansion_compare(
           int prime, int base, int character_exponent,
           long double *error, int *order, int *index, int *resonant);
int    subgroup_jacobi_expansion_inspect(
           int prime, int base, int character_exponent);


/* -- prime-base cubic collision energy and secondary defect ----- */

typedef struct {
    int base;
    int modulus;
    int unit_count;
    long long energy_numerator;
    long long energy_denominator;
    long long raw_variance;
    long long half_centered_square;
    long long dedekind_scaled_numerator;
    long long diagonal_scaled_numerator;
    long long upper_scaled_numerator;
    long long lower_scaled_numerator;
    int threshold_equivalence;
    int column_law;
    int reflection_law;
    int threshold_normalization;
    int weight_law;
    int correction_cancellation;
    int inverse_symmetry;
    int energy_dictionary;
} PrimeBaseCollisionEnergy;

int    prime_base_collision_energy_dedekind(
           int base, long long *total_scaled, long long *diagonal_scaled,
           long long *upper_scaled, long long *lower_scaled,
           int *weight_law, int *correction_cancellation,
           int *inverse_symmetry);
int    prime_base_collision_energy_values(
           int base, PrimeBaseCollisionEnergy *result);
int    prime_base_collision_energy_inspect(int base);
int    prime_base_collision_energy_poles(int base);


int    arithmetic_boundary_defect_metrics(
           int base, long double *energy_ratio,
           long double *secondary_ratio, long double *predicted_coefficient);
int    arithmetic_boundary_defect_inspect(int base);
int    arithmetic_boundary_defect_scan(int maximum_base);


/* -- carry-completed cyclic carriers and coherent product Grams -- */

typedef struct {
    int clock_size;
    int source_prime;
    int source_step;
    int source_order;
    int complement_generator;
    int factor_length;
    int transition_conjugacy;
    int half_turn_complement;
    int coprime_factorization;
    long long completed_size;
    long long sheet_quotient_size;
    long long clock_quotient_size;
    long long degree_zero_cells;
    long long degree_one_cells;
    long long degree_two_cells;
    long double least_positive_hodge;
} CarryCompletedCarrierSummary;

typedef struct {
    int first_length;
    int second_length;
    int first_step;
    int second_step;
    int clock_size;
    int frequency_bijection;
    int golden_polynomial_hits;
    long double constant_response;
    long double trace;
    long double first_centered_response;
    long double second_centered_response;
} CarryCompletedCarrierGramSummary;

int    carry_completed_carrier_compute(
           int clock_size, int source_prime, int source_step,
           CarryCompletedCarrierSummary *summary);
int    carry_completed_carrier_seam_values(
           int clock_size,
           long long *projected_numerator,
           long long *projected_denominator,
           long long *transverse_numerator,
           long long *transverse_denominator,
           long long *translated_numerator,
           long long *translated_denominator);
int    carry_completed_carrier_product_gram(
           int first_length, int second_length,
           int first_step, int second_step,
           CarryCompletedCarrierGramSummary *summary);
int    carry_completed_carrier_inspect(
           int clock_size, int source_prime, int source_step);
int    carry_completed_carrier_seam(int clock_size);
int    carry_completed_carrier_product(
           int first_length, int second_length,
           int first_step, int second_step);


/* -- reciprocal-square threshold selection ------------------- */

int    reciprocal_square_selection_alignment_fraction(
           int prime, int resolution,
           long long *numerator, long long *denominator);
int    reciprocal_square_selection_threshold_sign(
           int prime, int resolution, long long *certificate);
int    reciprocal_square_selection_cubic_remainder(
           int prime, int *linear_coefficient);
int    reciprocal_square_selection_inspect(
           int prime, int resolution, int base);
int    reciprocal_square_selection_cubic(int prime);
int    reciprocal_square_selection_table(void);
int    reciprocal_square_selection_scan(int maximum_prime);


/* -- weighted one-digit reference profile ------------------- */

int    weighted_reference_profile_inspect(
           int modulus, int supported, int base,
           long long lambda_num, long long lambda_den);
int    weighted_reference_profile_branch(int modulus, int exponent);

int    weighted_reference_profile_reflection_product(int modulus);
int    weighted_reference_profile_oriented_words(int modulus);

int    weighted_reference_profile_finite_orbit(
           int supported, int steps, int base);


/* ── Spectral coherence geometry (Watson framework) ──── */

void   coherence_print(int base, int N);

/* ── Legacy analytic-command compatibility ───────────── */

void   analytic_print(int base, int lag);

/* ── Scale (deficit lattice) ──────────────────────────── */

void   scale_print(int chromatic, int alpha_form, int csv);

/* ── Verification ────────────────────────────────────── */


int    digit_partition_inspect(int n, int base, int depth);
void   digit_partition_primes(int base);
void   digit_partition_table(void);


int    alignment_limit_inspect(int p, int m, int base, int depth);
int    alignment_limit_cosets(int p, int base);
int    alignment_limit_table(int base, int max_prime);
int    alignment_limit_sharpness(int steps);


int    three_tier_inspect(int n, int base, int depth);
int    three_tier_classify(int maximum, int base);
int    three_tier_scan(int maximum, int base);


int    deficit_lattice_is_supported(long long m, int base);
int    deficit_lattice_alignment_fraction(int p, long long m,
                                          long long *numerator,
                                          long long *denominator);
int    deficit_lattice_deficit_fraction(int p, long long m,
                                        long long *numerator,
                                        long long *denominator);
int    deficit_lattice_ratio_fraction(int p, long long m1, long long m2,
                                      long long *numerator,
                                      long long *denominator);
int    deficit_lattice_inspect(int p, long long m, int base);
int    deficit_lattice_ratio(int p, long long u, long long v,
                             int base, long long factor);
int    deficit_lattice_pythagorean(long long factor);
int    deficit_lattice_major_scale(long long factor);
int    deficit_lattice_chromatic_scale(long long factor);


int    coherence_decomposition_fractions(
           int n, int base, int depth,
           long long *alpha_numerator, long long *alpha_denominator,
           long long *sigma_numerator, long long *sigma_denominator,
           long long *focused_numerator, long long *focused_denominator);
int    coherence_decomposition_inspect(int n, int base, int depth);
int    coherence_decomposition_prime_core(int p, int supported,
                                          int base, int depth);
int    coherence_decomposition_pairs(int n, int base, int depth);
int    coherence_decomposition_sigma_zero(int maximum_prime, int base);
int    coherence_decomposition_golden_gap(int base);


int    cross_alignment_entry_fraction(int n, int base, int depth,
                                      int row, int column,
                                      long long *numerator,
                                      long long *denominator);
int    cross_alignment_scalar_fractions(
           int n, int base, int depth,
           long long *alpha_numerator, long long *alpha_denominator,
           long long *sigma_numerator, long long *sigma_denominator,
           long long *focused_numerator, long long *focused_denominator);
int    cross_alignment_eigenvalues(int p, int base, double *eigenvalues,
                                   int capacity, int *count,
                                   int *order, int *cosets);
int    cross_alignment_matrix_print(int n, int base, int depth);
int    cross_alignment_prime_print(int p, int base);
int    cross_alignment_fourier_print(int p, int base);
int    cross_alignment_block_print(int p, int supported,
                                   int base, int depth);


int    spectral_structure_metrics(int p, int base,
                                  int *order, int *cosets, int *occupied,
                                  int *rank, int *rank_bound,
                                  int *nullity, int *nullity_bound);
int    spectral_structure_cross_equality(int p, int base, int *values,
                                         int capacity, int *count);
int    spectral_structure_inspect(int p, int base);
int    spectral_structure_two_coset(int p, int base);
int    spectral_structure_character_energy(int p, int base);


#endif /* NFIELD_RESEARCH_ARITHMETIC_H */
