/* Multiplicative character energy restricted to primitive odd characters. */

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "finite_character_core.h"
#include "primitive_odd_sector_core.h"

#define CONJUGATE_ENERGY_TOLERANCE 2.0e-13L

static int modular_power(int base, int exponent, int modulus)
{
    int64_t result = 1;
    int64_t power = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int primitive_root_prime_square(int prime)
{
    int modulus = prime * prime;
    int order = prime * (prime - 1);
    int factors[16];
    int factor_count = 0;
    int remaining = order;

    for (int factor = 2; factor <= remaining / factor; factor++) {
        if (remaining % factor != 0) continue;
        factors[factor_count++] = factor;
        while (remaining % factor == 0) remaining /= factor;
    }
    if (remaining > 1) factors[factor_count++] = remaining;
    for (int candidate = 2; candidate < modulus; candidate++) {
        int valid = collision_table_gcd(candidate, modulus) == 1;
        for (int index = 0; valid && index < factor_count; index++)
            if (modular_power(candidate, order / factors[index], modulus) == 1)
                valid = 0;
        if (valid) return candidate;
    }
    return 0;
}

static long double dft_magnitude_squared(const long double *values,
                                         int count,
                                         int frequency)
{
    long double theta = -2.0L * acosl(-1.0L) * frequency / count;
    long double step_real = cosl(theta);
    long double step_imaginary = sinl(theta);
    long double root_real = 1.0L;
    long double root_imaginary = 0.0L;
    long double sum_real = 0.0L;
    long double sum_imaginary = 0.0L;

    for (int exponent = 0; exponent < count; exponent++) {
        long double next_real;
        sum_real += values[exponent] * root_real;
        sum_imaginary += values[exponent] * root_imaginary;
        next_real = root_real * step_real - root_imaginary * step_imaginary;
        root_imaginary = root_real * step_imaginary +
                         root_imaginary * step_real;
        root_real = next_real;
    }
    return sum_real * sum_real + sum_imaginary * sum_imaginary;
}

static long double effective_support(const long double *pair_mass,
                                     int pair_count)
{
    long double entropy = logl(2.0L);
    for (int index = 0; index < pair_count; index++)
        if (pair_mass[index] > 0.0L)
            entropy -= pair_mass[index] * logl(pair_mass[index]);
    return expl(entropy);
}

void primitive_odd_sector_result_free(PrimitiveOddSectorResult *result)
{
    if (!result) return;
    collision_centered_table_free(&result->table);
    memset(result, 0, sizeof(*result));
}

int primitive_odd_sector_compute(int base,
                                 const int *primes,
                                 int prime_count,
                                 const int *cutoffs,
                                 int cutoff_count,
                                 PrimitiveOddSectorResult *result)
{
    int modulus;
    int phi;
    int pair_count;
    int primitive_root;
    int *residue_log = NULL;
    int *pair_frequency = NULL;
    long double *collision_signal = NULL;
    long double *prime_signal = NULL;
    long double *collision_mass = NULL;
    long double *prime_mass = NULL;
    long double collision_total = 0.0L;
    long double collision_conjugate_error = 0.0L;
    int residue = 1;
    int failures = 0;

    if (!result || !primes || prime_count < 1 || !cutoffs ||
        cutoff_count < 1 || cutoff_count > PRIMITIVE_ODD_MAX_CUTOFFS ||
        !finite_character_is_prime(base) || base == 2)
        return 1;
    memset(result, 0, sizeof(*result));
    modulus = base * base;
    phi = base * (base - 1);
    pair_count = (base - 1) * (base - 1) / 4;
    primitive_root = primitive_root_prime_square(base);
    if (pair_count < 1 || primitive_root == 0 ||
        !collision_centered_table_build(base, 1, &result->table))
        return 1;
    result->primitive_root = primitive_root;
    result->cutoff_count = cutoff_count;

    residue_log = malloc((size_t)modulus * sizeof(*residue_log));
    pair_frequency = malloc((size_t)pair_count * sizeof(*pair_frequency));
    collision_signal = calloc((size_t)phi, sizeof(*collision_signal));
    prime_signal = calloc((size_t)phi, sizeof(*prime_signal));
    collision_mass = calloc((size_t)pair_count, sizeof(*collision_mass));
    prime_mass = calloc((size_t)pair_count, sizeof(*prime_mass));
    if (!residue_log || !pair_frequency || !collision_signal ||
        !prime_signal || !collision_mass || !prime_mass) {
        failures = 1;
        goto cleanup;
    }
    for (int value = 0; value < modulus; value++) residue_log[value] = -1;
    for (int exponent = 0; exponent < phi; exponent++) {
        residue_log[residue] = exponent;
        collision_signal[exponent] =
            (long double)result->table.centered_numerator[residue];
        residue = (int)((int64_t)residue * primitive_root % modulus);
    }
    if (residue != 1) failures++;

    {
        int pair_index = 0;
        for (int frequency = 1; frequency < phi / 2; frequency += 2) {
            if (frequency % base == 0) continue;
            if (pair_index >= pair_count) {
                failures++;
                break;
            }
            pair_frequency[pair_index++] = frequency;
        }
        if (pair_index != pair_count) failures++;
    }

    for (int pair_index = 0; pair_index < pair_count; pair_index++) {
        long double forward = dft_magnitude_squared(
            collision_signal, phi, pair_frequency[pair_index]);
        long double conjugate = dft_magnitude_squared(
            collision_signal, phi, phi - pair_frequency[pair_index]);
        long double scale = fmaxl(1.0L, fmaxl(forward, conjugate));
        long double error = fabsl(forward - conjugate) / scale;
        collision_mass[pair_index] = (forward + conjugate) / 2.0L;
        collision_total += collision_mass[pair_index];
        collision_conjugate_error =
            fmaxl(collision_conjugate_error, error);
    }
    if (!(collision_total > 0.0L)) failures++;
    else {
        for (int frequency = 0; frequency < phi; frequency++) {
            long double energy;
            long double fraction;
            if (frequency % 2 != 0 && frequency % base != 0) continue;
            energy = dft_magnitude_squared(
                collision_signal, phi, frequency);
            fraction = energy / collision_total;
            if (frequency % 2 == 0 &&
                fraction > result->maximum_even_energy_fraction)
                result->maximum_even_energy_fraction = fraction;
            if (frequency % base == 0 &&
                fraction > result->maximum_induced_energy_fraction)
                result->maximum_induced_energy_fraction = fraction;
        }
        if (result->maximum_even_energy_fraction > 1.0e-16L ||
            result->maximum_induced_energy_fraction > 1.0e-16L)
            failures++;
        for (int pair_index = 0; pair_index < pair_count; pair_index++)
            collision_mass[pair_index] /= collision_total;
    }

    for (int cutoff_index = 0; cutoff_index < cutoff_count; cutoff_index++) {
        PrimitiveOddSectorRow *row = &result->row[cutoff_index];
        long double prime_active_total = 0.0L;
        long double prime_odd_total = 0.0L;
        long double prime_conjugate_error = 0.0L;
        long double overlap_sum = 0.0L;
        long double collision_square = 0.0L;
        long double prime_square = 0.0L;
        long double center = 1.0L / pair_count;
        long double full_overlap = 0.0L;

        if (cutoffs[cutoff_index] <= modulus ||
            cutoffs[cutoff_index] > FINITE_CHARACTER_MAX_CUTOFF) {
            failures++;
            continue;
        }
        memset(prime_signal, 0, (size_t)phi * sizeof(*prime_signal));
        for (int prime_index = 0; prime_index < prime_count; prime_index++) {
            int prime = primes[prime_index];
            int log_index;
            if (prime >= cutoffs[cutoff_index]) break;
            if (prime <= modulus) continue;
            log_index = residue_log[prime % modulus];
            if (log_index < 0) {
                failures++;
                continue;
            }
            prime_signal[log_index] += 1.0L / sqrtl((long double)prime);
        }

        for (int frequency = 1; frequency < phi; frequency += 2) {
            long double energy = dft_magnitude_squared(
                prime_signal, phi, frequency);
            prime_odd_total += energy;
            if (frequency % base != 0) prime_active_total += energy;
        }
        for (int pair_index = 0; pair_index < pair_count; pair_index++) {
            long double forward = dft_magnitude_squared(
                prime_signal, phi, pair_frequency[pair_index]);
            long double conjugate = dft_magnitude_squared(
                prime_signal, phi, phi - pair_frequency[pair_index]);
            long double scale = fmaxl(1.0L, fmaxl(forward, conjugate));
            long double error = fabsl(forward - conjugate) / scale;
            prime_mass[pair_index] = (forward + conjugate) / 2.0L;
            prime_conjugate_error = fmaxl(prime_conjugate_error, error);
        }
        if (!(prime_active_total > 0.0L) || !(prime_odd_total > 0.0L)) {
            failures++;
            continue;
        }
        /* Pair averages sum to half the character-by-character active mass. */
        for (int pair_index = 0; pair_index < pair_count; pair_index++) {
            prime_mass[pair_index] /= prime_active_total / 2.0L;
            overlap_sum += collision_mass[pair_index] *
                           prime_mass[pair_index];
            collision_square +=
                (collision_mass[pair_index] - center) *
                (collision_mass[pair_index] - center);
            prime_square += (prime_mass[pair_index] - center) *
                            (prime_mass[pair_index] - center);
            full_overlap += collision_mass[pair_index] *
                (2.0L * (prime_mass[pair_index] *
                 (prime_active_total / 2.0L)) / prime_odd_total);
        }
        row->odd_characters = phi / 2;
        row->active_characters = 2 * pair_count;
        row->inactive_characters = row->odd_characters -
                                   row->active_characters;
        row->conjugate_pairs = pair_count;
        row->rho = pair_count * overlap_sum;
        row->collision_support = effective_support(
            collision_mass, pair_count);
        row->prime_support = effective_support(prime_mass, pair_count);
        row->primitive_occupancy = prime_active_total / prime_odd_total;
        row->full_odd_rho = row->odd_characters * full_overlap / 2.0L;
        {
            long double factored =
                (long double)row->odd_characters /
                row->active_characters * row->primitive_occupancy * row->rho;
            row->factorization_error = row->full_odd_rho - factored;
        }
        row->conjugate_error = fmaxl(
            collision_conjugate_error, prime_conjugate_error);
        row->conjugacy_ok =
            row->conjugate_error <= CONJUGATE_ENERGY_TOLERANCE;
        if (pair_count == 1) {
            row->relabeling_variance = 0.0L;
            row->z = 0.0L;
            row->z_defined = 0;
        } else {
            row->relabeling_variance =
                ((long double)pair_count * pair_count /
                 (pair_count - 1)) * collision_square * prime_square;
            if (row->relabeling_variance > 0.0L) {
                row->z = (row->rho - 1.0L) /
                         sqrtl(row->relabeling_variance);
                row->z_defined = 1;
            }
        }
        if (!row->conjugacy_ok || !isfinite(row->rho) ||
            !isfinite(row->primitive_occupancy) ||
            !isfinite(row->full_odd_rho) ||
            fabsl(row->factorization_error) > 1.0e-11L)
            failures++;
    }

cleanup:
    free(residue_log);
    free(pair_frequency);
    free(collision_signal);
    free(prime_signal);
    free(collision_mass);
    free(prime_mass);
    if (failures) {
        primitive_odd_sector_result_free(result);
        return 1;
    }
    return 0;
}
