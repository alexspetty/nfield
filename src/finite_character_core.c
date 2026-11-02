/* Shared exact-table and finite-character arithmetic for object verifiers. */

#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "finite_character_core.h"

#define ACTIVE_COEFFICIENT_TOLERANCE 1.0e-10L
#define PRODUCT_SIGN_TOLERANCE 1.0e-12L

int finite_character_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0)
            return 0;
    return 1;
}

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

static int primitive_root_modulus(int modulus, int order)
{
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
        for (int i = 0; valid && i < factor_count; i++)
            if (modular_power(candidate, order / factors[i], modulus) == 1)
                valid = 0;
        if (valid) return candidate;
    }
    return 0;
}

static int primitive_root(const CollisionCenteredTable *table)
{
    return primitive_root_modulus(table->modulus, table->phi);
}

int *finite_character_primes(int limit, int *prime_count)
{
    unsigned char *composite;
    int *primes;
    int count = 0;

    if (!prime_count || limit < 3 || limit > FINITE_CHARACTER_MAX_CUTOFF)
        return NULL;
    composite = calloc((size_t)limit, 1);
    if (!composite) return NULL;
    composite[0] = composite[1] = 1;
    for (int prime = 2; prime <= (limit - 1) / prime; prime++) {
        if (composite[prime]) continue;
        for (int64_t multiple = (int64_t)prime * prime;
             multiple < limit; multiple += prime)
            composite[multiple] = 1;
    }
    for (int value = 2; value < limit; value++)
        if (!composite[value]) count++;
    primes = malloc((size_t)count * sizeof(*primes));
    if (!primes) {
        free(composite);
        return NULL;
    }
    count = 0;
    for (int value = 2; value < limit; value++)
        if (!composite[value]) primes[count++] = value;
    free(composite);
    *prime_count = count;
    return primes;
}

long double centered_collision_value(const CollisionCenteredTable *table,
                                     int residue)
{
    return (long double)table->centered_numerator[residue] /
           table->fiber_count[residue % table->base];
}

int centered_collision_table_audit(const CollisionCenteredTable *table,
                                   int *reflection_cases,
                                   int *fiber_cases)
{
    int failures = 0;
    int reflections = 0;
    int fibers = 0;
    int64_t raw_total = 0;

    if (!table || table->base < 2 || table->lag < 1) return 1;
    for (int fiber = 0; fiber < table->base; fiber++) {
        int64_t centered_sum = 0;
        int expected = collision_table_gcd(fiber, table->base) == 1
                           ? table->fiber_size : 0;
        if (table->fiber_count[fiber] != expected) failures++;
        for (int residue = 1; residue < table->modulus; residue++)
            if (collision_table_gcd(residue, table->modulus) == 1 &&
                residue % table->base == fiber)
                centered_sum += table->centered_numerator[residue];
        if (centered_sum != 0) failures++;
        if (expected > 0) fibers++;
    }

    for (int residue = 1; residue < table->modulus; residue++) {
        int reflected;
        if (collision_table_gcd(residue, table->modulus) != 1) continue;
        reflected = table->modulus - residue;
        raw_total += table->value[residue];
        if (table->value[residue] + table->value[reflected] != -1)
            failures++;
        if (table->centered_numerator[residue] +
            table->centered_numerator[reflected] != 0)
            failures++;
        reflections++;
    }
    if (2 * raw_total != -table->phi) failures++;
    if (reflection_cases) *reflection_cases = reflections;
    if (fiber_cases) *fiber_cases = fibers;
    return failures;
}

int finite_character_pairing_audit(const CollisionCenteredTable *table,
                                   const int *primes,
                                   int prime_count,
                                   const int *cutoffs,
                                   int cutoff_count,
                                   FiniteCharacterPairingAudit *audit)
{
    int generator;
    int odd;
    int *discrete_log = NULL;
    long double *weights = NULL;
    long double complex *coefficients = NULL;
    long double complex *prime_sums = NULL;
    long double two_pi = 2.0L * acosl(-1.0L);
    int failures = 0;
    int value = 1;

    if (!table || !primes || prime_count < 1 || !cutoffs || !audit ||
        cutoff_count < 1 || cutoff_count > FINITE_CHARACTER_MAX_CUTOFFS)
        return 1;
    memset(audit, 0, sizeof(*audit));
    audit->cutoff_count = cutoff_count;
    generator = primitive_root(table);
    odd = table->phi / 2;
    audit->odd = odd;
    if (!generator || odd < 1) return 1;

    discrete_log = malloc((size_t)table->modulus * sizeof(*discrete_log));
    weights = calloc((size_t)cutoff_count * table->modulus,
                     sizeof(*weights));
    coefficients = calloc((size_t)odd, sizeof(*coefficients));
    prime_sums = calloc((size_t)cutoff_count * odd, sizeof(*prime_sums));
    if (!discrete_log || !weights || !coefficients || !prime_sums) {
        failures = 1;
        goto cleanup;
    }

    for (int residue = 0; residue < table->modulus; residue++)
        discrete_log[residue] = -1;
    for (int index = 0; index < table->phi; index++) {
        discrete_log[value] = index;
        value = (int)((int64_t)value * generator % table->modulus);
    }

    for (int index = 0; index < prime_count; index++) {
        int prime = primes[index];
        if (prime <= table->modulus) continue;
        for (int cutoff_index = 0; cutoff_index < cutoff_count;
             cutoff_index++) {
            if (prime >= cutoffs[cutoff_index]) continue;
            weights[(size_t)cutoff_index * table->modulus +
                    prime % table->modulus] += 1.0L / sqrtl((long double)prime);
            audit->prime_count[cutoff_index]++;
        }
    }

#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (int character = 0; character < odd; character++) {
        int exponent = 2 * character + 1;
        long double complex coefficient = 0.0L + I * 0.0L;
        for (int residue = 1; residue < table->modulus; residue++) {
            long double angle;
            long double complex chi;
            if (discrete_log[residue] < 0) continue;
            angle = two_pi * exponent * discrete_log[residue] / table->phi;
            chi = cosl(angle) + I * sinl(angle);
            coefficient += centered_collision_value(table, residue) *
                           conjl(chi);
            for (int cutoff_index = 0; cutoff_index < cutoff_count;
                 cutoff_index++) {
                long double weight =
                    weights[(size_t)cutoff_index * table->modulus + residue];
                prime_sums[(size_t)cutoff_index * odd + character] +=
                    weight * chi;
            }
        }
        coefficients[character] = coefficient / table->phi;
    }

    for (int character = 0; character < odd; character++) {
        int exponent = 2 * character + 1;
        int inactive = exponent % table->fiber_size == 0;
        long double magnitude = cabsl(coefficients[character]);
        if (inactive) {
            audit->inactive++;
            if (magnitude > ACTIVE_COEFFICIENT_TOLERANCE) failures++;
        } else {
            audit->active++;
            if (magnitude < ACTIVE_COEFFICIENT_TOLERANCE) failures++;
        }
    }

    for (int cutoff_index = 0; cutoff_index < cutoff_count; cutoff_index++) {
        FiniteCharacterPairingStats *stats = &audit->stats[cutoff_index];
        long double sx = 0.0L, sy = 0.0L;
        long double sxx = 0.0L, syy = 0.0L, sxy = 0.0L;

        for (int residue = 1; residue < table->modulus; residue++)
            if (collision_table_gcd(residue, table->modulus) == 1)
                stats->direct += centered_collision_value(table, residue) *
                    weights[(size_t)cutoff_index * table->modulus + residue];

        for (int character = 0; character < odd; character++) {
            int exponent = 2 * character + 1;
            long double product, x, y;
            if (exponent % table->fiber_size == 0) continue;
            product = creall(coefficients[character] *
                prime_sums[(size_t)cutoff_index * odd + character]);
            stats->net += product;
            if (product > PRODUCT_SIGN_TOLERANCE) stats->positive++;
            else if (product < -PRODUCT_SIGN_TOLERANCE) stats->negative++;
            else stats->zero_product++;
            x = cabsl(coefficients[character]);
            y = cabsl(prime_sums[(size_t)cutoff_index * odd + character]);
            sx += x;
            sy += y;
            sxx += x * x;
            syy += y * y;
            sxy += x * y;
        }
        stats->decomposition_error = stats->net - stats->direct;
        if (!isfinite(stats->decomposition_error) ||
            fabsl(stats->decomposition_error) >
                1.0e-9L * (1.0L + fabsl(stats->direct)))
            failures++;
        if (audit->active > 0) {
            long double mean_x = sx / audit->active;
            long double mean_y = sy / audit->active;
            long double variance_x = sxx / audit->active - mean_x * mean_x;
            long double variance_y = syy / audit->active - mean_y * mean_y;
            long double covariance = sxy / audit->active - mean_x * mean_y;
            long double threshold_x = 1.0e-24L * (1.0L + mean_x * mean_x);
            long double threshold_y = 1.0e-24L * (1.0L + mean_y * mean_y);
            if (variance_x > threshold_x && variance_y > threshold_y) {
                stats->correlation_defined = 1;
                stats->correlation = covariance /
                    sqrtl(variance_x * variance_y);
            }
        }
    }

cleanup:
    free(discrete_log);
    free(weights);
    free(coefficients);
    free(prime_sums);
    return failures;
}

typedef struct {
    int modulus;
    int order;
    int generator;
    int *exponent;
} FiniteGroupFactor;

typedef struct {
    int modulus;
    int unit_count;
    int factor_count;
    int *units;
    FiniteGroupFactor factors[FINITE_CHARACTER_MAX_FACTORS];
} FiniteCharacterGroup;

static int finite_group_phi(int value)
{
    int result = value;
    int remaining = value;
    for (int prime = 2; prime <= remaining / prime; prime++) {
        if (remaining % prime != 0) continue;
        result -= result / prime;
        while (remaining % prime == 0) remaining /= prime;
    }
    if (remaining > 1) result -= result / remaining;
    return result;
}

static int *finite_group_empty_exponents(int modulus)
{
    int *exponent = malloc((size_t)modulus * sizeof(*exponent));
    if (!exponent) return NULL;
    for (int residue = 0; residue < modulus; residue++) exponent[residue] = -1;
    return exponent;
}

static int finite_group_add_factor(FiniteCharacterGroup *group,
                                   int modulus, int order, int generator,
                                   int *exponent)
{
    if (!group || !exponent || order < 1 ||
        group->factor_count >= FINITE_CHARACTER_MAX_FACTORS)
        return 0;
    FiniteGroupFactor *factor = &group->factors[group->factor_count++];
    factor->modulus = modulus;
    factor->order = order;
    factor->generator = generator;
    factor->exponent = exponent;
    return 1;
}

static int finite_group_add_cyclic_factor(FiniteCharacterGroup *group,
                                          int modulus, int order,
                                          int generator)
{
    int *exponent = finite_group_empty_exponents(modulus);
    int residue = 1;
    if (!exponent) return 0;
    for (int index = 0; index < order; index++) {
        if (exponent[residue] >= 0) {
            free(exponent);
            return 0;
        }
        exponent[residue] = index;
        residue = (int)((int64_t)residue * generator % modulus);
    }
    if (residue != 1 || !finite_group_add_factor(
            group, modulus, order, generator, exponent)) {
        free(exponent);
        return 0;
    }
    return 1;
}

static int finite_group_add_two_power(FiniteCharacterGroup *group,
                                      int modulus, int power)
{
    if (power == 1) return 1;
    if (power == 2)
        return finite_group_add_cyclic_factor(group, modulus, 2, 3);

    int *sign = finite_group_empty_exponents(modulus);
    int *five = finite_group_empty_exponents(modulus);
    int order = 1 << (power - 2);
    int residue = 1;
    if (!sign || !five) {
        free(sign);
        free(five);
        return 0;
    }
    for (int unit = 1; unit < modulus; unit += 2)
        sign[unit] = unit % 4 == 1 ? 0 : 1;
    for (int index = 0; index < order; index++) {
        five[residue] = index;
        five[(modulus - residue) % modulus] = index;
        residue = (int)((int64_t)residue * 5 % modulus);
    }
    if (residue != 1 ||
        !finite_group_add_factor(group, modulus, 2, modulus - 1, sign)) {
        free(sign);
        free(five);
        return 0;
    }
    if (!finite_group_add_factor(group, modulus, order, 5, five)) {
        group->factor_count--;
        free(sign);
        free(five);
        return 0;
    }
    return 1;
}

static void finite_group_free(FiniteCharacterGroup *group)
{
    if (!group) return;
    for (int factor = 0; factor < group->factor_count; factor++)
        free(group->factors[factor].exponent);
    free(group->units);
    memset(group, 0, sizeof(*group));
}

static int finite_group_build(int modulus, FiniteCharacterGroup *group)
{
    int remaining;
    int unit_index = 0;
    int character_count = 1;

    if (!group || modulus < 2 ||
        modulus > FINITE_CHARACTER_SPECTRUM_MAX_MODULUS)
        return 0;
    memset(group, 0, sizeof(*group));
    group->modulus = modulus;
    group->unit_count = finite_group_phi(modulus);
    group->units = malloc((size_t)group->unit_count * sizeof(*group->units));
    if (!group->units) return 0;
    for (int residue = 1; residue < modulus; residue++)
        if (collision_table_gcd(residue, modulus) == 1)
            group->units[unit_index++] = residue;
    if (unit_index != group->unit_count) {
        finite_group_free(group);
        return 0;
    }

    remaining = modulus;
    for (int prime = 2; prime <= remaining / prime; prime++) {
        int power = 0;
        int prime_power = 1;
        int generator;
        if (remaining % prime != 0) continue;
        while (remaining % prime == 0) {
            remaining /= prime;
            prime_power *= prime;
            power++;
        }
        if (prime == 2) {
            if (!finite_group_add_two_power(group, prime_power, power)) {
                finite_group_free(group);
                return 0;
            }
            continue;
        }
        generator = primitive_root_modulus(
            prime_power, finite_group_phi(prime_power));
        if (!generator || !finite_group_add_cyclic_factor(
                group, prime_power, finite_group_phi(prime_power),
                generator)) {
            finite_group_free(group);
            return 0;
        }
    }
    if (remaining > 1) {
        if (remaining == 2) {
            if (!finite_group_add_two_power(group, 2, 1)) {
                finite_group_free(group);
                return 0;
            }
        } else {
            int generator = primitive_root_modulus(remaining, remaining - 1);
            if (!generator || !finite_group_add_cyclic_factor(
                    group, remaining, remaining - 1, generator)) {
                finite_group_free(group);
                return 0;
            }
        }
    }

    for (int factor = 0; factor < group->factor_count; factor++)
        character_count *= group->factors[factor].order;
    if (character_count != group->unit_count) {
        finite_group_free(group);
        return 0;
    }
    return 1;
}

static int64_t finite_group_gcd64(int64_t left, int64_t right)
{
    while (right != 0) {
        int64_t next = left % right;
        left = right;
        right = next;
    }
    return left < 0 ? -left : left;
}

static int64_t finite_group_phase_denominator(
    const FiniteCharacterGroup *group)
{
    int64_t denominator = 1;
    for (int factor = 0; factor < group->factor_count; factor++) {
        int64_t order = group->factors[factor].order;
        denominator = denominator / finite_group_gcd64(denominator, order) *
                      order;
    }
    return denominator;
}

static int64_t finite_group_phase_numerator(
    const FiniteCharacterGroup *group, const int *coordinates, int residue,
    int64_t denominator)
{
    int64_t numerator = 0;
    for (int factor = 0; factor < group->factor_count; factor++) {
        const FiniteGroupFactor *component = &group->factors[factor];
        int local = residue % component->modulus;
        int exponent = component->exponent[local];
        if (exponent < 0) return -1;
        numerator += (int64_t)coordinates[factor] * exponent *
                     (denominator / component->order);
    }
    numerator %= denominator;
    if (numerator < 0) numerator += denominator;
    return numerator;
}

static long double complex finite_group_character_value(
    const FiniteCharacterGroup *group, const int *coordinates, int residue,
    int64_t denominator)
{
    int64_t numerator = finite_group_phase_numerator(
        group, coordinates, residue, denominator);
    long double angle;
    if (numerator < 0) return 0.0L;
    angle = 2.0L * acosl(-1.0L) * numerator / denominator;
    return cosl(angle) + I * sinl(angle);
}

static int finite_group_factors_through(
    const FiniteCharacterGroup *group, const int *coordinates, int level,
    int64_t denominator)
{
    int identity = 1 % level;
    for (int index = 0; index < group->unit_count; index++) {
        int residue = group->units[index];
        if (residue % level != identity) continue;
        if (finite_group_phase_numerator(
                group, coordinates, residue, denominator) != 0)
            return 0;
    }
    return 1;
}

void finite_character_table_free(FiniteCharacterTable *table)
{
    if(!table) return;
    free(table->phase); free(table->conductor); free(table->odd);
    memset(table,0,sizeof *table);
}
int finite_character_table_build(int modulus,FiniteCharacterTable *out)
{
    if(!out || out->phase || out->conductor || out->odd || modulus<2 ||
       modulus>FINITE_CHARACTER_TABLE_MAX_MODULUS) return 0;
    FiniteCharacterGroup group={0}; FiniteCharacterTable table={0};
    if(!finite_group_build(modulus,&group)) return 0;
    table.modulus=modulus; table.count=group.unit_count;
    table.denominator=(int)finite_group_phase_denominator(&group);
    table.phase=malloc((size_t)table.count*modulus*sizeof *table.phase);
    table.conductor=calloc((size_t)table.count,sizeof *table.conductor);
    table.odd=calloc((size_t)table.count,sizeof *table.odd);
    if(!table.phase || !table.conductor || !table.odd) goto fail;
    for(int ch=0;ch<table.count;ch++) {
        int index=ch,coordinates[FINITE_CHARACTER_MAX_FACTORS]={0};
        for(int f=0;f<group.factor_count;f++) {
            coordinates[f]=index%group.factors[f].order; index/=group.factors[f].order;
        }
        for(int r=0;r<modulus;r++) table.phase[(size_t)ch*modulus+r]=
            collision_table_gcd(r,modulus)==1?(int)finite_group_phase_numerator(
                &group,coordinates,r,table.denominator):-1;
        table.odd[ch]=table.phase[(size_t)ch*modulus+modulus-1]!=0;
        for(int q=1;q<=modulus;q++) if(modulus%q==0 &&
           finite_group_factors_through(&group,coordinates,q,table.denominator)) {
            table.conductor[ch]=q; break;
        }
        if(!table.conductor[ch]) goto fail;
    }
    finite_group_free(&group); *out=table; return 1;
fail:
    finite_group_free(&group); finite_character_table_free(&table); return 0;
}
long double complex finite_character_table_value(const FiniteCharacterTable *table,
    unsigned ch,unsigned residue)
{
    if(!table || !table->phase || ch>=(unsigned)table->count) return 0;
    int phase=table->phase[(size_t)ch*table->modulus+residue%table->modulus];
    if(phase<0) return 0;
    long double angle=2*acosl(-1.0L)*phase/table->denominator;
    return cosl(angle)+I*sinl(angle);
}

void finite_character_spectrum_free(FiniteCharacterSpectrum *spectrum)
{
    if (!spectrum) return;
    free(spectrum->coordinates);
    free(spectrum->conjugate);
    free(spectrum->conductor);
    free(spectrum->odd);
    free(spectrum->base_factored);
    free(spectrum->resolved_active);
    free(spectrum->coefficient);
    memset(spectrum, 0, sizeof(*spectrum));
}

int finite_character_spectrum_compute(
    const CollisionCenteredTable *table, FiniteCharacterSpectrum *spectrum)
{
    FiniteCharacterGroup group = {0};
    int64_t denominator;
    int coordinate_width;
    long double signal_energy = 0.0L;
    long double coefficient_energy = 0.0L;
    int ok = 0;

    if (!table || !spectrum || table->modulus < 2 ||
        table->modulus > FINITE_CHARACTER_SPECTRUM_MAX_MODULUS ||
        table->phi < 1 || !finite_group_build(table->modulus, &group))
        return 0;
    memset(spectrum, 0, sizeof(*spectrum));
    spectrum->modulus = table->modulus;
    spectrum->character_count = group.unit_count;
    spectrum->factor_count = group.factor_count;
    spectrum->tolerance = 1.0e-11L;
    for (int factor = 0; factor < group.factor_count; factor++) {
        spectrum->factor_modulus[factor] = group.factors[factor].modulus;
        spectrum->factor_order[factor] = group.factors[factor].order;
        spectrum->factor_generator[factor] = group.factors[factor].generator;
    }

    coordinate_width = group.factor_count > 0 ? group.factor_count : 1;
    spectrum->coordinates = calloc(
        (size_t)group.unit_count * coordinate_width,
        sizeof(*spectrum->coordinates));
    spectrum->conjugate = calloc(
        (size_t)group.unit_count, sizeof(*spectrum->conjugate));
    spectrum->conductor = calloc(
        (size_t)group.unit_count, sizeof(*spectrum->conductor));
    spectrum->odd = calloc((size_t)group.unit_count, sizeof(*spectrum->odd));
    spectrum->base_factored = calloc(
        (size_t)group.unit_count, sizeof(*spectrum->base_factored));
    spectrum->resolved_active = calloc(
        (size_t)group.unit_count, sizeof(*spectrum->resolved_active));
    spectrum->coefficient = calloc(
        (size_t)group.unit_count, sizeof(*spectrum->coefficient));
    if (!spectrum->coordinates || !spectrum->conjugate ||
        !spectrum->conductor || !spectrum->odd ||
        !spectrum->base_factored || !spectrum->resolved_active ||
        !spectrum->coefficient)
        goto cleanup;

    denominator = finite_group_phase_denominator(&group);
    for (int character = 0; character < group.unit_count; character++) {
        int index = character;
        int conjugate = 0;
        int stride = 1;
        int *coordinates = &spectrum->coordinates[
            (size_t)character * coordinate_width];
        for (int factor = 0; factor < group.factor_count; factor++) {
            int order = group.factors[factor].order;
            int opposite;
            coordinates[factor] = index % order;
            index /= order;
            opposite = coordinates[factor] == 0
                           ? 0 : order - coordinates[factor];
            conjugate += opposite * stride;
            stride *= order;
        }
        spectrum->conjugate[character] = conjugate;
        {
            int64_t negative_phase = finite_group_phase_numerator(
                &group, coordinates, table->modulus - 1, denominator);
            if (negative_phase != 0) {
                if ((2 * negative_phase) % denominator != 0) goto cleanup;
                spectrum->odd[character] = 1;
            }
        }
        spectrum->base_factored[character] =
            finite_group_factors_through(
                &group, coordinates, table->base, denominator);
        for (int level = 1; level <= table->modulus; level++) {
            if (table->modulus % level != 0) continue;
            if (finite_group_factors_through(
                    &group, coordinates, level, denominator)) {
                spectrum->conductor[character] = level;
                break;
            }
        }
        if (spectrum->conductor[character] == 0) goto cleanup;
        if (!spectrum->odd[character]) spectrum->even_count++;
        if (spectrum->base_factored[character])
            spectrum->base_factored_count++;
        if (spectrum->odd[character] &&
            !spectrum->base_factored[character])
            spectrum->allowed_count++;

        for (int unit = 0; unit < group.unit_count; unit++) {
            int residue = group.units[unit];
            long double complex value = finite_group_character_value(
                &group, coordinates, residue, denominator);
            spectrum->coefficient[character] +=
                centered_collision_value(table, residue) * conjl(value);
        }
        spectrum->coefficient[character] /= group.unit_count;
    }

    for (int character = 0; character < group.unit_count; character++) {
        long double magnitude = cabsl(spectrum->coefficient[character]);
        if (magnitude > spectrum->tolerance) {
            spectrum->resolved_active[character] = 1;
            spectrum->resolved_active_count++;
        } else {
            spectrum->resolved_zero_count++;
        }
        if (!spectrum->odd[character] &&
            magnitude > spectrum->maximum_even_coefficient)
            spectrum->maximum_even_coefficient = magnitude;
        if (spectrum->base_factored[character] &&
            magnitude > spectrum->maximum_base_factored_coefficient)
            spectrum->maximum_base_factored_coefficient = magnitude;
        coefficient_energy += magnitude * magnitude;
        {
            int opposite = spectrum->conjugate[character];
            long double error = cabsl(
                spectrum->coefficient[opposite] -
                conjl(spectrum->coefficient[character]));
            if (error > spectrum->conjugate_error)
                spectrum->conjugate_error = error;
        }
    }

    for (int unit = 0; unit < group.unit_count; unit++) {
        int residue = group.units[unit];
        long double signal = centered_collision_value(table, residue);
        long double complex reconstructed = 0.0L;
        signal_energy += signal * signal;
        for (int character = 0; character < group.unit_count; character++) {
            const int *coordinates = &spectrum->coordinates[
                (size_t)character * coordinate_width];
            reconstructed += spectrum->coefficient[character] *
                finite_group_character_value(
                    &group, coordinates, residue, denominator);
        }
        {
            long double error = cabsl(reconstructed - signal) /
                                (1.0L + fabsl(signal));
            if (error > spectrum->inversion_error)
                spectrum->inversion_error = error;
        }
    }
    spectrum->parseval_error = fabsl(
        coefficient_energy - signal_energy / group.unit_count) /
        (1.0L + signal_energy / group.unit_count);
    ok = 1;

cleanup:
    finite_group_free(&group);
    if (!ok) finite_character_spectrum_free(spectrum);
    return ok;
}
