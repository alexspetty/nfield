/*
 * collision_character_structure.c
 *
 * Finite residue-stream and character-coordinate tools.
 *
 * Collision counts and constructive means are formed with exact integer
 * arithmetic. Character transforms and p^(-s) use long-double complex
 * arithmetic, with independently reported reconstruction residuals.
 */

#include <complex.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#ifndef M_PI
#define M_PI 3.141592653589793238462643383279502884L
#endif

#define CCS_MAX_BASE 64
#define CCS_MAX_CUTOFF 100000
#define CCS_MAX_FACTORS 16
#define CCS_TOL 1e-14L

typedef struct {
    int modulus;
    int order;
    int generator;
    int *exponent;
} CCSFactor;

typedef struct {
    int base;
    int unit_count;
    int factor_count;
    int *units;
    int *unit_index;
    CCSFactor factors[CCS_MAX_FACTORS];
    long double complex *value;
    int *conjugate;
} CCSCharacters;

typedef struct {
    int eligible_primes;
    long double complex *streams;
    long double complex *components;
    long double complex total;
} CCSSignal;

typedef struct {
    long double forward_error;
    long double inverse_error;
    long double principal_error;
    long double parseval_error;
    long double conjugate_error;
} CCSResiduals;

static int ccs_gcd(int a, int b)
{
    while (b != 0) {
        int next = a % b;
        a = b;
        b = next;
    }
    return a < 0 ? -a : a;
}

static int ccs_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int ccs_phi(int n)
{
    int result = n;
    int remaining = n;
    for (int p = 2; p <= remaining / p; p++) {
        if (remaining % p != 0) continue;
        result -= result / p;
        while (remaining % p == 0) remaining /= p;
    }
    if (remaining > 1) result -= result / remaining;
    return result;
}

static int ccs_mod_pow(int base, int exponent, int modulus)
{
    long long result = 1;
    long long power = base % modulus;
    if (power < 0) power += modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int ccs_primitive_root(int modulus)
{
    int order = ccs_phi(modulus);
    int primes[16];
    int count = 0;
    int remaining = order;
    for (int p = 2; p <= remaining / p; p++) {
        if (remaining % p != 0) continue;
        primes[count++] = p;
        while (remaining % p == 0) remaining /= p;
    }
    if (remaining > 1) primes[count++] = remaining;
    for (int g = 2; g < modulus; g++) {
        if (ccs_gcd(g, modulus) != 1) continue;
        int primitive = 1;
        for (int i = 0; i < count; i++)
            if (ccs_mod_pow(g, order / primes[i], modulus) == 1)
                primitive = 0;
        if (primitive) return g;
    }
    return 0;
}

static int ccs_valid_base(int base, int report)
{
    if (base < 2 || base > CCS_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n", CCS_MAX_BASE);
        return 0;
    }
    return 1;
}

static int ccs_valid_cutoff(int base, int cutoff, int report)
{
    if (!ccs_valid_base(base, report)) return 0;
    if (cutoff <= base + 1 || cutoff > CCS_MAX_CUTOFF) {
        if (report)
            fprintf(stderr, "cutoff must be between base+2 and %d\n",
                    CCS_MAX_CUTOFF);
        return 0;
    }
    return 1;
}

static int ccs_add_factor(CCSCharacters *system, int modulus, int order,
                          int generator, int *exponent)
{
    if (system->factor_count >= CCS_MAX_FACTORS || !exponent) return 0;
    CCSFactor *factor = &system->factors[system->factor_count++];
    factor->modulus = modulus;
    factor->order = order;
    factor->generator = generator;
    factor->exponent = exponent;
    return 1;
}

static int *ccs_empty_exponents(int modulus)
{
    int *exponent = malloc((size_t)modulus * sizeof(*exponent));
    if (!exponent) return NULL;
    for (int i = 0; i < modulus; i++) exponent[i] = -1;
    return exponent;
}

static int ccs_add_cyclic_factor(CCSCharacters *system, int modulus,
                                 int order, int generator)
{
    int *exponent = ccs_empty_exponents(modulus);
    if (!exponent) return 0;
    int value = 1;
    for (int j = 0; j < order; j++) {
        if (exponent[value] >= 0) {
            free(exponent);
            return 0;
        }
        exponent[value] = j;
        value = (int)((long long)value * generator % modulus);
    }
    if (value != 1 || !ccs_add_factor(system, modulus, order,
                                      generator, exponent)) {
        free(exponent);
        return 0;
    }
    return 1;
}

static int ccs_add_two_power_factors(CCSCharacters *system, int modulus,
                                     int exponent_power)
{
    if (exponent_power == 1) return 1;
    if (exponent_power == 2)
        return ccs_add_cyclic_factor(system, modulus, 2, 3);

    int *sign = ccs_empty_exponents(modulus);
    int *five = ccs_empty_exponents(modulus);
    if (!sign || !five) {
        free(sign);
        free(five);
        return 0;
    }
    for (int r = 1; r < modulus; r += 2)
        sign[r] = r % 4 == 1 ? 0 : 1;
    int order = 1 << (exponent_power - 2);
    int value = 1;
    for (int j = 0; j < order; j++) {
        five[value] = j;
        five[(modulus - value) % modulus] = j;
        value = (int)((long long)value * 5 % modulus);
    }
    if (!ccs_add_factor(system, modulus, 2, modulus - 1, sign)) {
        free(sign);
        free(five);
        return 0;
    }
    if (!ccs_add_factor(system, modulus, order, 5, five)) {
        system->factor_count--;
        free(sign);
        free(five);
        return 0;
    }
    return 1;
}

static void ccs_characters_free(CCSCharacters *system)
{
    for (int i = 0; i < system->factor_count; i++)
        free(system->factors[i].exponent);
    free(system->units);
    free(system->unit_index);
    free(system->value);
    free(system->conjugate);
    memset(system, 0, sizeof(*system));
}

static int ccs_characters_build(int base, CCSCharacters *system)
{
    memset(system, 0, sizeof(*system));
    if (!ccs_valid_base(base, 0)) return 0;
    system->base = base;
    system->unit_count = ccs_phi(base);
    system->units = malloc((size_t)system->unit_count * sizeof(*system->units));
    system->unit_index = malloc((size_t)base * sizeof(*system->unit_index));
    if (!system->units || !system->unit_index) {
        ccs_characters_free(system);
        return 0;
    }
    for (int r = 0; r < base; r++) system->unit_index[r] = -1;
    int unit = 0;
    for (int r = 1; r < base; r++) {
        if (ccs_gcd(r, base) != 1) continue;
        system->units[unit] = r;
        system->unit_index[r] = unit++;
    }
    if (unit != system->unit_count) {
        ccs_characters_free(system);
        return 0;
    }

    int remaining = base;
    for (int prime = 2; prime <= remaining / prime; prime++) {
        if (remaining % prime != 0) continue;
        int power = 0;
        int modulus = 1;
        while (remaining % prime == 0) {
            remaining /= prime;
            modulus *= prime;
            power++;
        }
        if (prime == 2) {
            if (!ccs_add_two_power_factors(system, modulus, power)) {
                ccs_characters_free(system);
                return 0;
            }
        } else {
            int generator = base == 10 && modulus == 5
                          ? 3 : ccs_primitive_root(modulus);
            if (!generator || !ccs_add_cyclic_factor(
                    system, modulus, ccs_phi(modulus), generator)) {
                ccs_characters_free(system);
                return 0;
            }
        }
    }
    if (remaining > 1) {
        int modulus = remaining;
        if (remaining == 2) {
            if (!ccs_add_two_power_factors(system, 2, 1)) {
                ccs_characters_free(system);
                return 0;
            }
        } else {
            int generator = base == 10 && modulus == 5
                          ? 3 : ccs_primitive_root(modulus);
            if (!generator || !ccs_add_cyclic_factor(
                    system, modulus, modulus - 1, generator)) {
                ccs_characters_free(system);
                return 0;
            }
        }
    }

    int character_count = 1;
    for (int i = 0; i < system->factor_count; i++)
        character_count *= system->factors[i].order;
    if (character_count != system->unit_count) {
        ccs_characters_free(system);
        return 0;
    }

    size_t matrix_size = (size_t)system->unit_count * system->unit_count;
    system->value = malloc(matrix_size * sizeof(*system->value));
    system->conjugate = malloc((size_t)system->unit_count *
                               sizeof(*system->conjugate));
    if (!system->value || !system->conjugate) {
        ccs_characters_free(system);
        return 0;
    }

    for (int character = 0; character < system->unit_count; character++) {
        int coordinates[CCS_MAX_FACTORS];
        int index = character;
        int conjugate = 0;
        int stride = 1;
        for (int f = 0; f < system->factor_count; f++) {
            int order = system->factors[f].order;
            coordinates[f] = index % order;
            index /= order;
            int opposite = coordinates[f] == 0 ? 0 : order - coordinates[f];
            conjugate += opposite * stride;
            stride *= order;
        }
        system->conjugate[character] = conjugate;
        for (int u = 0; u < system->unit_count; u++) {
            long double angle = 0.0L;
            int residue = system->units[u];
            for (int f = 0; f < system->factor_count; f++) {
                CCSFactor *factor = &system->factors[f];
                int local = residue % factor->modulus;
                int exponent = factor->exponent[local];
                if (exponent < 0) {
                    ccs_characters_free(system);
                    return 0;
                }
                angle += 2.0L * M_PI * coordinates[f] * exponent /
                         factor->order;
            }
            system->value[(size_t)character * system->unit_count + u] =
                cosl(angle) + I * sinl(angle);
        }
    }
    return 1;
}

static int ccs_collision_count(int p, int base, int multiplier)
{
    int matches = 0;
    for (int r = 1; r < p; r++) {
        int transformed = (int)((long long)multiplier * r % p);
        int left = (int)((long long)base * r / p);
        int right = (int)((long long)base * transformed / p);
        if (left == right) matches++;
    }
    return matches;
}

int collision_characters_prime_deviation(int p, int base, int lag,
                                         long long *numerator,
                                         long long *denominator,
                                         int *collision,
                                         int *multiplier)
{
    if (!numerator || !denominator || !collision || !multiplier ||
        !ccs_valid_base(base, 0) || !ccs_is_prime(p) || p <= base + 1 ||
        p > CCS_MAX_CUTOFF || lag < 1 || lag > 64)
        return 0;
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    long long mean_numerator =
        (long long)q * (base * (q - 1) + 2 * remainder);
    long long mean_denominator = base * (q - 1) + remainder;
    int g = ccs_mod_pow(base, lag, p);
    int count = ccs_collision_count(p, base, g);
    *numerator = (long long)count * mean_denominator - mean_numerator;
    *denominator = mean_denominator;
    *collision = count;
    *multiplier = g;
    return mean_denominator > 0;
}

static unsigned char *ccs_prime_sieve(int cutoff)
{
    unsigned char *composite = calloc((size_t)cutoff + 1, 1);
    if (!composite) return NULL;
    composite[0] = composite[1] = 1;
    for (int p = 2; p <= cutoff / p; p++) {
        if (composite[p]) continue;
        for (int multiple = p * p; multiple <= cutoff; multiple += p)
            composite[multiple] = 1;
    }
    return composite;
}

static void ccs_signal_free(CCSSignal *signal)
{
    free(signal->streams);
    free(signal->components);
    memset(signal, 0, sizeof(*signal));
}

static int ccs_signal_build(const CCSCharacters *system, int lag, int cutoff,
                            long double sigma, long double tau,
                            CCSSignal *signal)
{
    memset(signal, 0, sizeof(*signal));
    if (!ccs_valid_cutoff(system->base, cutoff, 0) || lag < 1 || lag > 64)
        return 0;
    int count = system->unit_count;
    signal->streams = calloc((size_t)count, sizeof(*signal->streams));
    signal->components = calloc((size_t)count, sizeof(*signal->components));
    unsigned char *composite = ccs_prime_sieve(cutoff);
    if (!signal->streams || !signal->components || !composite) {
        free(composite);
        ccs_signal_free(signal);
        return 0;
    }
    long double complex s = sigma + I * tau;

    for (int p = system->base + 2; p <= cutoff; p++) {
        if (composite[p]) continue;
        long long numerator = 0, denominator = 0;
        int collision = 0, multiplier = 0;
        if (!collision_characters_prime_deviation(
                p, system->base, lag, &numerator, &denominator,
                &collision, &multiplier)) {
            free(composite);
            ccs_signal_free(signal);
            return 0;
        }
        (void)collision;
        (void)multiplier;
        long double deviation = (long double)numerator / denominator;
        long double complex term = deviation * cexpl(-s * logl((long double)p));
        int stream = system->unit_index[p % system->base];
        if (stream < 0) {
            free(composite);
            ccs_signal_free(signal);
            return 0;
        }
        signal->streams[stream] += term;
        signal->total += term;
        signal->eligible_primes++;
    }

    /* Direct prime-sum route, separate from the residue-stream transform. */
    for (int p = system->base + 2; p <= cutoff; p++) {
        if (composite[p]) continue;
        long long numerator = 0, denominator = 0;
        int collision = 0, multiplier = 0;
        collision_characters_prime_deviation(
            p, system->base, lag, &numerator, &denominator,
            &collision, &multiplier);
        long double deviation = (long double)numerator / denominator;
        long double complex term = deviation * cexpl(-s * logl((long double)p));
        int stream = system->unit_index[p % system->base];
        for (int character = 0; character < count; character++) {
            long double complex chi =
                system->value[(size_t)character * count + stream];
            signal->components[character] += chi * term;
        }
    }
    free(composite);
    return 1;
}

static void ccs_forward(const CCSCharacters *system, const CCSSignal *signal,
                        long double complex *values)
{
    int count = system->unit_count;
    for (int character = 0; character < count; character++) {
        values[character] = 0.0L;
        for (int stream = 0; stream < count; stream++)
            values[character] +=
                system->value[(size_t)character * count + stream] *
                signal->streams[stream];
    }
}

static long double ccs_scaled_error(long double difference, long double scale)
{
    return difference / (1.0L + scale);
}

static int ccs_residuals(const CCSCharacters *system,
                         const CCSSignal *signal,
                         const CCSSignal *conjugate_signal,
                         CCSResiduals *residuals)
{
    int count = system->unit_count;
    long double complex *forward = calloc((size_t)count, sizeof(*forward));
    if (!forward) return 0;
    ccs_forward(system, signal, forward);
    memset(residuals, 0, sizeof(*residuals));

    for (int character = 0; character < count; character++) {
        long double scale = cabsl(signal->components[character]);
        long double error = ccs_scaled_error(
            cabsl(forward[character] - signal->components[character]), scale);
        if (error > residuals->forward_error) residuals->forward_error = error;
    }

    for (int stream = 0; stream < count; stream++) {
        long double complex reconstructed = 0.0L;
        for (int character = 0; character < count; character++)
            reconstructed += conjl(system->value[
                (size_t)character * count + stream]) *
                signal->components[character];
        reconstructed /= count;
        long double error = ccs_scaled_error(
            cabsl(reconstructed - signal->streams[stream]),
            cabsl(signal->streams[stream]));
        if (error > residuals->inverse_error) residuals->inverse_error = error;
    }

    long double complex stream_total = 0.0L;
    for (int stream = 0; stream < count; stream++)
        stream_total += signal->streams[stream];
    residuals->principal_error = ccs_scaled_error(
        cabsl(signal->components[0] - signal->total) +
        cabsl(stream_total - signal->total), cabsl(signal->total));

    long double component_energy = 0.0L;
    long double stream_energy = 0.0L;
    for (int character = 0; character < count; character++) {
        long double magnitude = cabsl(signal->components[character]);
        component_energy += magnitude * magnitude;
    }
    for (int stream = 0; stream < count; stream++) {
        long double magnitude = cabsl(signal->streams[stream]);
        stream_energy += magnitude * magnitude;
    }
    residuals->parseval_error = ccs_scaled_error(
        fabsl(component_energy - count * stream_energy), component_energy);

    for (int character = 0; character < count; character++) {
        int opposite = system->conjugate[character];
        long double complex expected = conjl(signal->components[character]);
        long double error = ccs_scaled_error(
            cabsl(conjugate_signal->components[opposite] - expected),
            cabsl(expected));
        if (error > residuals->conjugate_error)
            residuals->conjugate_error = error;
    }
    free(forward);
    return 1;
}

static int ccs_residuals_pass(const CCSResiduals *residuals)
{
    return residuals->forward_error < CCS_TOL &&
           residuals->inverse_error < CCS_TOL &&
           residuals->principal_error < CCS_TOL &&
           residuals->parseval_error < CCS_TOL &&
           residuals->conjugate_error < CCS_TOL;
}

static void ccs_print_complex(long double complex value)
{
    printf("%+.12Lf %+.12Lfi", creall(value), cimagl(value));
}

static void ccs_print_character_label(const CCSCharacters *system,
                                      int character)
{
    printf("chi_%d", character);
    if (system->factor_count == 0) return;
    printf(" [");
    int index = character;
    for (int f = 0; f < system->factor_count; f++) {
        int coordinate = index % system->factors[f].order;
        index /= system->factors[f].order;
        printf("%s%d", f == 0 ? "" : ",", coordinate);
    }
    printf("]");
}

int collision_characters_prime(int p, int base, int lag)
{
    if (!ccs_valid_base(base, 1)) return 1;
    if (!ccs_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (p <= base + 1) {
        fprintf(stderr, "the collision deviation requires p > base + 1\n");
        return 1;
    }
    if (p > CCS_MAX_CUTOFF) {
        fprintf(stderr, "p must not exceed %d\n", CCS_MAX_CUTOFF);
        return 1;
    }
    if (lag < 1 || lag > 64) {
        fprintf(stderr, "lag must be between 1 and 64\n");
        return 1;
    }
    long long numerator = 0, denominator = 0;
    int collision = 0, multiplier = 0;
    collision_characters_prime_deviation(
        p, base, lag, &numerator, &denominator, &collision, &multiplier);
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    long long mean_numerator =
        (long long)q * (base * (q - 1) + 2 * remainder);

    printf("Finite collision deviation at a power multiplier\n\n");
    printf("  p=%d, base=%d, lag=%d, p mod b=%d\n", p, base, lag, p % base);
    printf("  multiplier [b^lag]_p = %d%s\n", multiplier,
           multiplier == 1 ? " (identity is allowed)" : "");
    printf("  C_p,b([b^lag]_p) = %d\n", collision);
    printf("  p-1 = b*Q+R = %d*%d+%d\n", base, q, remainder);
    printf("  constructive mean = %lld/%lld\n",
           mean_numerator, denominator);
    printf("  Delta_p,b(lag) = %lld/%lld = %+.12Lf\n", numerator,
           denominator, (long double)numerator / denominator);
    printf("\nNo primitive-root hypothesis is used.\n");
    printf("Result  PASS\n");
    return 0;
}

int collision_characters_inspect(int cutoff, int base, int lag,
                                 long double sigma, long double tau)
{
    if (!ccs_valid_cutoff(base, cutoff, 1)) return 1;
    if (lag < 1 || lag > 64) {
        fprintf(stderr, "lag must be between 1 and 64\n");
        return 1;
    }
    CCSCharacters system = {0};
    CCSSignal signal = {0}, conjugate_signal = {0};
    CCSResiduals residuals;
    if (!ccs_characters_build(base, &system) ||
        !ccs_signal_build(&system, lag, cutoff, sigma, tau, &signal) ||
        !ccs_signal_build(&system, lag, cutoff, sigma, -tau,
                          &conjugate_signal) ||
        !ccs_residuals(&system, &signal, &conjugate_signal, &residuals)) {
        fprintf(stderr, "unable to build the finite character decomposition\n");
        ccs_signal_free(&signal);
        ccs_signal_free(&conjugate_signal);
        ccs_characters_free(&system);
        return 1;
    }
    int ok = ccs_residuals_pass(&residuals);

    printf("Finite residue streams and character coordinates\n\n");
    printf("base b=%d, lag ell=%d, cutoff x=%d, s=%+.6Lf%+.6Lfi\n",
           base, lag, cutoff, sigma, tau);
    printf("eligible primes b+1<p<=x: %d\n", signal.eligible_primes);
    printf("U_b has phi(b)=%d classes and %d characters\n\n",
           system.unit_count, system.unit_count);

    printf("Residue streams F_r,x(s,ell)\n");
    for (int stream = 0; stream < system.unit_count; stream++) {
        printf("  r=%-3d  ", system.units[stream]);
        ccs_print_complex(signal.streams[stream]);
        printf("\n");
    }
    printf("\nCharacter components\n");
    for (int character = 0; character < system.unit_count; character++) {
        printf("  ");
        ccs_print_character_label(&system, character);
        printf("  ");
        ccs_print_complex(signal.components[character]);
        if (character == 0) printf("  principal");
        if (system.conjugate[character] != character)
            printf("  conjugate chi_%d", system.conjugate[character]);
        printf("\n");
    }

    printf("\nFinite transform checks (scaled residuals)\n");
    printf("  forward stream-to-character transform   %.3Le  %s\n",
           residuals.forward_error,
           residuals.forward_error < CCS_TOL ? "PASS" : "FAIL");
    printf("  inverse character-to-stream transform   %.3Le  %s\n",
           residuals.inverse_error,
           residuals.inverse_error < CCS_TOL ? "PASS" : "FAIL");
    printf("  principal component equals total        %.3Le  %s\n",
           residuals.principal_error,
           residuals.principal_error < CCS_TOL ? "PASS" : "FAIL");
    printf("  Parseval identity                        %.3Le  %s\n",
           residuals.parseval_error,
           residuals.parseval_error < CCS_TOL ? "PASS" : "FAIL");
    printf("  conjugate-character pairing              %.3Le  %s\n",
           residuals.conjugate_error,
           residuals.conjugate_error < CCS_TOL ? "PASS" : "FAIL");
    printf("\nThis operation evaluates the exact finite-cutoff transform.\n");
    printf("Cutoff asymptotics remain a separate question.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");

    ccs_signal_free(&signal);
    ccs_signal_free(&conjugate_signal);
    ccs_characters_free(&system);
    return ok ? 0 : 1;
}

int collision_characters_base_ten_row(int cutoff, int *prime_count,
                                      long double *component_real,
                                      long double *component_imag)
{
    if (!prime_count || !component_real || !component_imag ||
        cutoff < 12 || cutoff > CCS_MAX_CUTOFF)
        return 0;
    CCSCharacters system = {0};
    CCSSignal signal = {0};
    if (!ccs_characters_build(10, &system) ||
        !ccs_signal_build(&system, 1, cutoff, 1.0L, 0.0L, &signal)) {
        ccs_signal_free(&signal);
        ccs_characters_free(&system);
        return 0;
    }
    *prime_count = signal.eligible_primes;
    for (int character = 0; character < 4; character++) {
        component_real[character] = creall(signal.components[character]);
        component_imag[character] = cimagl(signal.components[character]);
    }
    ccs_signal_free(&signal);
    ccs_characters_free(&system);
    return 1;
}

static int ccs_snapshot_row_pass(int row, int prime_count,
                                 const long double *real,
                                 const long double *imag)
{
    static const int expected_primes[] = {20, 163, 664, 1224};
    static const long double expected[][4] = {
        {-0.851414L, -0.012410L, -0.168966L, 0.300620L},
        {-1.149104L, -0.208657L, -0.217315L, 0.329630L},
        {-1.318994L, -0.288890L, -0.234378L, 0.354014L},
        {-1.392595L, -0.316180L, -0.241931L, 0.350235L}
    };
    return prime_count == expected_primes[row] &&
           fabsl(real[0] - expected[row][0]) < 5.1e-7L &&
           fabsl(real[1] - expected[row][1]) < 5.1e-7L &&
           fabsl(imag[1] - expected[row][2]) < 5.1e-7L &&
           fabsl(real[2] - expected[row][3]) < 5.1e-7L &&
           fabsl(imag[0]) < CCS_TOL && fabsl(imag[2]) < CCS_TOL;
}

int collision_characters_snapshot(void)
{
    int cutoffs[] = {100, 1000, 5000, 10000};
    int passed = 0;
    printf("Finite residue-stream snapshot\n");
    printf("Base-ten finite snapshot, lag ell=1, exponent s=1\n\n");
    printf("  x       primes     chi_0         Re chi_1      Im chi_1      chi_2       check\n");
    for (int row = 0; row < 4; row++) {
        int prime_count = 0;
        long double real[4] = {0.0L};
        long double imag[4] = {0.0L};
        int computed = collision_characters_base_ten_row(
            cutoffs[row], &prime_count, real, imag);
        int ok = computed && ccs_snapshot_row_pass(row, prime_count, real, imag);
        printf("  %-7d %-10d %+.6Lf      %+.6Lf      %+.6Lf      %+.6Lf      %s\n",
               cutoffs[row], prime_count, real[0], real[1], imag[1], real[2],
               ok ? "PASS" : "FAIL");
        if (ok) passed++;
    }
    printf("\nchi_3 is the complex conjugate of chi_1.\n");
    printf("Each row is an exact finite-cutoff packet followed by a numerical transform.\n");
    printf("%d/4 reference rows reproduced.\n", passed);
    return passed == 4 ? 0 : 1;
}

int collision_characters_examples(void)
{
    long long numerator = 0, denominator = 0;
    int collision = 0, multiplier = 0;
    int thirteen = collision_characters_prime_deviation(
        13, 10, 1, &numerator, &denominator, &collision, &multiplier) &&
        multiplier == 10 && collision == 0 && numerator == -4 &&
        denominator == 2;
    int identity = collision_characters_prime_deviation(
        7, 2, 3, &numerator, &denominator, &collision, &multiplier) &&
        multiplier == 1 && collision == 6 && numerator == 12 &&
        denominator == 4;
    int snapshot = 1;
    int primes = 0;
    long double real[4], imag[4];
    if (!collision_characters_base_ten_row(100, &primes, real, imag) ||
        !ccs_snapshot_row_pass(0, primes, real, imag))
        snapshot = 0;

    printf("Finite collision-deviation and character-coordinate examples\n\n");
    printf("decimal p=13 has multiplier 10, C=0, and Delta=-4/2=-2  %s\n",
           thirteen ? "PASS" : "FAIL");
    printf("base-two p=7 lag three permits identity multiplier and Delta=12/4=3  %s\n",
           identity ? "PASS" : "FAIL");
    printf("base-ten x=100 finite character row is reproduced  %s\n",
           snapshot ? "PASS" : "FAIL");
    printf("Result  %s\n", thirteen && identity && snapshot ? "PASS" : "FAIL");
    return thirteen && identity && snapshot ? 0 : 1;
}

static void ccs_check_collision_arithmetic(int *models, int *bins,
                                           int *gate, int *mean)
{
    *models = 0;
    *bins = 1;
    *gate = 1;
    *mean = 1;
    for (int base = 2; base <= 16; base++) {
        for (int p = base + 2; p <= 97; p++) {
            if (!ccs_is_prime(p)) continue;
            (*models)++;
            int q = (p - 1) / base;
            int remainder = (p - 1) % base;
            int bin_sizes[16] = {0};
            for (int r = 1; r < p; r++) {
                int digit = (int)((long long)base * r / p);
                int transformed = (int)((long long)base * r % p);
                if (digit < 0 || digit >= base || transformed <= 0 ||
                    (long long)base * r != (long long)p * digit + transformed)
                    *bins = 0;
                else
                    bin_sizes[digit]++;
            }
            int long_bins = 0;
            long long square_mass = 0;
            for (int d = 0; d < base; d++) {
                if (bin_sizes[d] == q + 1) long_bins++;
                if (bin_sizes[d] != q && bin_sizes[d] != q + 1) *bins = 0;
                square_mass += (long long)bin_sizes[d] * bin_sizes[d];
            }
            if (long_bins != remainder ||
                square_mass != (long long)base * q * q +
                               remainder * (2 * q + 1))
                *bins = 0;
            for (int r = 1; r < p; r++) {
                int digit_r = (int)((long long)base * r / p);
                int transformed_r = (int)((long long)base * r % p);
                for (int s = 1; s < p; s++) {
                    int digit_s = (int)((long long)base * s / p);
                    int transformed_s = (int)((long long)base * s % p);
                    if ((digit_r == digit_s) !=
                        (transformed_r % base == transformed_s % base))
                        *bins = 0;
                }
            }
            int constructive_count = 0;
            long long constructive_mass = 0;
            for (int g = 1; g < p; g++) {
                int collision = ccs_collision_count(p, base, g);
                int congruence = 0;
                for (int x = 1; x < p; x++) {
                    int y = (int)((long long)g * x % p);
                    if (x % base == y % base) congruence++;
                }
                if (collision != congruence) *gate = 0;
                if (g != 1) {
                    int one_minus = (1 - g) % p;
                    if (one_minus < 0) one_minus += p;
                    int inverse = ccs_mod_pow(one_minus, p - 2, p);
                    int coordinate = (int)((long long)base * inverse % p);
                    if (coordinate <= 0 || coordinate == base ||
                        ((collision == 0) != (coordinate < base)))
                        *gate = 0;
                }
                if (g != 1 && collision > 0) {
                    constructive_count++;
                    constructive_mass += collision;
                }
            }
            long long expected_mass =
                (long long)q * (base * (q - 1) + 2 * remainder);
            int expected_count = base * (q - 1) + remainder;
            if (constructive_count != expected_count ||
                constructive_mass != expected_mass)
                *mean = 0;
            for (int lag = 1; lag <= 3; lag++) {
                long long numerator = 0, denominator = 0;
                int collision = 0, multiplier = 0;
                if (!collision_characters_prime_deviation(
                        p, base, lag, &numerator, &denominator,
                        &collision, &multiplier) ||
                    multiplier != ccs_mod_pow(base, lag, p) ||
                    numerator != (long long)collision * expected_count -
                                 expected_mass ||
                    denominator != expected_count)
                    *mean = 0;
            }
        }
    }
}

static int ccs_check_character_systems(int *orthogonality)
{
    int structure = 1;
    *orthogonality = 1;
    for (int base = 2; base <= 24; base++) {
        CCSCharacters system = {0};
        if (!ccs_characters_build(base, &system)) return 0;
        if (system.unit_count != ccs_phi(base)) structure = 0;
        for (int character = 0; character < system.unit_count; character++) {
            if (system.conjugate[system.conjugate[character]] != character)
                structure = 0;
            for (int unit = 0; unit < system.unit_count; unit++)
                if (fabsl(cabsl(system.value[
                        (size_t)character * system.unit_count + unit]) - 1.0L) >
                    CCS_TOL)
                    structure = 0;
        }
        for (int left = 0; left < system.unit_count; left++) {
            for (int right = 0; right < system.unit_count; right++) {
                long double complex sum = 0.0L;
                for (int character = 0; character < system.unit_count;
                     character++)
                    sum += system.value[(size_t)character * system.unit_count + left] *
                           conjl(system.value[(size_t)character *
                                              system.unit_count + right]);
                long double expected = left == right ? system.unit_count : 0.0L;
                if (cabsl(sum - expected) > CCS_TOL * system.unit_count)
                    *orthogonality = 0;
            }
        }
        ccs_characters_free(&system);
    }
    return structure;
}

int collision_characters_verify(void)
{
    int collision_models = 0;
    int bins = 0, gate = 0, mean = 0;
    ccs_check_collision_arithmetic(&collision_models, &bins, &gate, &mean);
    int identity = 0;
    long long numerator = 0, denominator = 0;
    int collision = 0, multiplier = 0;
    identity = collision_characters_prime_deviation(
        7, 2, 3, &numerator, &denominator, &collision, &multiplier) &&
        multiplier == 1 && collision == 6 && numerator == 12 && denominator == 4;

    int orthogonality = 0;
    int systems = ccs_check_character_systems(&orthogonality);
    int forward = 1, inverse = 1, principal = 1, parseval = 1, pairing = 1;
    int models = 0;
    for (int base = 2; base <= 12; base++) {
        CCSCharacters system = {0};
        if (!ccs_characters_build(base, &system)) {
            forward = inverse = principal = parseval = pairing = 0;
            continue;
        }
        for (int lag = 1; lag <= 2; lag++) {
            long double parameters[][2] = {{1.0L, 0.0L}, {0.75L, 0.4L}};
            for (int parameter = 0; parameter < 2; parameter++) {
                CCSSignal signal = {0}, conjugate_signal = {0};
                CCSResiduals residuals;
                if (!ccs_signal_build(&system, lag, 211,
                                      parameters[parameter][0],
                                      parameters[parameter][1], &signal) ||
                    !ccs_signal_build(&system, lag, 211,
                                      parameters[parameter][0],
                                      -parameters[parameter][1],
                                      &conjugate_signal) ||
                    !ccs_residuals(&system, &signal, &conjugate_signal,
                                   &residuals)) {
                    forward = inverse = principal = parseval = pairing = 0;
                } else {
                    forward = forward && residuals.forward_error < CCS_TOL;
                    inverse = inverse && residuals.inverse_error < CCS_TOL;
                    principal = principal && residuals.principal_error < CCS_TOL;
                    parseval = parseval && residuals.parseval_error < CCS_TOL;
                    pairing = pairing && residuals.conjugate_error < CCS_TOL;
                    models++;
                }
                ccs_signal_free(&signal);
                ccs_signal_free(&conjugate_signal);
            }
        }
        ccs_characters_free(&system);
    }

    int snapshot = 1;
    int cutoffs[] = {100, 1000, 5000, 10000};
    for (int row = 0; row < 4; row++) {
        int primes = 0;
        long double real[4], imag[4];
        if (!collision_characters_base_ten_row(
                cutoffs[row], &primes, real, imag) ||
            !ccs_snapshot_row_pass(row, primes, real, imag))
            snapshot = 0;
    }
    int examples = collision_characters_examples() == 0;

    int checks[] = {bins, gate, mean, identity, systems, orthogonality,
                    forward, inverse, principal, parseval, pairing, snapshot,
                    examples};
    const char *labels[] = {
        "exact floor bins, endpoint distribution, and conjugation",
        "collision congruence and both sides of the zero gate",
        "exact constructive mean and prime deviation",
        "identity multiplier remains in the deviation domain",
        "phi(b) unit classes and complete character systems",
        "finite character orthogonality",
        "forward transform equals direct prime sums",
        "inverse transform reconstructs every residue stream",
        "principal component equals the total fluctuation",
        "Parseval identity",
        "conjugate pairing for complex s",
        "all four base-ten reference rows",
        "named exact examples"
    };
    int passed = 0;
    printf("\nFinite C verification of residue-stream character coordinates\n");
    printf("Exact collision arithmetic; long-double character transforms.\n");
    printf("Collision sweep: %d (base, prime) models; character systems: bases 2..24.\n",
           collision_models);
    printf("Transform sweep: %d finite (base, lag, s) models.\n\n", models);
    for (int i = 0; i < 13; i++) {
        printf("  %-64s %s\n", labels[i], checks[i] ? "PASS" : "FAIL");
        if (checks[i]) passed++;
    }
    printf("\n%d/13 verification groups passed.\n", passed);
    printf("The verifier closes finite-cutoff equations; cutoff asymptotics remain open.\n");
    return passed == 13;
}

void collision_characters_help(void)
{
    printf(
        "Finite residue streams and character coordinates\n\n"
        "This object constructs collision deviations, residue streams, and\n"
        "their complete finite character coordinates. It checks reconstruction,\n"
        "Parseval, conjugate pairing, and a base-ten cutoff snapshot.\n\n"
        "Usage:\n"
        "  nfield collision-characters prime <p> [--base <b>] [--lag <ell>]\n"
        "  nfield collision-characters inspect <x> [--base <b>] [--lag <ell>]\n"
        "                                      [--sigma <real>] [--tau <imag>]\n"
        "  nfield collision-characters snapshot\n"
        "  nfield collision-characters examples\n"
        "  nfield collision-characters verify\n"
        "  nfield verify collision-characters\n"
        "  nfield help collision-characters\n\n"
        "prime displays the exact rational collision deviation at one prime.\n"
        "inspect forms every residue stream and every character component at a\n"
        "finite cutoff, then checks the forward transform, inverse reconstruction,\n"
        "principal component, Parseval identity, and conjugate pairing. The\n"
        "complex exponent is s=sigma+i*tau; defaults are sigma=1 and tau=0.\n"
        "snapshot reproduces four base-ten cutoff rows at lag one and s=1.\n\n"
        "The domain uses p>b+1 because the constructive mean is undefined at\n"
        "p=b+1. Identity multipliers b^ell=1 mod p remain valid. No primitive-root\n"
        "hypothesis is used. Collision arithmetic is exact; finite character\n"
        "transforms use long-double complex arithmetic with reported residuals.\n\n"
        "The object evaluates finite residue channels and leaves their cutoff\n"
        "asymptotics open. The legacy character_components command studies a\n"
        "different b^2 table.\n"
    );
}
