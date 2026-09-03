/* Finite carry-boundary and Bernoulli factorization checks. */

#include <complex.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"

#define BBF_MAX_MODULUS 20000
#define BBF_MAX_ABS_WEIGHT 1000000
#define BBF_TOLERANCE 5.0e-10L

typedef struct {
    int prime;
    int depth;
    int modulus;
    int phi;
    int generator;
    int *discrete_log;
    unsigned char *is_unit;
} BbfContext;

typedef struct {
    long double complex direct_transform;
    long double complex bernoulli;
    long double complex boundary_flux;
    long double complex visible_flux;
    long double factorization_error;
    long double boundary_error;
    int visible_endpoints;
    long long visible_norm;
    int odd;
} BbfComparison;

static int bbf_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0) return 0;
    return 1;
}

static int bbf_gcd(int left, int right)
{
    while (right != 0) {
        int remainder = left % right;
        left = right;
        right = remainder;
    }
    return left < 0 ? -left : left;
}

static int bbf_power(int base, int exponent, int *value)
{
    if (!value || base < 2 || exponent < 1) return 0;
    int result = 1;
    for (int index = 0; index < exponent; index++) {
        if (result > BBF_MAX_MODULUS / base) return 0;
        result *= base;
    }
    *value = result;
    return 1;
}

static int bbf_modular_power(int base, int exponent, int modulus)
{
    long long result = 1;
    long long power = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int bbf_distinct_prime_factors(int value, int *factors, int capacity)
{
    int count = 0;
    int remaining = value;
    for (int divisor = 2; divisor <= remaining / divisor; divisor++) {
        if (remaining % divisor != 0) continue;
        if (count >= capacity) return -1;
        factors[count++] = divisor;
        while (remaining % divisor == 0) remaining /= divisor;
    }
    if (remaining > 1) {
        if (count >= capacity) return -1;
        factors[count++] = remaining;
    }
    return count;
}

static int bbf_primitive_root(int modulus, int phi)
{
    int factors[32];
    int count = bbf_distinct_prime_factors(phi, factors, 32);
    if (count < 0) return 0;
    for (int candidate = 2; candidate < modulus; candidate++) {
        if (bbf_gcd(candidate, modulus) != 1) continue;
        int primitive = 1;
        for (int index = 0; index < count; index++) {
            if (bbf_modular_power(
                    candidate, phi / factors[index], modulus) == 1) {
                primitive = 0;
                break;
            }
        }
        if (primitive) return candidate;
    }
    return 0;
}

static void bbf_context_free(BbfContext *context)
{
    if (!context) return;
    free(context->discrete_log);
    free(context->is_unit);
    *context = (BbfContext){0};
}

static int bbf_context_build(int prime, int depth, BbfContext *context)
{
    int modulus = 0;
    int lower = 1;
    if (!context || !bbf_is_prime(prime) || prime == 2 || depth < 1 ||
        !bbf_power(prime, depth, &modulus))
        return 0;
    for (int index = 1; index < depth; index++) lower *= prime;
    int phi = lower * (prime - 1);
    int generator = bbf_primitive_root(modulus, phi);
    if (generator == 0) return 0;
    *context = (BbfContext){
        .prime = prime,
        .depth = depth,
        .modulus = modulus,
        .phi = phi,
        .generator = generator
    };
    context->discrete_log = malloc(
        (size_t)modulus * sizeof(*context->discrete_log));
    context->is_unit = calloc(
        (size_t)modulus, sizeof(*context->is_unit));
    if (!context->discrete_log || !context->is_unit) {
        bbf_context_free(context);
        return 0;
    }
    for (int residue = 0; residue < modulus; residue++)
        context->discrete_log[residue] = -1;
    int residue = 1;
    for (int exponent = 0; exponent < phi; exponent++) {
        context->discrete_log[residue] = exponent;
        context->is_unit[residue] = 1;
        residue = (int)((long long)residue * generator % modulus);
    }
    if (residue != 1) {
        bbf_context_free(context);
        return 0;
    }
    return 1;
}

static int bbf_character_is_primitive(const BbfContext *context,
                                      int exponent)
{
    if (!context || exponent <= 0 || exponent >= context->phi) return 0;
    if (context->depth == 1) return 1;
    return exponent % context->prime != 0;
}

static long double complex bbf_character(
        const BbfContext *context, int exponent, int residue)
{
    residue %= context->modulus;
    if (residue < 0) residue += context->modulus;
    if (!context->is_unit[residue]) return 0.0L + 0.0L * I;
    long double angle = 2.0L * acosl(-1.0L) *
        (long double)((long long)exponent *
                      context->discrete_log[residue] % context->phi) /
        (long double)context->phi;
    return cosl(angle) + I * sinl(angle);
}

static long double bbf_sawtooth(long long value, int modulus)
{
    int residue = (int)(value % modulus);
    if (residue < 0) residue += modulus;
    if (residue == 0) return 0.0L;
    return (long double)residue / (long double)modulus - 0.5L;
}

static int bbf_compare(const BbfContext *context, int exponent,
                       const int *weights, int weight_count,
                       BbfComparison *comparison)
{
    if (!context || !weights || !comparison ||
        weight_count != context->modulus ||
        !bbf_character_is_primitive(context, exponent))
        return 0;
    *comparison = (BbfComparison){0};
    comparison->odd = exponent % 2;
    for (int cell = 0; cell < context->modulus; cell++)
        if (weights[cell] < -BBF_MAX_ABS_WEIGHT ||
            weights[cell] > BBF_MAX_ABS_WEIGHT)
            return 0;

    for (int unit = 1; unit < context->modulus; unit++) {
        if (!context->is_unit[unit]) continue;
        long double observable = 0.0L;
        for (int cell = 0; cell < context->modulus; cell++) {
            observable -= (long double)weights[cell] *
                (bbf_sawtooth((long long)(cell + 1) * unit,
                               context->modulus) -
                 bbf_sawtooth((long long)cell * unit,
                               context->modulus));
        }
        long double complex character = bbf_character(
            context, exponent, unit);
        comparison->direct_transform += observable * conjl(character);
        comparison->bernoulli +=
            ((long double)unit / (long double)context->modulus) *
            conjl(character);
    }

    for (int cell = 0; cell < context->modulus; cell++) {
        comparison->boundary_flux += (long double)weights[cell] *
            (bbf_character(context, exponent, cell + 1) -
             bbf_character(context, exponent, cell));
    }
    for (int residue = 0; residue < context->modulus; residue++) {
        int previous = residue == 0 ? context->modulus - 1 : residue - 1;
        long long boundary = (long long)weights[previous] - weights[residue];
        if (context->is_unit[residue] && boundary != 0) {
            comparison->visible_endpoints++;
            comparison->visible_norm += boundary * boundary;
            comparison->visible_flux += (long double)boundary *
                bbf_character(context, exponent, residue);
        }
    }
    long double complex factorized =
        -comparison->bernoulli * comparison->boundary_flux;
    comparison->factorization_error = cabsl(
        comparison->direct_transform - factorized);
    comparison->boundary_error = cabsl(
        comparison->boundary_flux - comparison->visible_flux);
    long double scale = 1.0L + cabsl(comparison->direct_transform) +
                        cabsl(factorized);
    return comparison->factorization_error <= BBF_TOLERANCE * scale &&
           comparison->boundary_error <= BBF_TOLERANCE * scale;
}

int boundary_bernoulli_factorization_compare(
        int prime, int depth, int character_exponent,
        const int *weights, int weight_count,
        long double *factorization_error, long double *boundary_error,
        int *visible_endpoints)
{
    if (!factorization_error || !boundary_error || !visible_endpoints)
        return 0;
    BbfContext context = {0};
    BbfComparison comparison;
    if (!bbf_context_build(prime, depth, &context)) return 0;
    int ok = bbf_compare(
        &context, character_exponent, weights, weight_count, &comparison);
    if (ok) {
        *factorization_error = comparison.factorization_error;
        *boundary_error = comparison.boundary_error;
        *visible_endpoints = comparison.visible_endpoints;
    }
    bbf_context_free(&context);
    return ok;
}

static int bbf_weights_valid(const int *weights, int weight_count)
{
    if (!weights || weight_count < 1) return 0;
    for (int cell = 0; cell < weight_count; cell++)
        if (weights[cell] < -BBF_MAX_ABS_WEIGHT ||
            weights[cell] > BBF_MAX_ABS_WEIGHT)
            return 0;
    return 1;
}

static long double bbf_observable_at(
        const BbfContext *context, const int *weights, int multiplier)
{
    long double observable = 0.0L;
    for (int cell = 0; cell < context->modulus; cell++)
        observable -= (long double)weights[cell] *
            (bbf_sawtooth((long long)(cell + 1) * multiplier,
                           context->modulus) -
             bbf_sawtooth((long long)cell * multiplier,
                           context->modulus));
    return observable;
}

static long double complex bbf_conductor_depth_weight(
        const BbfContext *ambient, const BbfContext *source,
        int exponent, int residue)
{
    residue %= ambient->modulus;
    if (residue < 0) residue += ambient->modulus;
    if (residue == 0) return 0.0L + 0.0L * I;

    int valuation = 0;
    int unit = residue;
    while (unit % ambient->prime == 0) {
        unit /= ambient->prime;
        valuation++;
    }
    if (valuation > ambient->depth - source->depth)
        return 0.0L + 0.0L * I;

    long double scale = 1.0L;
    for (int index = 0; index < valuation; index++)
        scale *= ambient->prime;
    return scale * bbf_character(source, exponent, unit);
}

static int bbf_induced_source_compare(
        const BbfContext *ambient, const BbfContext *source,
        int exponent, const int *weights, const long double *observable,
        const long long *boundary, long double complex *direct_out,
        long double *factorization_error,
        long double *boundary_pairing_error)
{
    if (!ambient || !source || !weights || !observable || !boundary ||
        !direct_out || !factorization_error || !boundary_pairing_error ||
        source->prime != ambient->prime || source->depth > ambient->depth ||
        !bbf_character_is_primitive(source, exponent))
        return 0;

    long double complex direct = 0.0L + 0.0L * I;
    long double complex bernoulli = 0.0L + 0.0L * I;
    long double complex difference_pairing = 0.0L + 0.0L * I;
    long double complex boundary_pairing = 0.0L + 0.0L * I;

    for (int unit = 1; unit < ambient->modulus; unit++) {
        if (!ambient->is_unit[unit]) continue;
        direct += observable[unit] *
            conjl(bbf_character(source, exponent, unit));
    }
    for (int unit = 1; unit < source->modulus; unit++) {
        if (!source->is_unit[unit]) continue;
        bernoulli += ((long double)unit / (long double)source->modulus) *
            conjl(bbf_character(source, exponent, unit));
    }
    for (int cell = 0; cell < ambient->modulus; cell++) {
        long double complex next = bbf_conductor_depth_weight(
            ambient, source, exponent, cell + 1);
        long double complex current = bbf_conductor_depth_weight(
            ambient, source, exponent, cell);
        difference_pairing += (long double)weights[cell] * (next - current);
        boundary_pairing += (long double)boundary[cell] * current;
    }

    long double complex factorized = -bernoulli * difference_pairing;
    *direct_out = direct;
    *factorization_error = cabsl(direct - factorized);
    *boundary_pairing_error = cabsl(
        difference_pairing - boundary_pairing);
    return 1;
}

int boundary_bernoulli_conductor_spectrum(
        int prime, int depth, const int *weights, int weight_count,
        CarryBoundarySpectrumSummary *summary)
{
    BbfContext ambient = {0};
    long double *observable = NULL;
    long long *boundary = NULL;
    long double complex *flux = NULL;
    int ok = 0;

    if (!summary || depth >= NFIELD_CARRY_BOUNDARY_MAX_DEPTH ||
        !bbf_context_build(prime, depth, &ambient) ||
        weight_count != ambient.modulus ||
        !bbf_weights_valid(weights, weight_count))
        goto cleanup;

    *summary = (CarryBoundarySpectrumSummary){
        .prime = prime,
        .depth = depth,
        .modulus = ambient.modulus
    };
    observable = calloc((size_t)ambient.modulus, sizeof(*observable));
    boundary = calloc((size_t)ambient.modulus, sizeof(*boundary));
    flux = calloc((size_t)ambient.phi, sizeof(*flux));
    if (!observable || !boundary || !flux) goto cleanup;

    for (int residue = 0; residue < ambient.modulus; residue++) {
        int previous = residue == 0 ? ambient.modulus - 1 : residue - 1;
        boundary[residue] = (long long)weights[previous] - weights[residue];
    }
    for (int unit = 1; unit < ambient.modulus; unit++) {
        if (!ambient.is_unit[unit]) continue;
        observable[unit] = bbf_observable_at(&ambient, weights, unit);
        summary->direct_energy += observable[unit] * observable[unit];
    }

    for (int exponent = 0; exponent < ambient.phi; exponent++)
        for (int unit = 1; unit < ambient.modulus; unit++) {
            if (!ambient.is_unit[unit]) continue;
            flux[exponent] += (long double)boundary[unit] *
                bbf_character(&ambient, exponent, unit);
        }
    for (int unit = 1; unit < ambient.modulus; unit++) {
        if (!ambient.is_unit[unit]) continue;
        long double complex reconstructed = 0.0L + 0.0L * I;
        for (int exponent = 0; exponent < ambient.phi; exponent++)
            reconstructed += flux[exponent] *
                conjl(bbf_character(&ambient, exponent, unit));
        reconstructed /= ambient.phi;
        long double error = cabsl(reconstructed - (long double)boundary[unit]);
        if (error > summary->unit_reconstruction_error)
            summary->unit_reconstruction_error = error;
    }

    for (int conductor_depth = 1;
         conductor_depth <= ambient.depth; conductor_depth++) {
        BbfContext source = {0};
        if (!bbf_context_build(prime, conductor_depth, &source)) goto cleanup;
        for (int exponent = 1; exponent < source.phi; exponent++) {
            if (!bbf_character_is_primitive(&source, exponent) ||
                exponent % 2 == 0)
                continue;
            long double complex direct = 0.0L + 0.0L * I;
            long double factorization_error = 0.0L;
            long double boundary_pairing_error = 0.0L;
            if (!bbf_induced_source_compare(
                    &ambient, &source, exponent, weights, observable, boundary,
                    &direct, &factorization_error,
                    &boundary_pairing_error)) {
                bbf_context_free(&source);
                goto cleanup;
            }
            summary->odd_channels++;
            summary->conductor_channels[conductor_depth - 1]++;
            summary->conductor_energy[conductor_depth - 1] +=
                cabsl(direct) * cabsl(direct) / ambient.phi;
            if (factorization_error >
                    summary->maximum_factorization_error)
                summary->maximum_factorization_error = factorization_error;
            if (boundary_pairing_error >
                    summary->maximum_boundary_pairing_error)
                summary->maximum_boundary_pairing_error =
                    boundary_pairing_error;
        }
        bbf_context_free(&source);
    }
    for (int index = 0; index < ambient.depth; index++)
        summary->spectral_energy += summary->conductor_energy[index];
    summary->energy_error = fabsl(
        summary->direct_energy - summary->spectral_energy);

    {
        long double scale = 1.0L + summary->direct_energy +
                            summary->spectral_energy;
        ok = summary->odd_channels == ambient.phi / 2 &&
             summary->maximum_factorization_error <=
                 BBF_TOLERANCE * scale &&
             summary->maximum_boundary_pairing_error <=
                 BBF_TOLERANCE * scale &&
             summary->unit_reconstruction_error <=
                 BBF_TOLERANCE * scale &&
             summary->energy_error <= BBF_TOLERANCE * scale;
    }

cleanup:
    free(observable);
    free(boundary);
    free(flux);
    bbf_context_free(&ambient);
    return ok;
}

static long double bbf_dedekind_sum(int multiplier, int modulus)
{
    if (modulus <= 1) return 0.0L;
    long double result = 0.0L;
    for (int residue = 0; residue < modulus; residue++)
        result += bbf_sawtooth(residue, modulus) *
            bbf_sawtooth((long long)multiplier * residue, modulus);
    return result;
}

int boundary_sawtooth_correlation(
        int prime, int depth, int first, int second,
        long double *direct, long double *dedekind, long double *error)
{
    BbfContext context = {0};
    if (!direct || !dedekind || !error ||
        !bbf_context_build(prime, depth, &context))
        return 0;
    first %= context.modulus;
    second %= context.modulus;
    if (first < 0) first += context.modulus;
    if (second < 0) second += context.modulus;
    if (!context.is_unit[first] || !context.is_unit[second]) {
        bbf_context_free(&context);
        return 0;
    }

    *direct = 0.0L;
    for (int unit = 1; unit < context.modulus; unit++) {
        if (!context.is_unit[unit]) continue;
        *direct += bbf_sawtooth((long long)first * unit,
                                context.modulus) *
                   bbf_sawtooth((long long)second * unit,
                                context.modulus);
    }
    int inverse = bbf_modular_power(
        first, context.phi - 1, context.modulus);
    int ratio = (int)((long long)second * inverse % context.modulus);
    int lower = context.modulus / prime;
    *dedekind = bbf_dedekind_sum(ratio, context.modulus) -
                bbf_dedekind_sum(ratio, lower);
    *error = fabsl(*direct - *dedekind);
    long double scale = 1.0L + fabsl(*direct) + fabsl(*dedekind);
    bbf_context_free(&context);
    return *error <= BBF_TOLERANCE * scale;
}

static int bbf_parse_support(const char *text, int modulus, int *weights,
                             int *support_size)
{
    if (!text || !*text || !weights || !support_size) return 0;
    const char *cursor = text;
    int count = 0;
    while (*cursor != '\0') {
        char *end = NULL;
        long cell = strtol(cursor, &end, 10);
        if (end == cursor || cell < 0 || cell >= modulus ||
            weights[cell] != 0)
            return 0;
        weights[cell] = 1;
        count++;
        if (*end == '\0') break;
        if (*end != ',') return 0;
        cursor = end + 1;
        if (*cursor == '\0') return 0;
    }
    *support_size = count;
    return count > 0;
}

static void bbf_print_complex(const char *label, long double complex value)
{
    printf("  %-28s %+.12Lf %+.12Lfi\n",
           label, creall(value), cimagl(value));
}

static int bbf_print_comparison(const BbfContext *context, int exponent,
                                const int *weights, int support_size,
                                const char *description)
{
    BbfComparison comparison;
    int ok = bbf_compare(
        context, exponent, weights, context->modulus, &comparison);
    if (!bbf_character_is_primitive(context, exponent)) {
        fprintf(stderr,
                "character exponent must select a primitive character in [1,phi)\n");
        return 1;
    }
    printf("Boundary-Bernoulli factorization\n\n");
    printf("  p=%d depth=%d modulus=%d phi=%d generator=%d\n",
           context->prime, context->depth, context->modulus,
           context->phi, context->generator);
    printf("  support=%s; marked cells=%d\n", description, support_size);
    printf("  character exponent=%d; parity=%s\n",
           exponent, comparison.odd ? "odd" : "even");
    printf("  visible boundary endpoints=%d; squared norm=%lld\n",
           comparison.visible_endpoints, comparison.visible_norm);
    bbf_print_complex("direct transform", comparison.direct_transform);
    bbf_print_complex("Bernoulli value", comparison.bernoulli);
    bbf_print_complex("boundary flux", comparison.boundary_flux);
    bbf_print_complex("-Bernoulli * flux",
                      -comparison.bernoulli * comparison.boundary_flux);
    printf("  direct/factorized error %.3Le  %s\n",
           comparison.factorization_error, ok ? "PASS" : "FAIL");
    printf("  support flux/visible-boundary error %.3Le  %s\n",
           comparison.boundary_error, ok ? "PASS" : "FAIL");
    if (!comparison.odd)
        printf("  even-character transform vanishes  %s\n",
               cabsl(comparison.direct_transform) <= BBF_TOLERANCE
                   ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int boundary_bernoulli_factorization_inspect(
        int prime, int depth, int character_exponent, const char *support)
{
    BbfContext context = {0};
    if (!bbf_context_build(prime, depth, &context)) {
        fprintf(stderr,
                "require an odd prime p, depth>=1, and p^depth<=20000\n");
        return 1;
    }
    int *weights = calloc((size_t)context.modulus, sizeof(*weights));
    if (!weights) {
        bbf_context_free(&context);
        return 1;
    }
    int support_size = 0;
    if (!bbf_parse_support(
            support, context.modulus, weights, &support_size)) {
        fprintf(stderr,
                "support must be a comma-separated list of distinct cells in [0,p^depth)\n");
        free(weights);
        bbf_context_free(&context);
        return 1;
    }
    int status = bbf_print_comparison(
        &context, character_exponent, weights, support_size, support);
    free(weights);
    bbf_context_free(&context);
    return status;
}

int boundary_bernoulli_factorization_spectrum(
        int prime, int depth, const char *support)
{
    BbfContext context = {0};
    if (!bbf_context_build(prime, depth, &context)) {
        fprintf(stderr,
                "require an odd prime p, depth>=1, and p^depth<=20000\n");
        return 1;
    }
    int *weights = calloc((size_t)context.modulus, sizeof(*weights));
    if (!weights) {
        bbf_context_free(&context);
        return 1;
    }
    int support_size = 0;
    if (!bbf_parse_support(
            support, context.modulus, weights, &support_size)) {
        fprintf(stderr,
                "support must be a comma-separated list of distinct cells in [0,p^depth)\n");
        free(weights);
        bbf_context_free(&context);
        return 1;
    }

    CarryBoundarySpectrumSummary summary = {0};
    int ok = boundary_bernoulli_conductor_spectrum(
        prime, depth, weights, context.modulus, &summary);
    printf("Conductor-depth carry-boundary spectrum\n\n");
    printf("  p=%d depth=%d modulus=%d; support=%s; marked cells=%d\n",
           prime, depth, context.modulus, support, support_size);
    printf("  odd channels=%d; expected=%d  %s\n",
           summary.odd_channels, context.phi / 2,
           summary.odd_channels == context.phi / 2 ? "PASS" : "FAIL");
    for (int index = 0; index < depth; index++)
        printf("  conductor p^%d channels=%d energy=%.15Lg\n",
               index + 1, summary.conductor_channels[index],
               summary.conductor_energy[index]);
    printf("  direct unit energy=%.15Lg\n", summary.direct_energy);
    printf("  conductor-spectral energy=%.15Lg\n",
           summary.spectral_energy);
    printf("  Parseval energy error %.3Le\n", summary.energy_error);
    printf("  maximum induced factorization error %.3Le\n",
           summary.maximum_factorization_error);
    printf("  maximum depth/boundary pairing error %.3Le\n",
           summary.maximum_boundary_pairing_error);
    printf("  maximum unit-boundary reconstruction error %.3Le\n",
           summary.unit_reconstruction_error);
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    free(weights);
    bbf_context_free(&context);
    return ok ? 0 : 1;
}

int boundary_sawtooth_correlation_inspect(
        int prime, int depth, int first, int second)
{
    long double direct = 0.0L;
    long double dedekind = 0.0L;
    long double error = 0.0L;
    int ok = boundary_sawtooth_correlation(
        prime, depth, first, second, &direct, &dedekind, &error);
    if (!ok && direct == 0.0L && dedekind == 0.0L && error == 0.0L) {
        fprintf(stderr,
                "require an odd prime p, depth>=1, p^depth<=20000, and two unit indices\n");
        return 1;
    }
    printf("Unit sawtooth correlation\n\n");
    printf("  p=%d depth=%d indices=(%d,%d)\n",
           prime, depth, first, second);
    printf("  direct unit-index correlation=%.15Lg\n", direct);
    printf("  Mobius-Dedekind combination=%.15Lg\n", dedekind);
    printf("  error %.3Le\n", error);
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int boundary_bernoulli_factorization_terminal(
        int prime, int depth, int character_exponent)
{
    BbfContext context = {0};
    int leading_place = 0;
    int middle_count = 1;
    if (depth < 2 || !bbf_context_build(prime, depth, &context)) {
        fprintf(stderr,
                "terminal support requires an odd prime, depth>=2, and p^depth<=20000\n");
        return 1;
    }
    for (int index = 1; index < depth; index++) middle_count *= prime;
    leading_place = middle_count;
    middle_count /= prime;
    int *weights = calloc((size_t)context.modulus, sizeof(*weights));
    if (!weights) {
        bbf_context_free(&context);
        return 1;
    }
    int support_size = 0;
    for (int digit = 0; digit < prime; digit++) {
        for (int middle = 0; middle < middle_count; middle++) {
            int cell = digit * leading_place + prime * middle + digit;
            weights[cell] = 1;
            support_size++;
        }
    }
    int status = bbf_print_comparison(
        &context, character_exponent, weights, support_size,
        "terminal first-digit/last-digit collision");
    free(weights);
    bbf_context_free(&context);
    return status;
}

static int bbf_displayed_case(void)
{
    BbfContext context = {0};
    if (!bbf_context_build(3, 2, &context)) return 0;
    int weights[9] = {1, 0, 0, 0, 1, 0, 0, 0, 1};
    BbfComparison comparison;
    int ok = bbf_compare(&context, 1, weights, 9, &comparison);
    long double root_three = sqrtl(3.0L);
    ok = ok &&
        cabsl(comparison.direct_transform -
              (2.0L - 2.0L * root_three * I)) < 1.0e-12L &&
        cabsl(comparison.bernoulli -
              (-1.0L + root_three / 3.0L * I)) < 1.0e-12L &&
        cabsl(comparison.boundary_flux -
              (3.0L - root_three * I)) < 1.0e-12L &&
        comparison.visible_endpoints == 4 && comparison.visible_norm == 4;
    bbf_context_free(&context);
    return ok;
}

static int bbf_modulus_six_blind_spot(void)
{
    int weights[6] = {1, 1, 0, 0, 0, 0};
    long long boundary[6] = {0};
    long double observable[6] = {0.0L};
    for (int residue = 0; residue < 6; residue++) {
        int previous = residue == 0 ? 5 : residue - 1;
        boundary[residue] = weights[previous] - weights[residue];
    }
    for (int multiplier = 1; multiplier < 6; multiplier++) {
        if (bbf_gcd(multiplier, 6) != 1) continue;
        for (int cell = 0; cell < 6; cell++)
            observable[multiplier] -= (long double)weights[cell] *
                (bbf_sawtooth((long long)(cell + 1) * multiplier, 6) -
                 bbf_sawtooth((long long)cell * multiplier, 6));
    }
    long double ordinary_flux = 0.0L;
    for (int residue = 0; residue < 6; residue++) {
        long double character = residue == 1 ? 1.0L :
                                residue == 5 ? -1.0L : 0.0L;
        ordinary_flux += boundary[residue] * character;
    }
    long double induced_transform = observable[1] - observable[5];
    return boundary[0] == -1 && boundary[2] == 1 &&
           fabsl(ordinary_flux) < 1.0e-15L &&
           fabsl(observable[1] - 1.0L / 6.0L) < 1.0e-15L &&
           fabsl(observable[5] + 1.0L / 6.0L) < 1.0e-15L &&
           fabsl(induced_transform - 1.0L / 3.0L) < 1.0e-15L;
}

static int bbf_lifted_support_invisibility(int *character_count)
{
    BbfContext context = {0};
    if (!character_count || !bbf_context_build(3, 3, &context)) return 0;
    int weights[27] = {0};
    for (int block = 0; block < 3; block++) {
        int start = block * 12;
        for (int offset = 0; offset < 3; offset++) weights[start + offset] = 1;
    }
    int endpoints_ok = 1;
    for (int residue = 0; residue < context.modulus; residue++) {
        int previous = residue == 0 ? context.modulus - 1 : residue - 1;
        int boundary = weights[previous] - weights[residue];
        if (boundary != 0 && residue % 3 != 0) endpoints_ok = 0;
    }
    int transforms_ok = 1;
    *character_count = 0;
    for (int exponent = 1; exponent < context.phi; exponent++) {
        if (!bbf_character_is_primitive(&context, exponent)) continue;
        BbfComparison comparison;
        (*character_count)++;
        if (!bbf_compare(
                &context, exponent, weights, context.modulus, &comparison) ||
            cabsl(comparison.direct_transform) > 1.0e-12L ||
            cabsl(comparison.boundary_flux) > 1.0e-12L)
            transforms_ok = 0;
    }
    bbf_context_free(&context);
    return endpoints_ok && transforms_ok;
}

static int bbf_conductor_spectrum_models(
        int *model_count, int *channel_count,
        long double *maximum_factor_error,
        long double *maximum_pairing_error,
        long double *maximum_reconstruction_error,
        long double *maximum_energy_error)
{
    static const int cases[][2] = {{3, 2}, {3, 3}, {5, 2}, {7, 2}};
    int all_ok = 1;
    *model_count = 0;
    *channel_count = 0;
    *maximum_factor_error = 0.0L;
    *maximum_pairing_error = 0.0L;
    *maximum_reconstruction_error = 0.0L;
    *maximum_energy_error = 0.0L;

    for (size_t case_index = 0;
         case_index < sizeof(cases) / sizeof(cases[0]); case_index++) {
        int prime = cases[case_index][0];
        int depth = cases[case_index][1];
        BbfContext context = {0};
        if (!bbf_context_build(prime, depth, &context)) return 0;
        int *weights = calloc((size_t)context.modulus, sizeof(*weights));
        if (!weights) {
            bbf_context_free(&context);
            return 0;
        }
        int leading = 1;
        int middle_count = 1;
        for (int index = 1; index < depth; index++) leading *= prime;
        for (int index = 2; index < depth; index++) middle_count *= prime;
        for (int digit = 0; digit < prime; digit++)
            for (int middle = 0; middle < middle_count; middle++)
                weights[digit * leading + prime * middle + digit] = 1;

        CarryBoundarySpectrumSummary summary = {0};
        int ok = boundary_bernoulli_conductor_spectrum(
            prime, depth, weights, context.modulus, &summary);
        (*model_count)++;
        *channel_count += summary.odd_channels;
        if (!ok || summary.odd_channels != context.phi / 2) all_ok = 0;
        if (summary.maximum_factorization_error > *maximum_factor_error)
            *maximum_factor_error = summary.maximum_factorization_error;
        if (summary.maximum_boundary_pairing_error > *maximum_pairing_error)
            *maximum_pairing_error = summary.maximum_boundary_pairing_error;
        if (summary.unit_reconstruction_error > *maximum_reconstruction_error)
            *maximum_reconstruction_error = summary.unit_reconstruction_error;
        if (summary.energy_error > *maximum_energy_error)
            *maximum_energy_error = summary.energy_error;
        if (prime == 3 && depth == 2) {
            if (summary.odd_channels != 3 ||
                summary.conductor_channels[0] != 1 ||
                summary.conductor_channels[1] != 2 ||
                fabsl(summary.conductor_energy[0]) > 1.0e-12L ||
                fabsl(summary.conductor_energy[1] - 16.0L / 3.0L) >
                    1.0e-11L ||
                fabsl(summary.direct_energy - 16.0L / 3.0L) > 1.0e-11L)
                all_ok = 0;
        }
        free(weights);
        bbf_context_free(&context);
    }
    return all_ok;
}

static int bbf_correlation_models(
        int *model_count, long double *maximum_error)
{
    static const int primes[] = {3, 5, 7};
    int all_ok = 1;
    *model_count = 0;
    *maximum_error = 0.0L;
    for (size_t prime_index = 0;
         prime_index < sizeof(primes) / sizeof(primes[0]); prime_index++) {
        for (int depth = 1; depth <= 3; depth++) {
            BbfContext context = {0};
            if (!bbf_context_build(primes[prime_index], depth, &context))
                continue;
            for (int second = 1; second < context.modulus; second++) {
                if (!context.is_unit[second]) continue;
                long double direct = 0.0L;
                long double dedekind = 0.0L;
                long double error = 0.0L;
                (*model_count)++;
                if (!boundary_sawtooth_correlation(
                        primes[prime_index], depth, 1, second,
                        &direct, &dedekind, &error))
                    all_ok = 0;
                if (error > *maximum_error) *maximum_error = error;
            }
            bbf_context_free(&context);
        }
    }
    return all_ok;
}

int boundary_bernoulli_factorization_verify(void)
{
    int displayed_ok = bbf_displayed_case();
    int basis_ok = 1;
    int terminal_ok = 1;
    int parity_ok = 1;
    int blind_spot_ok = bbf_modulus_six_blind_spot();
    int conductor_ok = 1;
    int reconstruction_ok = 1;
    int lifted_characters = 0;
    int lifted_ok = bbf_lifted_support_invisibility(&lifted_characters);
    int correlation_ok = 1;
    int domain_ok = 1;
    int basis_models = 0;
    int terminal_models = 0;
    int even_models = 0;
    int conductor_models = 0;
    int conductor_channels = 0;
    int correlation_models = 0;
    long double maximum_error = 0.0L;
    long double maximum_conductor_error = 0.0L;
    long double maximum_pairing_error = 0.0L;
    long double maximum_reconstruction_error = 0.0L;
    long double maximum_energy_error = 0.0L;
    long double maximum_correlation_error = 0.0L;

    static const int basis_primes[] = {3, 5, 7};
    for (size_t case_index = 0;
         case_index < sizeof(basis_primes) / sizeof(basis_primes[0]);
         case_index++) {
        BbfContext context = {0};
        if (!bbf_context_build(basis_primes[case_index], 2, &context))
            return 0;
        int *weights = calloc((size_t)context.modulus, sizeof(*weights));
        if (!weights) return 0;
        for (int cell = 0; cell < context.modulus; cell++) {
            weights[cell] = 1;
            for (int exponent = 1; exponent < context.phi; exponent++) {
                if (!bbf_character_is_primitive(&context, exponent)) continue;
                BbfComparison comparison;
                basis_models++;
                if (!bbf_compare(
                        &context, exponent, weights,
                        context.modulus, &comparison))
                    basis_ok = 0;
                if (comparison.factorization_error > maximum_error)
                    maximum_error = comparison.factorization_error;
                if (!comparison.odd) {
                    even_models++;
                    if (cabsl(comparison.direct_transform) > 1.0e-10L ||
                        cabsl(comparison.bernoulli) > 1.0e-10L)
                        parity_ok = 0;
                }
            }
            weights[cell] = 0;
        }
        free(weights);
        bbf_context_free(&context);
    }

    static const int terminal_cases[][2] = {
        {3, 2}, {3, 3}, {3, 4}, {5, 2},
        {5, 3}, {7, 2}, {11, 2}
    };
    for (size_t case_index = 0;
         case_index < sizeof(terminal_cases) / sizeof(terminal_cases[0]);
         case_index++) {
        int prime = terminal_cases[case_index][0];
        int depth = terminal_cases[case_index][1];
        BbfContext context = {0};
        if (!bbf_context_build(prime, depth, &context)) return 0;
        int *weights = calloc((size_t)context.modulus, sizeof(*weights));
        if (!weights) return 0;
        int leading = 1;
        int middle_count = 1;
        for (int index = 1; index < depth; index++) leading *= prime;
        for (int index = 2; index < depth; index++) middle_count *= prime;
        for (int digit = 0; digit < prime; digit++)
            for (int middle = 0; middle < middle_count; middle++)
                weights[digit * leading + prime * middle + digit] = 1;
        for (int exponent = 1; exponent < context.phi; exponent++) {
            if (!bbf_character_is_primitive(&context, exponent) ||
                exponent % 2 == 0)
                continue;
            BbfComparison comparison;
            terminal_models++;
            if (!bbf_compare(
                    &context, exponent, weights,
                    context.modulus, &comparison))
                terminal_ok = 0;
            if (comparison.factorization_error > maximum_error)
                maximum_error = comparison.factorization_error;
        }
        free(weights);
        bbf_context_free(&context);
    }

    conductor_ok = bbf_conductor_spectrum_models(
        &conductor_models, &conductor_channels,
        &maximum_conductor_error, &maximum_pairing_error,
        &maximum_reconstruction_error, &maximum_energy_error);
    reconstruction_ok = conductor_ok &&
        maximum_reconstruction_error <= 1.0e-10L &&
        maximum_energy_error <= 1.0e-10L;
    correlation_ok = bbf_correlation_models(
        &correlation_models, &maximum_correlation_error);

    int weights[9] = {1, 0, 0, 0, 1, 0, 0, 0, 1};
    long double factor_error = 0.0L;
    long double boundary_error = 0.0L;
    int visible = 0;
    domain_ok = !boundary_bernoulli_factorization_compare(
        2, 2, 1, weights, 9,
        &factor_error, &boundary_error, &visible) &&
        !boundary_bernoulli_factorization_compare(
            3, 2, 3, weights, 9,
            &factor_error, &boundary_error, &visible) &&
        !boundary_bernoulli_conductor_spectrum(
            2, 2, weights, 9,
            &(CarryBoundarySpectrumSummary){0}) &&
        !boundary_sawtooth_correlation(
            3, 2, 3, 1,
            &(long double){0}, &(long double){0}, &(long double){0});

    int passed = displayed_ok + basis_ok + terminal_ok + parity_ok +
                 blind_spot_ok + conductor_ok + reconstruction_ok + lifted_ok +
                 correlation_ok + domain_ok;
    printf("Boundary-Bernoulli factorization verification\n\n");
    printf("  displayed modulus-nine transform and boundary values  %s\n",
           displayed_ok ? "PASS" : "FAIL");
    printf("  primitive character/cell-basis models=%d              %s\n",
           basis_models, basis_ok ? "PASS" : "FAIL");
    printf("  terminal primitive-odd models=%d                       %s\n",
           terminal_models, terminal_ok ? "PASS" : "FAIL");
    printf("  even primitive models=%d vanish                         %s\n",
           even_models, parity_ok ? "PASS" : "FAIL");
    printf("  modulus-six nonunit blind spot and induced response      %s\n",
           blind_spot_ok ? "PASS" : "FAIL");
    printf("  conductor-depth spectra=%d; odd source channels=%d       %s\n",
           conductor_models, conductor_channels,
           conductor_ok ? "PASS" : "FAIL");
    printf("  unit reconstruction and prime-power energy Parseval      %s\n",
           reconstruction_ok ? "PASS" : "FAIL");
    printf("  lifted-support primitive channels=%d vanish               %s\n",
           lifted_characters, lifted_ok ? "PASS" : "FAIL");
    printf("  unit sawtooth Mobius-Dedekind correlations=%d             %s\n",
           correlation_models, correlation_ok ? "PASS" : "FAIL");
    printf("  odd-prime, primitive-character, and unit domain rejection %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("  maximum numerical factorization error %.3Le\n",
           maximum_error);
    printf("  maximum induced factorization error %.3Le\n",
           maximum_conductor_error);
    printf("  maximum depth/boundary pairing error %.3Le\n",
           maximum_pairing_error);
    printf("  maximum unit reconstruction error %.3Le\n",
           maximum_reconstruction_error);
    printf("  maximum energy Parseval error %.3Le\n",
           maximum_energy_error);
    printf("  maximum Mobius-Dedekind correlation error %.3Le\n",
           maximum_correlation_error);
    printf("\n%d/10 verification groups passed.\n", passed);
    printf("Exact boundary  supports, signed boundary derivatives, unit visibility,\n");
    printf("and squared norms use integer arithmetic.\n");
    printf("Numerical boundary  roots of unity, primitive and induced transforms,\n");
    printf("Bernoulli values, conductor energies, and sawtooth correlations use\n");
    printf("long-double complex arithmetic at tolerance %.1Le.\n", BBF_TOLERANCE);
    printf("Scope  reusable finite supports on cyclic odd-prime-power residue spaces;\n");
    printf("the modulus-six regression isolates the induced nonunit blind spot.\n");
    return passed == 10;
}

void boundary_bernoulli_factorization_help(void)
{
    printf(
        "Boundary-Bernoulli factorization\n\n"
        "Commands\n"
        "  nfield boundary-bernoulli-factorization inspect <p> <depth> <exponent>\n"
        "      --support <cell,cell,...>\n"
        "      Inspect any finite support modulo the odd prime power p^depth.\n"
        "  nfield boundary-bernoulli-factorization terminal <p> <depth> <exponent>\n"
        "      Build the terminal collision support automatically.\n"
        "  nfield boundary-bernoulli-factorization spectrum <p> <depth>\n"
        "      --support <cell,cell,...>\n"
        "      Decompose the complete odd carry energy by primitive conductor.\n"
        "  nfield boundary-bernoulli-factorization correlation <p> <depth> <x> <y>\n"
        "      Compare a unit sawtooth correlation with its Mobius-Dedekind form.\n"
        "  nfield boundary-bernoulli-factorization verify\n"
        "  nfield verify boundary-bernoulli-factorization\n\n"
        "Example\n"
        "  nfield boundary-bernoulli-factorization inspect 3 2 1\n"
        "      --support 0,4,8\n"
        "  nfield boundary-bernoulli-factorization spectrum 3 2\n"
        "      --support 0,4,8\n"
        "  nfield boundary-bernoulli-factorization correlation 3 2 1 2\n\n"
        "Scope\n"
        "  proved       primitive odd transform equals minus the generalized\n"
        "               Bernoulli value times the visible boundary flux; even\n"
        "               primitive channels vanish.\n"
        "  exact        support, signed boundary derivative, unit visibility,\n"
        "               endpoint count, and squared boundary norm.\n"
        "  numerical    roots of unity, primitive and induced transforms,\n"
        "               Bernoulli values, conductor energies, unit inversion,\n"
        "               and Mobius-Dedekind correlations.\n"
        "  boundary     the public computation covers cyclic odd prime powers\n"
        "               p^depth<=20000 and one exact modulus-six blind spot;\n"
        "               symbolic theorems may have wider domains.\n"
    );
}
