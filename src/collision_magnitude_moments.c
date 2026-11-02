/* Normalized finite moments of short sums and Bernoulli magnitudes. */
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include "collision_spectrum_core.h"
#include "collision_magnitude_moments.h"

static long double relative_error(long double actual, long double expected)
{
    return fabsl(actual - expected) / (1.0L + fabsl(expected));
}

CollisionMagnitudeMoments collision_magnitude_moments(int base)
{
    CollisionMagnitudeMoments row = {.base = base};
    CollisionSpectrumContext context;
    const long double pi = acosl(-1.0L);
    if (base < 5 || !collision_spectrum_context_build(base, &context)) {
        row.failures = 1;
        return row;
    }
    for (int level = 0; level < 2; level++) {
        int64_t modulus = level ? context.modulus : base;
        int64_t twisted_sum = 0;
        for (int64_t a = 1; a < modulus; a++)
            twisted_sum += a * (2 * ((2 * a) % modulus) - modulus);
        if (12 * twisted_sum != modulus * (modulus - 1) * (modulus - 5))
            row.failures++;
    }
    for (int a = 1; a < context.modulus; a++) {
        if (a % base == 0) continue;
        int64_t value = context.table.centered_numerator[a];
        row.energy_numerator += value * value;
    }
    for (int j = 1; j < context.phi; j += 2) {
        if (!collision_spectrum_character_is_primitive_odd(&context, j)) continue;
        CollisionSpectrumCharacter character;
        if (!collision_spectrum_character_compute(&context, j, &character)) {
            row.failures++;
            continue;
        }
        long double x = cabsl(character.short_sum) / sqrtl(base);
        long double y = character.l_one_magnitude;
        int64_t phase = (int64_t)j * context.discrete_log[2] % context.phi;
        long double angle = 2 * pi * phase / context.phi;
        long double chi2_real = cosl(angle), chi2_imag = sinl(angle);
        row.mean_x += x;
        row.mean_y += y;
        row.mean_xy += x * y;
        row.mean_x2 += x * x;
        row.mean_y2 += y * y;
        row.mean_x2y2 += x * x * y * y;
        row.mean_x_three_halves += x * sqrtl(x);
        row.mean_y3 += y * y * y;
        row.mean_y4 += y * y * y * y;
        row.mean_chi2_real += chi2_real;
        row.mean_chi2_imag += chi2_imag;
        row.mean_y2_chi2_real += y * y * chi2_real;
        row.mean_y2_chi2_imag += y * y * chi2_imag;
        row.count++;
    }
    if (row.count != (base - 1) * (base - 1) / 2) row.failures++;
    if (row.count == 0) {
        collision_spectrum_context_free(&context);
        row.failures++;
        return row;
    }
    row.mean_x /= row.count;
    row.mean_y /= row.count;
    row.mean_xy /= row.count;
    row.mean_x2 /= row.count;
    row.mean_y2 /= row.count;
    row.mean_x2y2 /= row.count;
    row.mean_x_three_halves /= row.count;
    row.mean_y3 /= row.count;
    row.mean_y4 /= row.count;
    row.mean_chi2_real /= row.count;
    row.mean_chi2_imag /= row.count;
    row.mean_y2_chi2_real /= row.count;
    row.mean_y2_chi2_imag /= row.count;
    long double variance_x = row.mean_x2 - row.mean_x * row.mean_x;
    long double variance_y = row.mean_y2 - row.mean_y * row.mean_y;
    if (variance_x <= 0 || variance_y <= 0) row.failures++;
    row.correlation = (row.mean_xy - row.mean_x * row.mean_y) /
                      sqrtl(variance_x * variance_y);
    row.enrichment = row.mean_x2y2 / (row.mean_x2 * row.mean_y2);
    long double b = base;
    long double energy = row.energy_numerator / (b * b);
    long double nu = pi * pi / 6 * (1 - 1 / (b * b));
    row.variance_y_margin = variance_y - nu / 16;
    if (row.variance_y_margin < -2.0e-12L) row.failures++;
    long double actual[] = {row.mean_x2, row.mean_y2,
                            row.mean_x2y2, row.enrichment,
                            row.mean_chi2_real, row.mean_chi2_imag,
                            row.mean_y2_chi2_real, row.mean_y2_chi2_imag};
    long double expected[] = {
        1,
        nu,
        pi * pi * energy / (2 * b * b * (b - 1)),
        3 * energy / ((b - 1) * (b * b - 1)),
        0, 0, nu / 2, 0
    };
    for (int i = 0; i < 8; i++) {
        long double error = relative_error(actual[i], expected[i]);
        if (error > row.max_identity_error) row.max_identity_error = error;
        if (error > 2.0e-12L) row.failures++;
    }
    if (!isfinite(row.correlation) || !isfinite(row.enrichment)) row.failures++;
    collision_spectrum_context_free(&context);
    return row;
}

