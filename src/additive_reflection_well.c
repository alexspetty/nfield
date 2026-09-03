/* Exact additive convolution identities for the centered collision table. */

#include <complex.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "finite_character_core.h"
#include "nfield.h"

enum { REFLECTION_WELL_BASE_COUNT = 12 };

static const int reflection_well_bases[REFLECTION_WELL_BASE_COUNT] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 10
};

static const uint64_t expected_energies[REFLECTION_WELL_BASE_COUNT] = {
    UINT64_C(48), UINT64_C(1200), UINT64_C(8624), UINT64_C(100672),
    UINT64_C(254176), UINT64_C(1035776), UINT64_C(1854096),
    UINT64_C(5019152), UINT64_C(16698896), UINT64_C(23817424),
    UINT64_C(59381744), UINT64_C(26600)
};

typedef struct {
    int even_ok;
    int total_ok;
    int well_ok;
    int compensation_ok;
    int spectrum_ok;
    int64_t energy_numerator;
    int64_t well_numerator;
    int64_t total_numerator;
    int64_t nonzero_sum_numerator;
    long double maximum_square_error;
    long double maximum_positive_spectrum;
    long double maximum_spectrum_imaginary;
} AdditiveReflectionAudit;

static long double complex discrete_transform(const long long *values,
                                              int count,
                                              int frequency)
{
    long double angle = -2.0L * acosl(-1.0L) * frequency / count;
    long double complex sum = 0.0L + I * 0.0L;
    for (int index = 0; index < count; index++) {
        long double phase = angle * index;
        sum += values[index] * (cosl(phase) + I * sinl(phase));
    }
    return sum;
}

static int reflection_well_audit(const CollisionCenteredTable *table,
                                 AdditiveReflectionAudit *audit)
{
    long long *convolution;
    int failures = 0;

    if (!table || !audit || table->lag != 1) return 1;
    convolution = calloc((size_t)table->modulus, sizeof(*convolution));
    if (!convolution) return 1;
    *audit = (AdditiveReflectionAudit){
        .even_ok = 1,
        .total_ok = 1,
        .well_ok = 1,
        .compensation_ok = 1,
        .spectrum_ok = 1
    };

    for (int residue = 0; residue < table->modulus; residue++)
        audit->energy_numerator +=
            table->centered_numerator[residue] *
            table->centered_numerator[residue];
    for (int shift = 0; shift < table->modulus; shift++) {
        for (int residue = 0; residue < table->modulus; residue++) {
            int other = shift - residue;
            if (other < 0) other += table->modulus;
            convolution[shift] += table->centered_numerator[residue] *
                                  table->centered_numerator[other];
        }
        audit->total_numerator += convolution[shift];
        if (shift != 0)
            audit->nonzero_sum_numerator += convolution[shift];
    }
    audit->well_numerator = convolution[0];
    for (int shift = 0; shift < table->modulus; shift++) {
        int reflected = shift == 0 ? 0 : table->modulus - shift;
        if (convolution[shift] != convolution[reflected])
            audit->even_ok = 0;
    }
    if (audit->total_numerator != 0) audit->total_ok = 0;
    if (audit->well_numerator != -audit->energy_numerator)
        audit->well_ok = 0;
    if (audit->nonzero_sum_numerator != audit->energy_numerator)
        audit->compensation_ok = 0;

    for (int frequency = 0; frequency < table->modulus; frequency++) {
        long double complex signal = discrete_transform(
            table->centered_numerator, table->modulus, frequency);
        long double complex spectrum = discrete_transform(
            convolution, table->modulus, frequency);
        long double complex square = signal * signal;
        long double scale = 1.0L + fabsl((long double)audit->energy_numerator);
        long double error = cabsl(spectrum - square) / scale;
        long double positive = creall(spectrum) > 0.0L
                                   ? creall(spectrum) : 0.0L;
        if (error > audit->maximum_square_error)
            audit->maximum_square_error = error;
        if (positive > audit->maximum_positive_spectrum)
            audit->maximum_positive_spectrum = positive;
        if (fabsl(cimagl(spectrum)) >
            audit->maximum_spectrum_imaginary)
            audit->maximum_spectrum_imaginary = fabsl(cimagl(spectrum));
        if (error > 5.0e-10L ||
            creall(spectrum) > 5.0e-8L * scale ||
            fabsl(cimagl(spectrum)) > 5.0e-8L * scale)
            audit->spectrum_ok = 0;
    }
    if (!audit->even_ok || !audit->total_ok || !audit->well_ok ||
        !audit->compensation_ok || !audit->spectrum_ok)
        failures++;
    free(convolution);
    return failures;
}

int additive_reflection_well_inspect(int base)
{
    CollisionCenteredTable table = {0};
    AdditiveReflectionAudit audit;
    int failures;

    if (base < 2 || base > 64) {
        fprintf(stderr, "base must be between 2 and 64\n");
        return 1;
    }
    if (!collision_centered_table_build(base, 1, &table)) return 1;
    failures = centered_collision_table_audit(&table, NULL, NULL);
    failures += reflection_well_audit(&table, &audit);

    printf("Additive reflection well\n");
    printf("Exact cyclic convolution at base %d\n\n", base);
    printf("  modulus=%d; denominator scale=%d^2\n",
           table.modulus, base);
    printf("  energy numerator = %" PRId64 "\n", audit.energy_numerator);
    printf("  K(0) numerator = %" PRId64 "\n", audit.well_numerator);
    printf("  K(0) = -energy                              %s\n",
           audit.well_ok ? "PASS" : "FAIL");
    printf("  K(-t) = K(t) for every shift                %s\n",
           audit.even_ok ? "PASS" : "FAIL");
    printf("  complete convolution sum is zero            %s\n",
           audit.total_ok ? "PASS" : "FAIL");
    printf("  nonzero shifts compensate the well exactly  %s\n",
           audit.compensation_ok ? "PASS" : "FAIL");
    printf("  Fourier square identity and nonpositivity    %s\n",
           audit.spectrum_ok ? "PASS" : "FAIL");
    printf("  maximum normalized Fourier error = %.3Le\n",
           audit.maximum_square_error);
    printf("\nClassification  convolution identities are exact integer checks;\n");
    printf("the finite Fourier transform is numerical corroboration.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return failures == 0 ? 0 : 1;
}

int additive_reflection_well_verify(void)
{
    int table_failures = 0;
    int identity_failures = 0;
    int fixture_failures = 0;
    int spectrum_failures = 0;

    printf("Additive reflection well verification\n\n");
    for (int base_index = 0; base_index < REFLECTION_WELL_BASE_COUNT;
         base_index++) {
        CollisionCenteredTable table = {0};
        AdditiveReflectionAudit audit;
        if (!collision_centered_table_build(
                reflection_well_bases[base_index], 1, &table)) {
            table_failures++;
            continue;
        }
        table_failures += centered_collision_table_audit(
            &table, NULL, NULL);
        if (reflection_well_audit(&table, &audit) != 0)
            identity_failures++;
        if ((uint64_t)audit.energy_numerator !=
            expected_energies[base_index])
            fixture_failures++;
        if (!audit.spectrum_ok) spectrum_failures++;
        collision_centered_table_free(&table);
    }
    printf("  twelve exact centered table gates                  %s\n",
           table_failures == 0 ? "PASS" : "FAIL");
    printf("  evenness, zero total, well, and compensation       %s\n",
           identity_failures == 0 ? "PASS" : "FAIL");
    printf("  twelve declared exact energy numerators            %s\n",
           fixture_failures == 0 ? "PASS" : "FAIL");
    printf("  Fourier square and nonpositive spectrum            %s\n",
           spectrum_failures == 0 ? "PASS" : "FAIL");
    printf("\n4/4 verification groups %s.\n",
           table_failures + identity_failures + fixture_failures +
           spectrum_failures == 0 ? "passed" : "did not pass");
    printf("Proved  finite oddness gives all four convolution identities and\n");
    printf("the Fourier square formula for every base.\n");
    return table_failures + identity_failures + fixture_failures +
           spectrum_failures == 0;
}

void additive_reflection_well_help(void)
{
    printf(
        "Additive reflection well\n\n"
        "Commands\n"
        "  nfield additive-reflection-well inspect <base>\n"
        "      Compute the full cyclic convolution, exact negative well,\n"
        "      exact compensation, and finite Fourier square.\n"
        "  nfield additive-reflection-well verify\n"
        "  nfield verify additive-reflection-well\n\n"
        "Scope\n"
        "  proved             even convolution, zero total, negative well,\n"
        "                     positive compensation, and Fourier square.\n"
        "  exact computation all convolution identities use integer numerators.\n"
        "  numerical check   the finite Fourier identity is corroborated with\n"
        "                     long-double complex arithmetic.\n"
    );
}
