/* Centered gate and full-to-primitive odd sector factorization. */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "finite_character_core.h"
#include "nfield.h"
#include "primitive_odd_sector_core.h"

enum { PRIMITIVE_SECTOR_BASE_COUNT = 11 };

static const int sector_bases[PRIMITIVE_SECTOR_BASE_COUNT] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
};

static const int sector_cutoffs[PRIMITIVE_ODD_MAX_CUTOFFS] = {
    250000, 500000, 1000000, 2000000, 3000000, 5000000
};

static int validate_base_and_cutoff(int base, int cutoff)
{
    if (!finite_character_is_prime(base) || base == 2) {
        fprintf(stderr, "base must be an odd prime\n");
        return 0;
    }
    if (base > 37) {
        fprintf(stderr, "base must not exceed 37 for this finite sector audit\n");
        return 0;
    }
    if (cutoff <= base * base || cutoff > FINITE_CHARACTER_MAX_CUTOFF) {
        fprintf(stderr, "cutoff must satisfy base^2 < cutoff <= %d\n",
                FINITE_CHARACTER_MAX_CUTOFF);
        return 0;
    }
    return 1;
}

int primitive_odd_sector_inspect(int base, int cutoff)
{
    PrimitiveOddSectorResult result = {0};
    const PrimitiveOddSectorRow *row;
    int *primes;
    int prime_count = 0;
    int failures = 0;

    if (!validate_base_and_cutoff(base, cutoff)) return 1;
    primes = finite_character_primes(cutoff, &prime_count);
    if (!primes) {
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures += primitive_odd_sector_compute(
        base, primes, prime_count, &cutoff, 1, &result);
    free(primes);
    if (failures) return 1;
    failures += centered_collision_table_audit(&result.table, NULL, NULL);
    row = &result.row[0];

    printf("Primitive odd sector\n");
    printf("Centered gate and sector factorization\n\n");
    printf("  base=%d modulus=%d cutoff=%d\n",
           base, result.table.modulus, cutoff);
    printf("  odd characters=%d\n", row->odd_characters);
    printf("  primitive odd characters=%d; induced odd characters=%d\n",
           row->active_characters, row->inactive_characters);
    printf("  primitive conjugate pairs=%d\n", row->conjugate_pairs);
    printf("  exact centered reflection and fiber-zero gate  %s\n",
           failures == 0 ? "PASS" : "FAIL");
    printf("  maximum even-character energy fraction = %.3Le  %s\n",
           result.maximum_even_energy_fraction,
           result.maximum_even_energy_fraction <= 1.0e-16L
               ? "PASS" : "FAIL");
    printf("  maximum induced-character energy fraction = %.3Le  %s\n",
           result.maximum_induced_energy_fraction,
           result.maximum_induced_energy_fraction <= 1.0e-16L
               ? "PASS" : "FAIL");
    printf("  conjugate energy error = %.3Le  %s\n",
           row->conjugate_error, row->conjugacy_ok ? "PASS" : "FAIL");
    printf("\n  primitive-sector overlap rho = %.12Lf\n", row->rho);
    printf("  relabeling variance = %.12Lf\n", row->relabeling_variance);
    if (row->z_defined)
        printf("  standardized displacement Z = %+.12Lf\n", row->z);
    else
        printf("  standardized displacement Z = undefined (one conjugate pair)\n");
    printf("  collision entropy H = %.12Lf\n",
           logl(row->collision_support));
    printf("  collision effective support exp(H) = %.12Lf\n",
           row->collision_support);
    printf("  prime entropy H = %.12Lf\n", logl(row->prime_support));
    printf("  prime effective support exp(H) = %.12Lf\n",
           row->prime_support);
    printf("  primitive prime-energy occupancy eta = %.12Lf\n",
           row->primitive_occupancy);
    printf("  full odd-sector overlap = %.12Lf\n", row->full_odd_rho);
    printf("  sector-factorization error = %.3Le  %s\n",
           row->factorization_error,
           fabsl(row->factorization_error) <= 1.0e-11L
               ? "PASS" : "FAIL");
    printf("\nClassification\n");
    printf("  proved structure  the centered gate and sector factorization follow\n");
    printf("                    from finite character orthogonality.\n");
    printf("  exact input       the centered table is checked with integer arithmetic.\n");
    printf("  finite numerical  character energies use primes b^2 < p < %d.\n",
           cutoff);
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    primitive_odd_sector_result_free(&result);
    return failures == 0 ? 0 : 1;
}

int primitive_odd_sector_verify(void)
{
    int *primes;
    int prime_count = 0;
    int table_failures = 0;
    int count_failures = 0;
    int conjugacy_failures = 0;
    int factorization_failures = 0;
    int base_three_failures = 0;
    int rows = 0;

    printf("Primitive odd sector verification\n\n");
    primes = finite_character_primes(
        FINITE_CHARACTER_MAX_CUTOFF, &prime_count);
    if (!primes) {
        printf("unable to allocate the prime sieve\n");
        return 0;
    }
    for (int base_index = 0; base_index < PRIMITIVE_SECTOR_BASE_COUNT;
         base_index++) {
        PrimitiveOddSectorResult result = {0};
        int base = sector_bases[base_index];
        if (primitive_odd_sector_compute(
                base, primes, prime_count, sector_cutoffs,
                PRIMITIVE_ODD_MAX_CUTOFFS, &result) != 0) {
            table_failures++;
            continue;
        }
        table_failures += centered_collision_table_audit(
            &result.table, NULL, NULL);
        if (result.maximum_even_energy_fraction > 1.0e-16L ||
            result.maximum_induced_energy_fraction > 1.0e-16L)
            table_failures++;
        for (int cutoff_index = 0;
             cutoff_index < PRIMITIVE_ODD_MAX_CUTOFFS; cutoff_index++) {
            const PrimitiveOddSectorRow *row = &result.row[cutoff_index];
            int expected_odd = base * (base - 1) / 2;
            int expected_active = (base - 1) * (base - 1) / 2;
            int expected_pairs = (base - 1) * (base - 1) / 4;
            rows++;
            if (row->odd_characters != expected_odd ||
                row->active_characters != expected_active ||
                row->inactive_characters != (base - 1) / 2 ||
                row->conjugate_pairs != expected_pairs)
                count_failures++;
            if (!row->conjugacy_ok) conjugacy_failures++;
            if (fabsl(row->factorization_error) > 1.0e-11L)
                factorization_failures++;
            if (base == 3 && fabsl(row->rho - 1.0L) > 1.0e-12L)
                base_three_failures++;
        }
        primitive_odd_sector_result_free(&result);
    }
    free(primes);

    printf("  eleven centered gates, including even and induced channels  %s\n",
           table_failures == 0 ? "PASS" : "FAIL");
    printf("  eleven distinct sector classifications across %d rows  %s\n",
           rows, count_failures == 0 ? "PASS" : "FAIL");
    printf("  conjugate character energies agree in every row     %s\n",
           conjugacy_failures == 0 ? "PASS" : "FAIL");
    printf("  full odd-sector overlap factors in every row        %s\n",
           factorization_failures == 0 ? "PASS" : "FAIL");
    printf("  base-three one-pair overlap is identically one      %s\n",
           base_three_failures == 0 ? "PASS" : "FAIL");
    printf("\n5/5 verification groups %s.\n",
           table_failures + count_failures + conjugacy_failures +
           factorization_failures + base_three_failures == 0
               ? "passed" : "did not pass");
    printf("Proof boundary  the structural propositions are algebraic. This\n");
    printf("verifier checks exact tables and 66 finite spectra.\n");
    return table_failures + count_failures + conjugacy_failures +
           factorization_failures + base_three_failures == 0;
}

void primitive_odd_sector_help(void)
{
    printf(
        "Primitive odd sector\n\n"
        "Commands\n"
        "  nfield primitive-odd-sector inspect <odd-prime-base> [--cutoff <X>]\n"
        "      Check the centered gate, character counts, conjugate pairs,\n"
        "      relabeling variance, standardized displacement, entropy support,\n"
        "      primitive occupancy, and full-sector factorization.\n"
        "  nfield primitive-odd-sector verify\n"
        "  nfield verify primitive-odd-sector\n\n"
        "Scope\n"
        "  proved             centered gate and sector factorization.\n"
        "  exact computation centered table, reflections, and fiber sums.\n"
        "  finite numerical  character energies at the printed cutoff.\n"
        "  open              no limiting overlap or convergence assertion.\n"
    );
}
