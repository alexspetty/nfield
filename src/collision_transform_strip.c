/*
 * collision_transform_strip.c
 *
 * Exact finite centered-transform and prime-window tools.
 *
 * The finite table, fiber means, reflection, and centered signal use exact
 * integer arithmetic. Prime-window values use long-double arithmetic and are
 * always labeled as finite observations. Analytic continuation, zero-free
 * regions, and the zero-cancellation obstruction remain mathematical results.
 */

#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "finite_character_core.h"
#include "nfield.h"

#define CTRANS_MAX_BASE 128
#define CTRANS_MAX_MODULUS 50000
#define CTRANS_MAX_INPUT 10000000
#define CTRANS_EXPONENTS 6
#define CTRANS_BASES 5

typedef struct {
    int reflection;
    int raw_mean;
    int fiber_size;
    int mean_reflection;
    int centered_odd;
    int fiber_zero;
} CTransformChecks;

static const int ctransform_snapshot_bases[CTRANS_BASES] = {
    3, 5, 7, 10, 12
};

static const long double ctransform_snapshot_exponents[CTRANS_EXPONENTS] = {
    1.0L, 0.9L, 0.8L, 0.7L, 0.6L, 0.5L
};

static const long double
ctransform_snapshot_expected[CTRANS_EXPONENTS][CTRANS_BASES] = {
    { 0.000042L,  0.000014L, -0.000136L,  0.000065L,  0.000098L},
    { 0.000183L,  0.000016L, -0.000580L,  0.000047L,  0.000409L},
    { 0.000807L, -0.000122L, -0.002488L, -0.000868L,  0.001714L},
    { 0.003629L, -0.001345L, -0.010721L, -0.008671L,  0.007215L},
    { 0.016621L, -0.009300L, -0.046418L, -0.060258L,  0.030483L},
    { 0.077496L, -0.055134L, -0.201877L, -0.366499L,  0.129262L}
};

static int ctransform_validate(int base, int lag, int report)
{
    int modulus = 0;
    if (base < 2 || base > CTRANS_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n",
                    CTRANS_MAX_BASE);
        return 0;
    }
    if (lag < 1 || lag > 16) {
        if (report) fprintf(stderr, "lag must be between 1 and 16\n");
        return 0;
    }
    if (!collision_table_modulus(base, lag, &modulus) ||
        modulus > CTRANS_MAX_MODULUS) {
        if (report)
            fprintf(stderr,
                    "base^(lag+1) exceeds the finite-table limit of %d\n",
                    CTRANS_MAX_MODULUS);
        return 0;
    }
    return 1;
}

static unsigned char *ctransform_sieve(int limit)
{
    unsigned char *composite = calloc((size_t)limit + 1, 1);
    if (!composite) return NULL;
    composite[0] = 1;
    if (limit >= 1) composite[1] = 1;
    for (int p = 2; p <= limit / p; p++) {
        if (composite[p]) continue;
        for (int64_t multiple = (int64_t)p * p;
             multiple <= limit; multiple += p)
            composite[multiple] = 1;
    }
    return composite;
}

static CTransformChecks ctransform_check_table(
    const CollisionCenteredTable *table)
{
    CTransformChecks checks = {1, 1, 1, 1, 1, 1};
    long long raw_total = 0;

    for (int fiber = 1; fiber < table->base; fiber++) {
        if (collision_table_gcd(fiber, table->base) != 1) continue;
        if (table->fiber_count[fiber] != table->fiber_size)
            checks.fiber_size = 0;
        long long centered_total = 0;
        for (int a = fiber; a < table->modulus; a += table->base) {
            if (collision_table_gcd(a, table->modulus) != 1) continue;
            centered_total += table->centered_numerator[a];
        }
        if (centered_total != 0) checks.fiber_zero = 0;
        raw_total += table->fiber_sum[fiber];
    }
    if (2 * raw_total != -table->phi) checks.raw_mean = 0;

    for (int a = 1; a < table->modulus; a++) {
        if (collision_table_gcd(a, table->modulus) != 1) continue;
        int reflected = table->modulus - a;
        int fiber = a % table->base;
        int reflected_fiber = reflected % table->base;
        if (table->value[a] + table->value[reflected] != -1)
            checks.reflection = 0;
        if (table->fiber_sum[fiber] +
            table->fiber_sum[reflected_fiber] != -table->fiber_size)
            checks.mean_reflection = 0;
        if (table->centered_numerator[a] +
            table->centered_numerator[reflected] != 0)
            checks.centered_odd = 0;
    }
    return checks;
}

static int ctransform_checks_pass(CTransformChecks checks)
{
    return checks.reflection && checks.raw_mean && checks.fiber_size &&
           checks.mean_reflection && checks.centered_odd && checks.fiber_zero;
}

int collision_transform_prime_window(
    int lower, int upper, int base, int lag,
    const long double *exponents, int exponent_count,
    long double *sums, int *prime_count)
{
    if (!exponents || exponent_count < 1 || !sums || !prime_count ||
        !ctransform_validate(base, lag, 0) || lower < 0 ||
        upper <= lower || upper > CTRANS_MAX_INPUT)
        return 0;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (lower < modulus) return 0;

    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 0;
    unsigned char *composite = ctransform_sieve(upper);
    if (!composite) {
        collision_centered_table_free(&table);
        return 0;
    }

    for (int e = 0; e < exponent_count; e++) sums[e] = 0.0L;
    *prime_count = 0;
    for (int p = lower + 1; p <= upper; p++) {
        if (composite[p] || p <= modulus) continue;
        int residue = p % modulus;
        if (collision_table_gcd(residue, modulus) != 1) continue;
        int fiber = residue % base;
        long double centered =
            (long double)table.centered_numerator[residue] /
            table.fiber_count[fiber];
        for (int e = 0; e < exponent_count; e++)
            sums[e] += centered / powl((long double)p, exponents[e]);
        (*prime_count)++;
    }

    free(composite);
    collision_centered_table_free(&table);
    return 1;
}

int collision_transform_inspect(int n, int base, int lag)
{
    if (!ctransform_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (n <= modulus) {
        fprintf(stderr, "inspection requires n > base^(lag+1) = %d\n",
                modulus);
        return 1;
    }
    if (n > CTRANS_MAX_INPUT) {
        fprintf(stderr, "n must not exceed %d\n", CTRANS_MAX_INPUT);
        return 1;
    }
    if (collision_table_gcd(n, base) != 1) {
        fprintf(stderr, "n must be coprime to the base\n");
        return 1;
    }

    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    int residue = n % modulus;
    int collision = 0, deviation = 0, multiplier = 0;
    long long numerator = 0, denominator = 0;
    int ok = collision_table_direct_deviation(
                 n, base, lag, &collision, &deviation, &multiplier) &&
             deviation == table.value[residue] &&
             collision_centered_table_fraction(
                 &table, residue, &numerator, &denominator);
    int fiber = residue % base;

    printf("Centered collision transform\n\n");
    printf("n = %d; base b = %d; lag ell = %d\n", n, base, lag);
    printf("q = b^(ell+1) = %d; class a = n mod q = %d\n",
           modulus, residue);
    printf("direct multiplier [b^ell]_n = %d\n", multiplier);
    printf("direct collision count C_b,ell(n) = %d\n", collision);
    printf("direct deviation S_b,ell(n) = %+d\n", deviation);
    printf("finite table T_b,ell(a) = %+d  %s\n",
           table.value[residue], ok ? "PASS" : "FAIL");
    printf("reduction fiber a mod b = %d\n", fiber);
    printf("fiber mean mu = %lld/%d\n",
           table.fiber_sum[fiber], table.fiber_count[fiber]);
    printf("centered value f_b,ell(a) = %lld/%lld\n",
           numerator, denominator);
    printf("The input may be prime or composite.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

int collision_transform_table(int base, int lag)
{
    if (!ctransform_validate(base, lag, 1)) return 1;
    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    CTransformChecks checks = ctransform_check_table(&table);

    printf("Centered collision transform\n");
    printf("Complete centered table in base %d at lag %d\n\n", base, lag);
    printf("  a   a mod b   T(a)   fiber mean   f(a)\n");
    for (int a = 1; a < table.modulus; a++) {
        if (collision_table_gcd(a, table.modulus) != 1) continue;
        int fiber = a % base;
        long long numerator = 0, denominator = 0;
        collision_centered_table_fraction(
            &table, a, &numerator, &denominator);
        printf("  %-4d %-9d %+4d   %lld/%d       %+lld/%lld\n",
               a, fiber, table.value[a], table.fiber_sum[fiber],
               table.fiber_count[fiber], numerator, denominator);
    }
    printf("\n%d unit classes; every fiber mean comes from the complete table.\n",
           table.phi);
    printf("Result  %s\n",
           ctransform_checks_pass(checks) ? "PASS" : "FAIL");
    int ok = ctransform_checks_pass(checks);
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

int collision_transform_gate(int base, int lag)
{
    if (!ctransform_validate(base, lag, 1)) return 1;
    CollisionCenteredTable table;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    CTransformChecks checks = ctransform_check_table(&table);
    int ok = ctransform_checks_pass(checks);

    printf("Centered collision transform\n");
    printf("Exact finite character-gate certificate in base %d at lag %d\n\n",
           base, lag);
    printf("  finite reflection T(a)+T(-a)=-1                   %s\n",
           checks.reflection ? "PASS" : "FAIL");
    printf("  exact raw grand mean -1/2                         %s\n",
           checks.raw_mean ? "PASS" : "FAIL");
    printf("  every reduction fiber contains b^ell classes      %s\n",
           checks.fiber_size ? "PASS" : "FAIL");
    printf("  reflected fiber means sum to -1                   %s\n",
           checks.mean_reflection ? "PASS" : "FAIL");
    printf("  centered signal satisfies f(-a)=-f(a)             %s\n",
           checks.centered_odd ? "PASS" : "FAIL");
    printf("  centered sum is zero on every reduction fiber     %s\n",
           checks.fiber_zero ? "PASS" : "FAIL");
    printf("\nOddness kills every even Dirichlet-character coefficient.\n");
    printf("Fiber-zero kills every character descending through the base.\n");
    printf("The principal channel is therefore absent. These conclusions use\n");
    printf("the exact finite identities above, not sampled primes.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

static void ctransform_print_character_label(
    const FiniteCharacterSpectrum *spectrum, int character)
{
    int width = spectrum->factor_count > 0 ? spectrum->factor_count : 1;
    printf("chi[");
    if (spectrum->factor_count == 0) {
        printf("0");
    } else {
        for (int factor = 0; factor < spectrum->factor_count; factor++) {
            if (factor > 0) printf(",");
            printf("%d", spectrum->coordinates[
                (size_t)character * width + factor]);
        }
    }
    printf("]");
}

int collision_transform_spectrum(int base, int lag)
{
    CollisionCenteredTable table = {0};
    FiniteCharacterSpectrum spectrum = {0};
    int ok = 1;
    int active_gate = 1;
    int conductor_ok = 1;

    if (!ctransform_validate(base, lag, 1)) return 1;
    if (!collision_centered_table_build(base, lag, &table)) return 1;
    if (table.modulus > FINITE_CHARACTER_SPECTRUM_MAX_MODULUS) {
        fprintf(stderr,
                "character spectrum requires q <= %d\n",
                FINITE_CHARACTER_SPECTRUM_MAX_MODULUS);
        collision_centered_table_free(&table);
        return 1;
    }
    if (!finite_character_spectrum_compute(&table, &spectrum)) {
        fprintf(stderr, "unable to construct the finite character spectrum\n");
        collision_centered_table_free(&table);
        return 1;
    }

    printf("Centered collision transform\n");
    printf("Finite character spectrum in base %d at lag %d\n\n", base, lag);
    printf("q=%d; phi(q)=%d; character factors",
           table.modulus, table.phi);
    if (spectrum.factor_count == 0) {
        printf(" C1");
    } else {
        for (int factor = 0; factor < spectrum.factor_count; factor++)
            printf(" C%d", spectrum.factor_order[factor]);
    }
    printf("\n");
    printf("Coefficient convention c_chi = phi(q)^-1 sum_a f(a) conjugate(chi(a)).\n");
    printf("Resolved support uses long-double character values and tolerance %.1Le.\n\n",
           spectrum.tolerance);
    printf("  idx  character       parity  descends  conductor  coefficient                    |c|          state\n");
    for (int character = 0; character < spectrum.character_count;
         character++) {
        long double complex coefficient = spectrum.coefficient[character];
        printf("  %3d  ", character);
        ctransform_print_character_label(&spectrum, character);
        printf("%*s  %-4s    %-3s      %-5d      %+.9Le %+.9Lei  %.3Le  %s\n",
               spectrum.factor_count < 3 ? 11 : 5, "",
               spectrum.odd[character] ? "odd" : "even",
               spectrum.base_factored[character] ? "yes" : "no",
               spectrum.conductor[character],
               creall(coefficient), cimagl(coefficient),
               cabsl(coefficient),
               spectrum.resolved_active[character]
                   ? "resolved active" : "zero at tolerance");
        if (spectrum.resolved_active[character] &&
            (!spectrum.odd[character] ||
             spectrum.base_factored[character]))
            active_gate = 0;
        if (spectrum.conductor[character] < 1 ||
            table.modulus % spectrum.conductor[character] != 0 ||
            ((base % spectrum.conductor[character] == 0) !=
             spectrum.base_factored[character]))
            conductor_ok = 0;
    }
    ok = active_gate && conductor_ok &&
         spectrum.maximum_even_coefficient <= spectrum.tolerance &&
         spectrum.maximum_base_factored_coefficient <= spectrum.tolerance &&
         spectrum.inversion_error <= 5.0e-11L &&
         spectrum.parseval_error <= 5.0e-11L &&
         spectrum.conjugate_error <= 5.0e-11L;

    printf("\nSupport and gate\n");
    printf("  resolved active coefficients = %d; zeros at tolerance = %d\n",
           spectrum.resolved_active_count, spectrum.resolved_zero_count);
    printf("  odd non-base-descended sector = %d characters\n",
           spectrum.allowed_count);
    printf("  maximum even coefficient = %.3Le  %s\n",
           spectrum.maximum_even_coefficient,
           spectrum.maximum_even_coefficient <= spectrum.tolerance
               ? "PASS" : "FAIL");
    printf("  maximum base-descended coefficient = %.3Le  %s\n",
           spectrum.maximum_base_factored_coefficient,
           spectrum.maximum_base_factored_coefficient <= spectrum.tolerance
               ? "PASS" : "FAIL");
    printf("  every resolved active channel passes the finite gate  %s\n",
           active_gate ? "PASS" : "FAIL");
    printf("  primitive-ancestor conductor assigned to every channel %s\n",
           conductor_ok ? "PASS" : "FAIL");
    if (lag == 1 && finite_character_is_prime(base))
        printf("  prime-base active sector is primitive and odd         %s\n",
               active_gate ? "PASS" : "FAIL");
    printf("\nTransform identities\n");
    printf("  inverse reconstruction error = %.3Le  %s\n",
           spectrum.inversion_error,
           spectrum.inversion_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("  Parseval error = %.3Le  %s\n", spectrum.parseval_error,
           spectrum.parseval_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("  conjugate-coefficient error = %.3Le  %s\n",
           spectrum.conjugate_error,
           spectrum.conjugate_error <= 5.0e-11L ? "PASS" : "FAIL");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");

    finite_character_spectrum_free(&spectrum);
    collision_centered_table_free(&table);
    return ok ? 0 : 1;
}

int collision_transform_window(int lower, int upper, int base, int lag,
                               long double sigma)
{
    if (!ctransform_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (lower < modulus || upper <= lower || upper > CTRANS_MAX_INPUT) {
        fprintf(stderr,
                "window must satisfy q <= lower < upper <= %d\n",
                CTRANS_MAX_INPUT);
        return 1;
    }
    if (!(sigma > 0.0L)) {
        fprintf(stderr, "sigma must be positive\n");
        return 1;
    }
    long double sum = 0.0L;
    int prime_count = 0;
    if (!collision_transform_prime_window(
            lower, upper, base, lag, &sigma, 1, &sum, &prime_count))
        return 1;
    printf("Centered collision transform\n");
    printf("Declared finite prime window\n\n");
    printf("base=%d; lag=%d; q=%d; %d < p <= %d\n",
           base, lag, modulus, lower, upper);
    printf("included primes = %d\n", prime_count);
    printf("sigma = %.6Lf\n", sigma);
    printf("window contribution = %+.12Lf\n", sum);
    printf("This is one finite window, not a value assigned to an infinite series.\n");
    printf("Result  PASS\n");
    return 0;
}

static int ctransform_snapshot_ok(int print)
{
    long double observed[CTRANS_BASES][CTRANS_EXPONENTS];
    int counts[CTRANS_BASES];
    int ok = 1;
    for (int b = 0; b < CTRANS_BASES; b++) {
        if (!collision_transform_prime_window(
                1000000, 10000000, ctransform_snapshot_bases[b], 1,
                ctransform_snapshot_exponents, CTRANS_EXPONENTS,
                observed[b], &counts[b]))
            return 0;
        if (counts[b] != 586081) ok = 0;
    }

    if (print) {
        printf("Centered collision transform\n");
        printf("Reference terminal window; 1000000 < p <= 10000000\n\n");
        printf("  s       base 3      base 5      base 7      base 10     base 12\n");
    }
    for (int e = 0; e < CTRANS_EXPONENTS; e++) {
        if (print) printf("  %.1Lf", ctransform_snapshot_exponents[e]);
        for (int b = 0; b < CTRANS_BASES; b++) {
            int row_ok = fabsl(observed[b][e] -
                               ctransform_snapshot_expected[e][b]) < 5.1e-7L;
            if (!row_ok) ok = 0;
            if (print) printf("  %+.6Lf", observed[b][e]);
        }
        if (print) printf("\n");
    }
    if (print) {
        printf("\nAll bases include 586081 primes in the declared window.\n");
        printf("6/6 reference exponent rows reproduced to displayed precision.\n");
        printf("Finite windows do not prove convergence below one or on the critical line.\n");
        printf("Result  %s\n", ok ? "PASS" : "FAIL");
    }
    return ok;
}

int collision_transform_snapshot(void)
{
    return ctransform_snapshot_ok(1) ? 0 : 1;
}

int collision_transform_examples(void)
{
    CollisionCenteredTable table;
    if (!collision_centered_table_build(10, 1, &table)) return 1;
    long long numerator = 0, denominator = 0;
    int centered = collision_centered_table_fraction(
        &table, 91, &numerator, &denominator) &&
        table.value[91] == -9 && numerator == -73 && denominator == 10;
    CTransformChecks checks = ctransform_check_table(&table);
    int gate = ctransform_checks_pass(checks);
    int collision = 0, deviation = 0, multiplier = 0;
    int finite = collision_table_direct_deviation(
        191, 10, 1, &collision, &deviation, &multiplier) &&
        collision == 10 && deviation == -9 && multiplier == 10;
    printf("Centered collision transform\n");
    printf("Named exact finite examples\n\n");
    printf("  decimal class 91 has T=-9 and f=-73/10          %s\n",
           centered ? "PASS" : "FAIL");
    printf("  n=191 directly realizes class 91 and T=-9       %s\n",
           finite ? "PASS" : "FAIL");
    printf("  complete decimal centered table passes the gate %s\n",
           gate ? "PASS" : "FAIL");
    printf("Result  %s\n", centered && finite && gate ? "PASS" : "FAIL");
    collision_centered_table_free(&table);
    return centered && finite && gate ? 0 : 1;
}

static void ctransform_report(const char *label, int ok, int *passed)
{
    printf("  %-66s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int collision_transform_verify(void)
{
    int finite = 1, reflection = 1, raw_mean = 1, fiber_size = 1;
    int mean_reflection = 1, centered_odd = 1, fiber_zero = 1;
    int direct = 1, tables = 0, unit_classes = 0, direct_checks = 0;
    int character_groups = 1, transform_inversion = 1, transform_gate = 1;
    int transform_identities = 1, transformed_classes = 0;

    for (int i = 0; i < CTRANS_BASES; i++) {
        int base = ctransform_snapshot_bases[i];
        CollisionCenteredTable table = {0};
        FiniteCharacterSpectrum spectrum = {0};
        if (!collision_centered_table_build(base, 1, &table)) {
            finite = 0;
            continue;
        }
        CTransformChecks checks = ctransform_check_table(&table);
        reflection &= checks.reflection;
        raw_mean &= checks.raw_mean;
        fiber_size &= checks.fiber_size;
        mean_reflection &= checks.mean_reflection;
        centered_odd &= checks.centered_odd;
        fiber_zero &= checks.fiber_zero;
        if (!finite_character_spectrum_compute(&table, &spectrum)) {
            character_groups = 0;
            transform_inversion = 0;
            transform_gate = 0;
            transform_identities = 0;
        } else {
            character_groups &=
                spectrum.character_count == table.phi &&
                spectrum.even_count == table.phi / 2 &&
                spectrum.base_factored_count ==
                    table.phi / table.fiber_size;
            transform_inversion &= spectrum.inversion_error <= 5.0e-11L;
            transform_gate &=
                spectrum.maximum_even_coefficient <= spectrum.tolerance &&
                spectrum.maximum_base_factored_coefficient <=
                    spectrum.tolerance;
            transform_identities &=
                spectrum.parseval_error <= 5.0e-11L &&
                spectrum.conjugate_error <= 5.0e-11L;
            for (int character = 0;
                 character < spectrum.character_count; character++) {
                if (spectrum.conductor[character] < 1 ||
                    table.modulus % spectrum.conductor[character] != 0 ||
                    ((base % spectrum.conductor[character] == 0) !=
                     spectrum.base_factored[character]))
                    character_groups = 0;
                if (spectrum.resolved_active[character] &&
                    (!spectrum.odd[character] ||
                     spectrum.base_factored[character]))
                    transform_gate = 0;
            }
            if (finite_character_is_prime(base)) {
                int expected_primitive_odd =
                    (base - 1) * (base - 1) / 2;
                if (spectrum.allowed_count != expected_primitive_odd)
                    transform_gate = 0;
            }
            transformed_classes += spectrum.character_count;
        }
        for (int a = 1; a < table.modulus; a++) {
            if (collision_table_gcd(a, table.modulus) != 1) continue;
            for (int multiple = 1; multiple <= 3; multiple++) {
                int n = multiple * table.modulus + a;
                int collision = 0, deviation = 0, multiplier = 0;
                if (!collision_table_direct_deviation(
                        n, base, 1, &collision, &deviation, &multiplier) ||
                    deviation != table.value[a])
                    direct = 0;
                direct_checks++;
            }
        }
        tables++;
        unit_classes += table.phi;
        finite_character_spectrum_free(&spectrum);
        collision_centered_table_free(&table);
    }

    int examples = collision_transform_examples() == 0;
    int snapshot = ctransform_snapshot_ok(0);
    int passed = 0;
    printf("\nFinite C verification of the centered collision transform\n");
    printf("Exact lag-one tables: %d selected bases and %d unit classes.\n",
           tables, unit_classes);
    printf("Finite transforms: %d character coefficients on those same classes.\n",
           transformed_classes);
    printf("Direct comparison: %d checks using three representatives per class.\n\n",
           direct_checks);
    ctransform_report("finite floor table constructed on every unit class",
                      finite, &passed);
    ctransform_report("all 468 direct collision counts equal the finite table",
                      direct && direct_checks == 468, &passed);
    ctransform_report("raw reflection and exact grand mean -1/2",
                      reflection && raw_mean, &passed);
    ctransform_report("every reduction fiber has the exact size b^ell",
                      fiber_size, &passed);
    ctransform_report("reflected fiber means sum to -1", mean_reflection,
                      &passed);
    ctransform_report("centered signal is exactly odd", centered_odd, &passed);
    ctransform_report("every centered reduction-fiber sum is zero", fiber_zero,
                      &passed);
    ctransform_report("complete finite character groups on all 156 unit classes",
                      character_groups && transformed_classes == 156, &passed);
    ctransform_report("normalized Fourier inversion reconstructs every class",
                      transform_inversion, &passed);
    ctransform_report("even and base-descended coefficients pass the exact gate",
                      transform_gate, &passed);
    ctransform_report("Parseval and conjugate coefficients agree",
                      transform_identities, &passed);
    ctransform_report("named decimal finite examples", examples, &passed);
    ctransform_report("all six reference terminal-window rows", snapshot,
                      &passed);
    printf("\n%d/13 verification groups passed.\n", passed);
    printf("The finite arithmetic and displayed prime windows are reproducible.\n");
    printf("Zero-free penetration and the zero-cancellation obstruction belong\n");
    printf("to the external analytic layer beyond this finite verifier.\n");
    return passed == 13;
}

void collision_transform_help(void)
{
    printf(
        "Centered collision transform and prime windows\n\n"
        "Build the exact finite table, center every reduction fiber, inspect\n"
        "its surviving character support, and evaluate declared prime windows.\n\n"
        "Usage:\n"
        "  nfield collision-transform inspect <n> [--base <b>] [--lag <ell>]\n"
        "  nfield collision-transform table [--base <b>] [--lag <ell>]\n"
        "  nfield collision-transform gate [--base <b>] [--lag <ell>]\n"
        "  nfield collision-transform spectrum [--base <b>] [--lag <ell>]\n"
        "  nfield collision-transform window <low> <high> [--base <b>]\n"
        "       [--lag <ell>] [--sigma <real>]\n"
        "  nfield collision-transform snapshot\n"
        "  nfield collision-transform examples\n"
        "  nfield collision-transform verify\n"
        "  nfield verify collision-transform\n\n"
        "inspect checks one direct collision count against the exact finite table\n"
        "and prints its fixed fiber-centered value. The input may be prime or\n"
        "composite. table exposes every unit class. gate verifies reflection,\n"
        "oddness, and zero fiber sums exactly; these are the two mechanisms that\n"
        "remove even characters and characters descending through the base.\n"
        "spectrum computes every normalized coefficient, its primitive-ancestor\n"
        "conductor, and the support resolved at tolerance 1e-11. It checks\n"
        "inversion, Parseval, conjugate pairing, and the exact gate. Character\n"
        "spectra require q<=4096.\n\n"
        "window evaluates one declared finite prime interval. snapshot reproduces\n"
        "the reference five-base terminal window at all six exponents. The\n"
        "verifier checks exactly 468 direct representatives, all 156 character\n"
        "coefficients in the five reference bases, and every displayed window\n"
        "row. Tables are limited to q<=50000 and windows to ten million.\n\n"
        "Proof boundary\n"
        "  exact finite arithmetic  tables, fibers, reflection, and gate\n"
        "  finite numerical         character coefficients at printed tolerance\n"
        "  bounded computation      declared prime windows through ten million\n"
        "  external analysis        zero-free penetration, continuation, and\n"
        "                           the zero-cancellation obstruction\n"
    );
}
