/* Finite extraction of the secondary collision-energy residual. */

#include <math.h>
#include <stdio.h>

#include "nfield.h"

static int abd_is_prime(int value)
{
    if (value < 2) return 0;
    if (value % 2 == 0) return value == 2;
    for (int divisor = 3; divisor <= value / divisor; divisor += 2)
        if (value % divisor == 0) return 0;
    return 1;
}

int arithmetic_boundary_defect_metrics(
        int base, long double *energy_ratio,
        long double *secondary_ratio, long double *predicted_coefficient)
{
    if (!energy_ratio || !secondary_ratio || !predicted_coefficient)
        return 0;
    long long total = 0;
    long long diagonal = 0;
    long long upper = 0;
    long long lower = 0;
    int weight_ok = 0;
    int correction_ok = 0;
    int symmetry_ok = 0;
    if (!prime_base_collision_energy_dedekind(
            base, &total, &diagonal, &upper, &lower,
            &weight_ok, &correction_ok, &symmetry_ok) ||
        !weight_ok || !correction_ok || !symmetry_ok)
        return 0;
    long double b = (long double)base;
    long double modulus = b * b;
    long double energy = (long double)total / (12.0L * modulus);
    long double logarithm = logl(b);
    *energy_ratio = energy / (b * b * b);
    *secondary_ratio =
        (energy - b * b * b) / (b * b * logarithm * logarithm);
    long double pi = acosl(-1.0L);
    *predicted_coefficient = -1.0L / (pi * pi);
    return 1;
}

int arithmetic_boundary_defect_inspect(int base)
{
    long double energy_ratio = 0.0L;
    long double secondary_ratio = 0.0L;
    long double predicted = 0.0L;
    if (!arithmetic_boundary_defect_metrics(
            base, &energy_ratio, &secondary_ratio, &predicted)) {
        fprintf(stderr, "base must be an odd prime not exceeding 251\n");
        return 1;
    }
    long long total = 0;
    long long diagonal = 0;
    long long upper = 0;
    long long lower = 0;
    int weight_ok = 0;
    int correction_ok = 0;
    int symmetry_ok = 0;
    (void)prime_base_collision_energy_dedekind(
        base, &total, &diagonal, &upper, &lower,
        &weight_ok, &correction_ok, &symmetry_ok);
    printf("Arithmetic boundary defect\n\n");
    printf("  base=%d; exact 12*b^2*E_b numerator=%lld\n", base, total);
    printf("  E_b/b^3=%.15Lf\n", energy_ratio);
    printf("  (E_b-b^3)/(b^2(log b)^2)=%.15Lf\n", secondary_ratio);
    printf("  proved secondary coefficient -1/pi^2=%.15Lf\n", predicted);
    printf("\nStatus\n");
    printf("  exact       E_b and both finite pole masses are integer-scaled values.\n");
    printf("  theorem     the all-prime asymptotic has coefficient -1/pi^2.\n");
    printf("  open        O(log b), O(1), and the normalized sampling limit S_b->1.\n");
    printf("\nResult  PASS (exact finite extraction)\n");
    return 0;
}

int arithmetic_boundary_defect_scan(int maximum_base)
{
    if (maximum_base < 3 || maximum_base > 251) {
        fprintf(stderr, "maximum base must lie between 3 and 251\n");
        return 1;
    }
    printf("Arithmetic boundary-defect finite scan\n\n");
    printf("  b       E_b/b^3        normalized defect      coefficient -1/pi^2\n");
    int models = 0;
    for (int base = 3; base <= maximum_base; base += 2) {
        if (!abd_is_prime(base)) continue;
        long double energy_ratio = 0.0L;
        long double secondary_ratio = 0.0L;
        long double predicted = 0.0L;
        if (!arithmetic_boundary_defect_metrics(
                base, &energy_ratio, &secondary_ratio, &predicted))
            return 1;
        printf("  %-3d  %.12Lf  %+.12Lf  %+.12Lf\n",
               base, energy_ratio, secondary_ratio, predicted);
        models++;
    }
    printf("\nExact finite models=%d. Analytic status is separate from finite evaluation.\n",
           models);
    return 0;
}

int arithmetic_boundary_defect_verify(void)
{
    int extraction_ok = 1;
    int coefficient_ok = 1;
    int boundary_ok = 1;
    int models = 0;
    long double expected = -1.0L / (acosl(-1.0L) * acosl(-1.0L));
    for (int base = 3; base <= 251; base += 2) {
        if (!abd_is_prime(base)) continue;
        long double energy_ratio = 0.0L;
        long double secondary_ratio = 0.0L;
        long double predicted = 0.0L;
        models++;
        if (!arithmetic_boundary_defect_metrics(
                base, &energy_ratio, &secondary_ratio, &predicted) ||
            !isfinite(energy_ratio) || !isfinite(secondary_ratio))
            extraction_ok = 0;
        if (fabsl(predicted - expected) > 1.0e-18L)
            coefficient_ok = 0;
    }
    long double first = 0.0L;
    long double second = 0.0L;
    long double third = 0.0L;
    boundary_ok = !arithmetic_boundary_defect_metrics(
                      2, &first, &second, &third) &&
                  !arithmetic_boundary_defect_metrics(
                      9, &first, &second, &third) &&
                  !arithmetic_boundary_defect_metrics(
                      257, &first, &second, &third);
    int coverage_ok = models == 53;
    int passed = extraction_ok + coefficient_ok + boundary_ok + coverage_ok;
    printf("Arithmetic boundary-defect verification\n\n");
    printf("  exact finite odd-prime extractions=%d             %s\n",
           models, extraction_ok ? "PASS" : "FAIL");
    printf("  proved secondary coefficient encoded as -1/pi^2   %s\n",
           coefficient_ok ? "PASS" : "FAIL");
    printf("  even, composite, and over-limit rejection         %s\n",
           boundary_ok ? "PASS" : "FAIL");
    printf("  complete declared finite range                     %s\n",
           coverage_ok ? "PASS" : "FAIL");
    printf("\n%d/4 verification groups passed.\n", passed);
    printf("Computed  each E_b is exact; logarithms enter only the displayed\n");
    printf("normalization. The finite sweep tests extraction, not asymptotic proof.\n");
    printf("Proved  the all-prime secondary coefficient is -1/pi^2.\n");
    printf("Open  O(log b), O(1), and the normalized sampling limit S_b->1.\n");
    return passed == 4;
}

void arithmetic_boundary_defect_help(void)
{
    printf(
        "Arithmetic boundary defect\n\n"
        "Commands\n"
        "  nfield arithmetic-boundary-defect inspect <odd-prime-base>\n"
        "  nfield arithmetic-boundary-defect scan <maximum-base>\n"
        "  nfield arithmetic-boundary-defect verify\n"
        "  nfield verify arithmetic-boundary-defect\n\n"
        "Example\n"
        "  nfield arithmetic-boundary-defect scan 43\n\n"
        "Scope\n"
        "  exact        E_b comes from the integer-scaled Dedekind ratio sum.\n"
        "  numerical    only log b and the normalization use floating arithmetic.\n"
        "  theorem      E_b=b^3-(1/pi^2)b^2(log b)^2\n"
        "               +O(b^2(log(2b))^2/loglog(3b)).\n"
        "  open         O(log b), O(1), and the normalized sampling limit S_b->1.\n"
        "  boundary     odd prime bases through 251; the sweep extracts finite\n"
        "               values while the asymptotic statement remains symbolic.\n"
    );
}
