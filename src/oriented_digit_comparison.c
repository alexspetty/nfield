/* Exact response of the oriented two-digit comparison source. */

#include <limits.h>
#include <stdio.h>

#include "nfield.h"

static int odc_gcd(int a, int b)
{
    while (b != 0) {
        int remainder = a % b;
        a = b;
        b = remainder;
    }
    return a < 0 ? -a : a;
}

static int odc_is_prime(int value)
{
    if (value < 2) return 0;
    if (value % 2 == 0) return value == 2;
    for (int divisor = 3; divisor <= value / divisor; divisor += 2)
        if (value % divisor == 0) return 0;
    return 1;
}

static int odc_weight(int base, int cell)
{
    int first = cell / base;
    int second = cell % base;
    return (first > second) - (first < second);
}

static int odc_boundary(int base, int cell)
{
    int modulus = base * base;
    int previous = cell == 0 ? modulus - 1 : cell - 1;
    return odc_weight(base, previous) - odc_weight(base, cell);
}

static int odc_ceiling_quotient(long long numerator, int denominator)
{
    return numerator == 0 ? 0 : 1 + (numerator - 1) / denominator;
}

int oriented_digit_comparison_response_direct(int base, int phase,
                                               int *response)
{
    if (!response || base < 2 || base > 1000 ||
        base > INT_MAX / base)
        return 0;
    int modulus = base * base;
    if (phase < 0 || phase >= modulus) return 0;

    int total = 0;
    for (int cell = 0; cell < modulus; cell++) {
        int upper = odc_ceiling_quotient(
            (long long)(cell + 1) * phase, modulus);
        int lower = odc_ceiling_quotient(
            (long long)cell * phase, modulus);
        total += odc_weight(base, cell) * (upper - lower);
    }
    *response = total;
    return 1;
}

int oriented_digit_comparison_response_formula(int base, int phase,
                                                int *response)
{
    if (!response || base < 2 || base > 1000 ||
        base > INT_MAX / base)
        return 0;
    int modulus = base * base;
    if (phase < 0 || phase >= modulus) return 0;
    int divisor = odc_gcd(phase, modulus);
    *response = odc_gcd(divisor, base) -
                (divisor + base - 1) / base;
    return 1;
}

int oriented_digit_comparison_boundary_norm(int base, int *norm_squared)
{
    if (!norm_squared || base < 2 || base > 1000 ||
        base > INT_MAX / base)
        return 0;
    int modulus = base * base;
    int total = 0;
    for (int cell = 0; cell < modulus; cell++) {
        int boundary = odc_boundary(base, cell);
        total += boundary * boundary;
    }
    *norm_squared = total;
    return 1;
}

int oriented_digit_comparison_intrinsic_count(int denominator, int base,
                                               long long *count)
{
    if (!count || denominator < 1 || base < 2 || base > 1000 ||
        base > INT_MAX / base)
        return 0;
    int modulus = base * base;
    long long total = 0;
    for (int numerator = 1; numerator < denominator; numerator++) {
        int cell = (int)(((long long)modulus * numerator) / denominator);
        total += odc_weight(base, cell);
    }
    *count = total;
    return 1;
}

static int odc_trichotomy_direct(int denominator, int base,
                                 long long *ascents,
                                 long long *equalities,
                                 long long *descents)
{
    if (!ascents || !equalities || !descents || denominator < 1 ||
        base < 2 || base > 1000 || base > INT_MAX / base)
        return 0;

    int modulus = base * base;
    long long a = 0;
    long long e = 0;
    long long d = 0;
    for (int numerator = 1; numerator < denominator; numerator++) {
        int cell = (int)(((long long)modulus * numerator) / denominator);
        int first = cell / base;
        int second = cell % base;
        if (first < second) a++;
        else if (first == second) e++;
        else d++;
    }
    *ascents = a;
    *equalities = e;
    *descents = d;
    return 1;
}

static void odc_prime_row_trichotomy_formula(int prime, int row_index,
                                             int height,
                                             long long *ascents,
                                             long long *equalities,
                                             long long *descents)
{
    long long bulk_side =
        (long long)height * prime * (prime - 1) / 2;
    *ascents = bulk_side +
        (long long)(prime - 1) * (row_index - 1) / 2;
    *equalities = (long long)height * prime + row_index - 1;
    *descents = bulk_side +
        (long long)(prime - 1) * (row_index + 1) / 2;
}

int oriented_digit_comparison_trichotomy(int prime, int row_index,
                                          int height)
{
    if (!odc_is_prime(prime) || prime < 3 || prime > 997) {
        fprintf(stderr, "prime must be an odd prime not exceeding 997\n");
        return 1;
    }
    if (row_index < 1 || row_index >= prime) {
        fprintf(stderr, "row index must be in 1..p-1\n");
        return 1;
    }
    if (height < 0 || height > 8) {
        fprintf(stderr, "height must be in 0..8\n");
        return 1;
    }

    long long denominator64 =
        (long long)height * prime * prime + (long long)prime * row_index;
    if (denominator64 > INT_MAX) {
        fprintf(stderr, "denominator exceeds the exact direct-count domain\n");
        return 1;
    }
    int denominator = (int)denominator64;
    long long ascents = 0;
    long long equalities = 0;
    long long descents = 0;
    long long expected_ascents = 0;
    long long expected_equalities = 0;
    long long expected_descents = 0;
    odc_trichotomy_direct(denominator, prime,
                          &ascents, &equalities, &descents);
    odc_prime_row_trichotomy_formula(
        prime, row_index, height,
        &expected_ascents, &expected_equalities, &expected_descents);

    long long mass = ascents + equalities + descents;
    long long orientation = descents - ascents;
    long long synthesized_ascents =
        (mass - equalities - orientation) / 2;
    long long synthesized_descents =
        (mass - equalities + orientation) / 2;
    int ok = ascents == expected_ascents &&
             equalities == expected_equalities &&
             descents == expected_descents &&
             mass == denominator - 1 &&
             orientation == prime - 1 &&
             synthesized_ascents == ascents &&
             synthesized_descents == descents;

    printf("Prime-square comparison trichotomy\n\n");
    printf("  prime=%d row-index=%d height=%d denominator=%d\n",
           prime, row_index, height, denominator);
    printf("  direct ascents=%lld equalities=%lld descents=%lld\n",
           ascents, equalities, descents);
    printf("  closed ascents=%lld equalities=%lld descents=%lld  %s\n",
           expected_ascents, expected_equalities, expected_descents,
           ascents == expected_ascents &&
           equalities == expected_equalities &&
           descents == expected_descents ? "PASS" : "FAIL");
    printf("  analysis mass=%lld collision=%lld orientation=%lld\n",
           mass, equalities, orientation);
    printf("  synthesis ascents=%lld equalities=%lld descents=%lld  %s\n",
           synthesized_ascents, equalities, synthesized_descents,
           synthesized_ascents == ascents &&
           synthesized_descents == descents ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int oriented_digit_comparison_inspect(int base, int phase)
{
    int direct = 0;
    int formula = 0;
    int norm_squared = 0;
    if (!oriented_digit_comparison_response_direct(base, phase, &direct) ||
        !oriented_digit_comparison_response_formula(base, phase, &formula) ||
        !oriented_digit_comparison_boundary_norm(base, &norm_squared)) {
        fprintf(stderr, "base must be in 2..1000 and phase in 0..b^2-1\n");
        return 1;
    }

    int modulus = base * base;
    int divisor = odc_gcd(phase, modulus);
    int unit = divisor == 1;
    int ramified = divisor > 1 && divisor < modulus;
    int ok = direct == formula && norm_squared == 6 * (base - 1) &&
             ((unit && direct == 0) ||
              (ramified && direct > 0) ||
              (phase == 0 && direct == 0));

    printf("Oriented two-digit comparison\n\n");
    printf("  base=%d carrier=b^2=%d phase=%d gcd=%d\n",
           base, modulus, phase, divisor);
    printf("  source sign(first digit - second digit)\n");
    printf("  direct ceiling response=%d\n", direct);
    printf("  divisor formula gcd(d,b)-ceil(d/b)=%d  %s\n",
           formula, direct == formula ? "PASS" : "FAIL");
    printf("  phase class=%s\n",
           unit ? "unit: silent" :
           ramified ? "proper nonunit: active" : "zero: silent");
    printf("  cyclic boundary squared norm=%d; expected=%d  %s\n",
           norm_squared, 6 * (base - 1),
           norm_squared == 6 * (base - 1) ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int oriented_digit_comparison_prime(int prime)
{
    if (!odc_is_prime(prime) || prime < 3 || prime > 997) {
        fprintf(stderr, "prime must be an odd prime not exceeding 997\n");
        return 1;
    }
    int modulus = prime * prime;
    long long energy = 0;
    int failures = 0;
    int active = 0;
    for (int phase = 1; phase < modulus; phase++) {
        int response = 0;
        oriented_digit_comparison_response_direct(prime, phase, &response);
        energy += (long long)response * response;
        if (phase % prime == 0) {
            active++;
            if (response != prime - 1) failures++;
        } else if (response != 0) {
            failures++;
        }
    }
    long long expected_energy =
        (long long)(prime - 1) * (prime - 1) * (prime - 1);
    int ok = failures == 0 && active == prime - 1 &&
             energy == expected_energy;

    printf("Prime-square oriented comparison\n\n");
    printf("  prime=%d carrier=%d\n", prime, modulus);
    printf("  unit phases=%d; response=0\n", prime * (prime - 1));
    printf("  nonzero ramified phases=%d; response=%d\n",
           active, prime - 1);
    printf("  zero phase response=0\n");
    printf("  full nonzero-phase energy=%lld; expected (p-1)^3=%lld  %s\n",
           energy, expected_energy,
           energy == expected_energy ? "PASS" : "FAIL");
    printf("  unit-sector reconstruction obstruction=exact silence\n");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int oriented_digit_comparison_verify(void)
{
    int formula_models = 0;
    int formula_failures = 0;
    int classification_failures = 0;
    for (int base = 2; base <= 48; base++) {
        int modulus = base * base;
        for (int phase = 0; phase < modulus; phase++) {
            int direct = 0;
            int formula = 0;
            int divisor = odc_gcd(phase, modulus);
            formula_models++;
            if (!oriented_digit_comparison_response_direct(
                    base, phase, &direct) ||
                !oriented_digit_comparison_response_formula(
                    base, phase, &formula) || direct != formula)
                formula_failures++;
            if ((divisor == 1 && direct != 0) ||
                (divisor > 1 && divisor < modulus && direct <= 0) ||
                (phase == 0 && direct != 0))
                classification_failures++;
        }
    }

    int boundary_models = 0;
    int boundary_failures = 0;
    for (int base = 2; base <= 500; base++) {
        int norm_squared = 0;
        int modulus = base * base;
        int support = 0;
        int total = 0;
        boundary_models++;
        if (!oriented_digit_comparison_boundary_norm(base, &norm_squared) ||
            norm_squared != 6 * (base - 1))
            boundary_failures++;
        for (int cell = 0; cell < modulus; cell++) {
            int boundary = odc_boundary(base, cell);
            total += boundary;
            support += boundary != 0;
            if (boundary != 0 && boundary != 1 && boundary != -2)
                boundary_failures++;
        }
        if (total != 0 || support != 3 * (base - 1))
            boundary_failures++;
    }

    int intrinsic_models = 0;
    int intrinsic_failures = 0;
    for (int base = 2; base <= 24; base++) {
        int modulus = base * base;
        for (int height = 0; height <= 3; height++) {
            for (int phase = 0; phase < modulus; phase++) {
                int denominator = height * modulus + phase;
                int formula = 0;
                long long intrinsic = 0;
                if (denominator == 0) continue;
                intrinsic_models++;
                oriented_digit_comparison_response_formula(
                    base, phase, &formula);
                if (!oriented_digit_comparison_intrinsic_count(
                        denominator, base, &intrinsic) ||
                    intrinsic != formula)
                    intrinsic_failures++;
            }
        }
    }

    int prime_models = 0;
    int prime_failures = 0;
    for (int prime = 3; prime <= 251; prime += 2) {
        if (!odc_is_prime(prime)) continue;
        int modulus = prime * prime;
        long long energy = 0;
        prime_models++;
        for (int phase = 1; phase < modulus; phase++) {
            int response = 0;
            oriented_digit_comparison_response_formula(
                prime, phase, &response);
            energy += (long long)response * response;
            if ((phase % prime == 0 && response != prime - 1) ||
                (phase % prime != 0 && response != 0))
                prime_failures++;
        }
        if (energy != (long long)(prime - 1) * (prime - 1) *
                      (prime - 1))
            prime_failures++;
    }

    int trichotomy_models = 0;
    int trichotomy_failures = 0;
    for (int prime = 3; prime <= 97; prime += 2) {
        if (!odc_is_prime(prime)) continue;
        for (int row_index = 1; row_index < prime; row_index++) {
            for (int height = 0; height <= 3; height++) {
                int denominator =
                    height * prime * prime + prime * row_index;
                long long ascents = 0;
                long long equalities = 0;
                long long descents = 0;
                long long expected_ascents = 0;
                long long expected_equalities = 0;
                long long expected_descents = 0;
                trichotomy_models++;
                odc_trichotomy_direct(
                    denominator, prime, &ascents, &equalities, &descents);
                odc_prime_row_trichotomy_formula(
                    prime, row_index, height,
                    &expected_ascents, &expected_equalities,
                    &expected_descents);
                long long mass = ascents + equalities + descents;
                long long orientation = descents - ascents;
                if (ascents != expected_ascents ||
                    equalities != expected_equalities ||
                    descents != expected_descents ||
                    mass != denominator - 1 ||
                    orientation != prime - 1 ||
                    (mass - equalities - orientation) / 2 != ascents ||
                    (mass - equalities + orientation) / 2 != descents)
                    trichotomy_failures++;
            }
        }
    }

    int domain_ok =
        !oriented_digit_comparison_response_direct(1, 0, &(int){0}) &&
        !oriented_digit_comparison_response_formula(3, 9, &(int){0}) &&
        !oriented_digit_comparison_intrinsic_count(0, 3, &(long long){0});
    int passed = (formula_failures == 0) +
                 (classification_failures == 0) +
                 (boundary_failures == 0) +
                 (intrinsic_failures == 0) +
                 (prime_failures == 0) + domain_ok;
    passed += trichotomy_failures == 0;

    printf("Oriented two-digit comparison verification\n\n");
    printf("  direct all-phase formula models=%d                 %s\n",
           formula_models, formula_failures == 0 ? "PASS" : "FAIL");
    printf("  units silent; proper nonunits active; zero silent %s\n",
           classification_failures == 0 ? "PASS" : "FAIL");
    printf("  boundary support/norm bases 2..500=%d              %s\n",
           boundary_models, boundary_failures == 0 ? "PASS" : "FAIL");
    printf("  all-denominator intrinsic models=%d                %s\n",
           intrinsic_models, intrinsic_failures == 0 ? "PASS" : "FAIL");
    printf("  odd-prime square/energy models=%d                   %s\n",
           prime_models, prime_failures == 0 ? "PASS" : "FAIL");
    printf("  prime-row trichotomy models=%d                     %s\n",
           trichotomy_models,
           trichotomy_failures == 0 ? "PASS" : "FAIL");
    printf("  invalid domains rejected                            %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("\n%d/7 verification groups passed.\n", passed);
    printf("Finite boundary  exact integer arithmetic; direct response bases 2..48,\n");
    printf("boundary bases 2..500, and odd-prime square laws through 251.\n");
    return passed == 7;
}

void oriented_digit_comparison_help(void)
{
    printf(
        "Oriented two-digit comparison\n\n"
        "Usage:\n"
        "  nfield oriented-digit-comparison inspect <base> <phase>\n"
        "  nfield oriented-digit-comparison prime <odd-prime>\n"
        "  nfield oriented-digit-comparison trichotomy <odd-prime> <row-index> [--height H]\n"
        "  nfield oriented-digit-comparison verify\n"
        "  nfield verify oriented-digit-comparison\n\n"
        "The source is sign(first digit - second digit) on the b^2 word\n"
        "carrier. Its intrinsic all-denominator response is zero on unit\n"
        "phases and positive on every proper nonunit phase. At a prime square\n"
        "it is the exact scalar detector of the nonzero ramified row and has\n"
        "energy (p-1)^3. The trichotomy action reconstructs the aggregate\n"
        "ascent/equality/descent counts from mass, collision, and orientation.\n"
        "The verifier uses exact integer arithmetic.\n");
}
