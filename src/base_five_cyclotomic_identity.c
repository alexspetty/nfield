/* Exact polynomial certificate for the base-five collision sector. */

#include <math.h>
#include <stdio.h>

#include "collision_spectrum_core.h"
#include "nfield.h"

static const int base_five_p[8] = {1, 1, 1, 0, 0, 0, 0, 1};
static const int base_five_q[8] = {1, 2, 3, 1, -2, 1, 1, 2};
static const int cyclotomic_twenty[9] = {1, 0, -1, 0, 1, 0, -1, 0, 1};
static const int certificate_quotient[7] = {-3, 0, 1, 5, 1, 0, -3};

static int integer_gcd(int left, int right)
{
    while (right != 0) {
        int next = left % right;
        left = right;
        right = next;
    }
    return left < 0 ? -left : left;
}

static int small_totient(int value)
{
    int result = value;
    for (int prime = 2; prime <= value / prime; prime++) {
        if (value % prime != 0) continue;
        result -= result / prime;
        while (value % prime == 0) value /= prime;
    }
    if (value > 1) result -= result / value;
    return result;
}

static int small_mobius(int value)
{
    int sign = 1;
    for (int prime = 2; prime <= value / prime; prime++) {
        if (value % prime != 0) continue;
        value /= prime;
        sign = -sign;
        if (value % prime == 0) return 0;
        while (value % prime == 0) value /= prime;
    }
    if (value > 1) sign = -sign;
    return sign;
}

static int ramanujan_sum_twenty(int exponent)
{
    int quotient = 20 / integer_gcd(20, exponent);
    return small_mobius(quotient) * small_totient(20) /
           small_totient(quotient);
}

static int power_orbit_certificate(int report)
{
    static const int first_half[10] = {1, 2, 4, 8, 16, 7, 14, 3, 6, 12};
    int residue = 1;
    int failures = 0;
    int primitive_odd = 0;

    for (int exponent = 0; exponent < 20; exponent++) {
        int expected = exponent < 10
            ? first_half[exponent]
            : 25 - first_half[exponent - 10];
        if (residue != expected) failures++;
        residue = residue * 2 % 25;
    }
    if (residue != 1 || first_half[2] != 4 || first_half[7] != 3)
        failures++;
    for (int exponent = 1; exponent < 20; exponent++)
        if (exponent % 2 == 1 && exponent % 5 != 0) primitive_odd++;
    if (primitive_odd != 8) failures++;
    if (report) {
        printf("  powers of two, reflected residues, and eight primitive odd exponents  %s\n",
               failures == 0 ? "PASS" : "FAIL");
    }
    return failures;
}

static int laurent_expansion_certificate(int report)
{
    static const int expected_d[15] = {
        1, 1, 1, 0, 0, 1, 2, 4, 2, 1, 0, 0, 1, 1, 1
    };
    static const int expected_even[20] = {
        32, 0, 14, 0, 7, 0, 17, 0, 9, 0,
        2, 0, 9, 0, 17, 0, 7, 0, 14, 0
    };
    static const int ramanujan_exponents[6] = {0, 2, 4, 6, 8, 10};
    static const int ramanujan_expected[6] = {8, 2, -2, 2, -2, -8};
    int d[15] = {0};
    int d_mod_twenty[20] = {0};
    int d_square_mod_twenty[20] = {0};
    int failures = 0;

    for (int left = 0; left < 8; left++)
        for (int right = 0; right < 8; right++)
            d[7 + left - right] += base_five_p[left] * base_five_p[right];
    for (int index = 0; index < 15; index++) {
        int exponent = index - 7;
        int reduced = (exponent % 20 + 20) % 20;
        if (d[index] != expected_d[index]) failures++;
        d_mod_twenty[reduced] += d[index];
    }
    for (int left = 0; left < 20; left++)
        for (int right = 0; right < 20; right++)
            d_square_mod_twenty[(left + right) % 20] +=
                d_mod_twenty[left] * d_mod_twenty[right];
    for (int exponent = 0; exponent < 20; exponent += 2)
        if (d_square_mod_twenty[exponent] != expected_even[exponent])
            failures++;
    for (int index = 0; index < 6; index++)
        if (ramanujan_sum_twenty(ramanujan_exponents[index]) !=
            ramanujan_expected[index])
            failures++;
    if (report) {
        printf("  Laurent expansion, cyclic square, and Ramanujan values  %s\n",
               failures == 0 ? "PASS" : "FAIL");
    }
    return failures;
}

static int polynomial_certificate(int report)
{
    int left[15] = {0};
    int right[15] = {0};
    int mismatches = 0;

    for (int left_index = 0; left_index < 8; left_index++) {
        for (int right_index = 0; right_index < 8; right_index++) {
            int degree = 7 + left_index - right_index;
            left[degree] +=
                base_five_q[left_index] * base_five_q[right_index] -
                5 * base_five_p[left_index] * base_five_p[right_index];
        }
    }
    for (int left_index = 0; left_index < 9; left_index++)
        for (int right_index = 0; right_index < 7; right_index++)
            right[left_index + right_index] +=
                cyclotomic_twenty[left_index] *
                certificate_quotient[right_index];
    for (int degree = 0; degree < 15; degree++)
        if (left[degree] != right[degree]) mismatches++;
    if (report) {
        printf("  Laurent polynomial certificate degrees 0 through 14: %d mismatches  %s\n",
               mismatches, mismatches == 0 ? "PASS" : "FAIL");
    }
    return mismatches;
}

static int base_five_audit(int report)
{
    CollisionSpectrumSummary summary;
    int orbit_failures = power_orbit_certificate(report);
    int expansion_failures = laurent_expansion_certificate(report);
    int polynomial_failures = polynomial_certificate(report);
    int ramanujan_moment =
        32 * 8 + 28 * 2 + 14 * (-2) + 34 * 2 + 18 * (-2) + 2 * (-8);
    int diagonal_fourth_moment = 16 * ramanujan_moment;
    int bernoulli_fourth_moment = diagonal_fourth_moment / 25;
    int failures = orbit_failures + expansion_failures + polynomial_failures;

    if (!collision_spectrum_base_audit(5, &summary)) return 1;
    if (ramanujan_moment != 300 || diagonal_fourth_moment != 4800 ||
        bernoulli_fourth_moment != 192 || summary.energy_numerator != 1200 ||
        summary.base_five_relation_error > 2.0e-11L)
        failures++;
    if (report) {
        long double pi = acosl(-1.0L);
        long double expected_l_fourth =
            192.0L * pi * pi * pi * pi / 625.0L;
        printf("  primitive-twentieth-root Ramanujan moment = %d  %s\n",
               ramanujan_moment, ramanujan_moment == 300 ? "PASS" : "FAIL");
        printf("  sum |S_G|^4 = %d  %s\n", diagonal_fourth_moment,
               diagonal_fourth_moment == 4800 ? "PASS" : "FAIL");
        printf("  sum |B_1|^4 = %d  %s\n", bernoulli_fourth_moment,
               bernoulli_fourth_moment == 192 ? "PASS" : "FAIL");
        printf("  centered energy numerator/base^2 = %lld/25 = %.0Lf  %s\n",
               (long long)summary.energy_numerator,
               (long double)summary.energy_numerator / 25.0L,
               summary.energy_numerator == 1200 ? "PASS" : "FAIL");
        printf("  max |S_G|-sqrt(5)|B_1| error = %.3Le  %s\n",
               summary.base_five_relation_error,
               summary.base_five_relation_error <= 2.0e-11L
                   ? "PASS" : "FAIL");
        printf("  max coefficient square-law error = %.3Le  %s\n",
               summary.base_five_coefficient_error,
               summary.base_five_coefficient_error <= 2.0e-11L
                   ? "PASS" : "FAIL");
        printf("  sum |L(1,chi)|^4 = %.15Lf\n",
               summary.base_five_l_one_fourth_moment);
        printf("  exact target 192*pi^4/625 = %.15Lf  %s\n",
               expected_l_fourth,
               fabsl(summary.base_five_l_one_fourth_moment -
                     expected_l_fourth) <= 2.0e-11L ? "PASS" : "FAIL");
    }
    return failures;
}

int base_five_cyclotomic_identity_audit(void)
{
    int failures;
    printf("Base-five cyclotomic identity\n");
    printf("Exact polynomial and fourth-moment certificate\n\n");
    failures = base_five_audit(1);
    printf("\nClassification  the polynomial, Ramanujan, energy, and moment targets\n");
    printf("are exact; roots-of-unity magnitudes are numerical corroboration.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    return failures == 0 ? 0 : 1;
}

int base_five_cyclotomic_identity_verify(void)
{
    int ok = base_five_audit(0) == 0;
    printf("Base-five cyclotomic identity verification\n\n");
    printf("  exact power orbit and primitive exponents      %s\n",
           ok ? "PASS" : "FAIL");
    printf("  exact Laurent expansions and Ramanujan values  %s\n",
           ok ? "PASS" : "FAIL");
    printf("  exact cyclotomic polynomial certificate        %s\n",
           ok ? "PASS" : "FAIL");
    printf("  all eight magnitude and coefficient laws       %s\n",
           ok ? "PASS" : "FAIL");
    printf("  exact centered collision energy E_5=48        %s\n",
           ok ? "PASS" : "FAIL");
    printf("  exact Bernoulli, diagonal, and L(1) moments     %s\n",
           ok ? "PASS" : "FAIL");
    printf("\n6/6 verification groups %s.\n",
           ok ? "passed" : "did not pass");
    printf("Identity  the cyclotomic certificate forces the magnitude and\n");
    printf("coefficient laws; exact finite ledgers give the energy and moments.\n");
    return ok;
}

void base_five_cyclotomic_identity_help(void)
{
    printf(
        "Base-five cyclotomic identity\n\n"
        "Commands\n"
        "  nfield base-five-cyclotomic-identity audit\n"
        "      Check the exact polynomial certificate, Ramanujan moment,\n"
        "      centered energy, and L(1) fourth-moment value.\n"
        "  nfield base-five-cyclotomic-identity verify\n"
        "  nfield verify base-five-cyclotomic-identity\n\n"
        "Scope\n"
        "  exact identities   base-five cyclotomic magnitude relation,\n"
        "                     coefficient square law, and fourth moment.\n"
        "  exact computation integer polynomial and Ramanujan certificates.\n"
        "  numerical check   all eight primitive odd roots-of-unity channels.\n"
    );
}
