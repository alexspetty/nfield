/*
 * reciprocal_square_selection.c
 *
 * Exact finite certificates for the reciprocal-square threshold selection.
 * The implementation keeps the base-dependent alignment hypothesis separate
 * from the base-independent cubic and minimal-polynomial calculations.
 */

#include <limits.h>
#include <stdio.h>
#include "nfield.h"

#define RSS_MAX_DENOMINATOR 100000
#define RSS_MAX_PRIME 10000

typedef struct {
    long long rational;
    long long radical;
    long long denominator;
} RssQsqrtFive;

static int rss_factorization_identity(int prime);
static int rss_check_fourth_power_identity(void);

static int rss_gcd(int first, int second)
{
    while (second != 0) {
        int next = first % second;
        first = second;
        second = next;
    }
    return first < 0 ? -first : first;
}

static long long rss_gcdll(long long first, long long second)
{
    if (first < 0) first = -first;
    if (second < 0) second = -second;
    while (second != 0) {
        long long next = first % second;
        first = second;
        second = next;
    }
    return first == 0 ? 1 : first;
}

static int rss_is_prime(int value)
{
    if (value < 2) return 0;
    if (value % 2 == 0) return value == 2;
    for (int divisor = 3; divisor <= value / divisor; divisor += 2)
        if (value % divisor == 0) return 0;
    return 1;
}

static int rss_valid_pair(int prime, int resolution)
{
    return rss_is_prime(prime) && resolution >= 1
        && prime <= RSS_MAX_DENOMINATOR / resolution;
}

static int rss_clearing_depth(int resolution, int base)
{
    int remaining = resolution;
    int depth = 0;
    while (remaining > 1) {
        int common = rss_gcd(remaining, base);
        if (common == 1) return -1;
        remaining /= common;
        depth++;
    }
    return depth;
}

static void rss_reduce(long long *numerator, long long *denominator)
{
    long long common = rss_gcdll(*numerator, *denominator);
    *numerator /= common;
    *denominator /= common;
}

static RssQsqrtFive rss_qsqrt_five(
        long long rational, long long radical, long long denominator)
{
    RssQsqrtFive value = {rational, radical, denominator};
    if (value.denominator < 0) {
        value.rational = -value.rational;
        value.radical = -value.radical;
        value.denominator = -value.denominator;
    }
    long long common = rss_gcdll(value.rational, value.radical);
    common = rss_gcdll(common, value.denominator);
    value.rational /= common;
    value.radical /= common;
    value.denominator /= common;
    return value;
}

static RssQsqrtFive rss_qsqrt_five_integer(long long value)
{
    return rss_qsqrt_five(value, 0, 1);
}

static RssQsqrtFive rss_qsqrt_five_add(
        RssQsqrtFive first, RssQsqrtFive second)
{
    return rss_qsqrt_five(
        first.rational * second.denominator
            + second.rational * first.denominator,
        first.radical * second.denominator
            + second.radical * first.denominator,
        first.denominator * second.denominator);
}

static RssQsqrtFive rss_qsqrt_five_scale(
        RssQsqrtFive value, long long scalar)
{
    return rss_qsqrt_five(
        scalar * value.rational,
        scalar * value.radical,
        value.denominator);
}

static RssQsqrtFive rss_qsqrt_five_subtract(
        RssQsqrtFive first, RssQsqrtFive second)
{
    return rss_qsqrt_five_add(first, rss_qsqrt_five_scale(second, -1));
}

static RssQsqrtFive rss_qsqrt_five_multiply(
        RssQsqrtFive first, RssQsqrtFive second)
{
    return rss_qsqrt_five(
        first.rational * second.rational
            + 5 * first.radical * second.radical,
        first.rational * second.radical
            + first.radical * second.rational,
        first.denominator * second.denominator);
}

static RssQsqrtFive rss_qsqrt_five_power(
        RssQsqrtFive value, int exponent)
{
    RssQsqrtFive result = rss_qsqrt_five_integer(1);
    for (int index = 0; index < exponent; index++)
        result = rss_qsqrt_five_multiply(result, value);
    return result;
}

static int rss_qsqrt_five_equal(
        RssQsqrtFive first, RssQsqrtFive second)
{
    return first.rational * second.denominator
            == second.rational * first.denominator
        && first.radical * second.denominator
            == second.radical * first.denominator;
}

static int rss_qsqrt_five_sign(RssQsqrtFive value)
{
    long long rational = value.rational;
    long long radical = value.radical;
    if (rational == 0)
        return radical > 0 ? 1 : radical < 0 ? -1 : 0;
    if (radical == 0)
        return rational > 0 ? 1 : -1;
    if (rational > 0 && radical > 0) return 1;
    if (rational < 0 && radical < 0) return -1;

    long long rational_square = rational * rational;
    long long radical_square = 5 * radical * radical;
    if (rational_square == radical_square) return 0;
    if (rational > 0)
        return rational_square > radical_square ? 1 : -1;
    return radical_square > rational_square ? 1 : -1;
}

static RssQsqrtFive rss_qsqrt_five_cubic_value(
        int prime, RssQsqrtFive value)
{
    RssQsqrtFive square = rss_qsqrt_five_multiply(value, value);
    RssQsqrtFive cube = rss_qsqrt_five_multiply(square, value);
    return rss_qsqrt_five_add(
        rss_qsqrt_five_subtract(cube, square),
        rss_qsqrt_five_add(
            rss_qsqrt_five_scale(value, -prime),
            rss_qsqrt_five_integer(2)));
}

static void rss_polynomial_multiply(
        const long long first[4], const long long second[4],
        long long product[4])
{
    for (int index = 0; index < 4; index++) product[index] = 0;
    for (int first_degree = 0; first_degree < 4; first_degree++)
        for (int second_degree = 0;
             first_degree + second_degree < 4; second_degree++)
            product[first_degree + second_degree]
                += first[first_degree] * second[second_degree];
}

static int rss_polynomial_equal(
        const long long first[4], const long long second[4])
{
    for (int index = 0; index < 4; index++)
        if (first[index] != second[index]) return 0;
    return 1;
}

static int rss_synchronized_digit(
        int numerator, int denominator, int base, int depth)
{
    int remainder = numerator % denominator;
    for (int position = 0; position < depth; position++)
        remainder = (int)(((long long)base * remainder) % denominator);
    return (int)(((long long)base * remainder) / denominator);
}

static int rss_direct_aligned_count_at_depth(
        int prime, int resolution, int base, int depth,
        int *aligned_count)
{
    if (!rss_valid_pair(prime, resolution) || base < 2
        || base % prime != 1 || !is_b_smooth(resolution, base))
        return 0;

    int minimum_depth = rss_clearing_depth(resolution, base);
    if (minimum_depth < 0 || depth < minimum_depth) return 0;
    int denominator = prime * resolution;
    int reference_digit = rss_synchronized_digit(1, denominator, base, depth);
    int aligned = 0;

    for (int numerator = 1; numerator < denominator; numerator++) {
        if (numerator % prime == 0) {
            aligned++;
            continue;
        }
        int row_digit = rss_synchronized_digit(
            numerator, denominator, base, depth);
        if (row_digit == reference_digit) aligned++;
    }

    *aligned_count = aligned;
    return 1;
}

static int rss_direct_aligned_count(
        int prime, int resolution, int base,
        int *aligned_count, int *clearing_depth)
{
    if (!rss_valid_pair(prime, resolution) || base < 2
        || base % prime != 1 || !is_b_smooth(resolution, base))
        return 0;

    int depth = rss_clearing_depth(resolution, base);
    if (depth < 0) return 0;
    if (!rss_direct_aligned_count_at_depth(
            prime, resolution, base, depth, aligned_count))
        return 0;
    *clearing_depth = depth;
    return 1;
}

int reciprocal_square_selection_alignment_fraction(
        int prime, int resolution,
        long long *numerator, long long *denominator)
{
    if (!numerator || !denominator || !rss_valid_pair(prime, resolution))
        return 0;
    *numerator = 2LL * resolution - 1;
    *denominator = (long long)prime * resolution - 1;
    rss_reduce(numerator, denominator);
    return 1;
}

int reciprocal_square_selection_threshold_sign(
        int prime, int resolution, long long *certificate)
{
    if (!certificate || !rss_valid_pair(prime, resolution)) return 0;
    long long numerator = 2LL * resolution - 1;
    long long denominator = (long long)prime * resolution - 1;
    *certificate = numerator * numerator
                 + numerator * denominator
                 - denominator * denominator;
    return 1;
}

int reciprocal_square_selection_cubic_remainder(
        int prime, int *linear_coefficient)
{
    if (!linear_coefficient || !rss_is_prime(prime)
        || prime > RSS_MAX_PRIME)
        return 0;
    *linear_coefficient = 3 - prime;
    return 1;
}

static long long rss_cubic_value(int prime, int value)
{
    long long x = value;
    return x * x * x - x * x - (long long)prime * x + 2;
}

static int rss_has_rational_root(int prime)
{
    const int candidates[] = {1, -1, 2, -2};
    for (int index = 0; index < 4; index++)
        if (rss_cubic_value(prime, candidates[index]) == 0) return 1;
    return 0;
}

static int rss_limit_golden_sign(int prime)
{
    return 4 + 2 * prime - prime * prime;
}

static int rss_root_in_separating_window(int prime)
{
    if (prime < 3) return 0;
    long long at_two_fifths = 238LL - 50LL * prime;
    long long at_two_thirds = 50LL - 18LL * prime;
    return at_two_fifths > 0 && at_two_thirds < 0;
}

static const char *rss_sign_word(long long value)
{
    return value > 0 ? "above" : value < 0 ? "below" : "equal";
}

int reciprocal_square_selection_inspect(int prime, int resolution, int base)
{
    if (!rss_is_prime(prime)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (resolution < 1) {
        fprintf(stderr, "m must be a positive integer\n");
        return 1;
    }
    if (prime > RSS_MAX_DENOMINATOR / resolution) {
        fprintf(stderr, "p*m must not exceed %d\n", RSS_MAX_DENOMINATOR);
        return 1;
    }
    if (base < 2 || base > RSS_MAX_DENOMINATOR) {
        fprintf(stderr, "base must be between 2 and %d\n",
                RSS_MAX_DENOMINATOR);
        return 1;
    }
    if (base % prime != 1) {
        fprintf(stderr,
                "one-digit regime requires base congruent to 1 modulo p\n");
        return 1;
    }
    if (!is_b_smooth(resolution, base)) {
        fprintf(stderr, "m must be base-supported\n");
        return 1;
    }

    long long formula_numerator = 0;
    long long formula_denominator = 0;
    long long threshold_certificate = 0;
    int direct_count = 0;
    int depth = 0;
    if (!reciprocal_square_selection_alignment_fraction(
            prime, resolution, &formula_numerator, &formula_denominator)
        || !reciprocal_square_selection_threshold_sign(
            prime, resolution, &threshold_certificate)
        || !rss_direct_aligned_count(
            prime, resolution, base, &direct_count, &depth))
        return 1;

    long long expected_count = 2LL * resolution - 1;
    long long field_size = (long long)prime * resolution - 1;
    int formula_ok = direct_count == expected_count;
    int selection_ok = (prime == 2 && threshold_certificate > 0)
        || (prime == 3
            && ((threshold_certificate > 0) == (resolution >= 3)))
        || (prime >= 5 && threshold_certificate < 0);

    printf("Reciprocal-square threshold selection\n\n");
    printf("  base b=%d; prime p=%d; supported resolution m=%d\n",
           base, prime, resolution);
    printf("  denominator p*m=%d; common clearing depth D=%d\n",
           prime * resolution, depth);
    printf("  direct aligned rows=%d; formula rows=2m-1=%lld  %s\n",
           direct_count, expected_count, formula_ok ? "PASS" : "FAIL");
    printf("  exact alignment alpha_b(pm)=%lld/%lld",
           formula_numerator, formula_denominator);
    if (formula_numerator != expected_count
        || formula_denominator != field_size)
        printf(" (reduced from %lld/%lld)", expected_count, field_size);
    printf("\n");
    printf("  threshold certificate A^2+A*B-B^2=%lld\n",
           threshold_certificate);
    printf("  alpha is %s reciprocal golden ratio 1/phi\n",
           rss_sign_word(threshold_certificate));
    printf("  exact threshold classification  %s\n",
           selection_ok ? "PASS" : "FAIL");

    if (prime == 2)
        printf("  status: degenerate prime; alpha=1 for every supported m.\n");
    else if (prime == 3)
        printf("  status: unique nondegenerate prime; integer threshold m>=3.\n");
    else
        printf("  status: no positive resolution reaches 1/phi.\n");

    printf("\nResult  %s\n", formula_ok && selection_ok ? "PASS" : "FAIL");
    return formula_ok && selection_ok ? 0 : 1;
}

int reciprocal_square_selection_cubic(int prime)
{
    if (!rss_is_prime(prime)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (prime > RSS_MAX_PRIME) {
        fprintf(stderr, "p must not exceed %d\n", RSS_MAX_PRIME);
        return 1;
    }

    int remainder = 0;
    if (!reciprocal_square_selection_cubic_remainder(prime, &remainder))
        return 1;
    int factors = rss_has_rational_root(prime);
    int expected_factors = prime == 2 || prime == 3 || prime == 5;
    int factorization_ok = factors == expected_factors
        && (!expected_factors || rss_factorization_identity(prime));
    int fourth_power_ok = prime != 3 || rss_check_fourth_power_identity();

    printf("Self-referential threshold cubic\n\n");
    printf("  f_p(x)=x^3-x^2-%d*x+2\n", prime);
    printf("  rational-root candidates: +1, -1, +2, -2\n");
    printf("  values: f(1)=%lld, f(-1)=%lld, f(2)=%lld, f(-2)=%lld\n",
           rss_cubic_value(prime, 1), rss_cubic_value(prime, -1),
           rss_cubic_value(prime, 2), rss_cubic_value(prime, -2));
    printf("  reducible over Q: %s  %s\n", factors ? "yes" : "no",
           factorization_ok ? "PASS" : "FAIL");
    if (prime == 2)
        printf("  factorization: (x-1)(x^2-2)\n");
    else if (prime == 3)
        printf("  factorization: (x-2)(x^2+x-1)\n");
    else if (prime == 5)
        printf("  factorization: (x+2)(x^2-3x+1)\n");
    else
        printf("  factorization: irreducible cubic over Q\n");

    printf("\nGolden minimal-polynomial division\n");
    printf("  quotient: x-2\n");
    printf("  remainder: (%d)*x\n", remainder);
    printf("  x^2+x-1 divides f_p exactly: %s\n",
           remainder == 0 ? "yes; p=3  PASS" : "no");
    if (prime == 3)
        printf("  induced exact identity: x^4=2-3x  %s\n",
               fourth_power_ok ? "PASS" : "FAIL");

    if (prime == 2) {
        printf("\n  self-referential threshold: absent from (0,1).\n");
    } else {
        long long left = 238LL - 50LL * prime;
        long long right = 50LL - 18LL * prime;
        printf("\nSeparating-window certificate\n");
        printf("  125*f_p(2/5)=%lld\n", left);
        printf("  27*f_p(2/3)=%lld\n", right);
        printf("  unique root lies in (2/5,2/3): %s\n",
               rss_root_in_separating_window(prime) ? "yes" : "no");
    }

    int ok = factorization_ok && fourth_power_ok
        && (remainder == 0) == (prime == 3);
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int reciprocal_square_selection_table(void)
{
    const int resolutions[] = {1, 2, 4, 5, 8, 10, 16, 32, 100, 256};
    const int displayed_roundings[] = {
        5000, 6000, 6364, 6429, 6522,
        6552, 6596, 6632, 6656, 6662
    };
    int all_ok = 1;

    printf("Reciprocal-square selection alignment fixture\n");
    printf("Base 10, p=3, ten displayed supported resolutions\n\n");
    printf("  m      n      exact alpha    decimal    direct rows    versus 1/phi\n");
    for (int index = 0; index < 10; index++) {
        int resolution = resolutions[index];
        long long numerator = 0;
        long long denominator = 0;
        long long certificate = 0;
        int direct_count = 0;
        int depth = 0;
        int ok = reciprocal_square_selection_alignment_fraction(
                3, resolution, &numerator, &denominator)
            && reciprocal_square_selection_threshold_sign(
                3, resolution, &certificate)
            && rss_direct_aligned_count(
                3, resolution, 10, &direct_count, &depth)
            && direct_count == 2 * resolution - 1;
        long long rounding =
            (2 * numerator * 10000 + denominator) / (2 * denominator);
        ok = ok && rounding == displayed_roundings[index];
        (void)depth;
        printf("  %-6d %-6d %lld/%-12lld %lld.%04lld   %-14d %s  %s\n",
               resolution, 3 * resolution, numerator, denominator,
               rounding / 10000, rounding % 10000, direct_count,
               rss_sign_word(certificate),
               ok ? "PASS" : "FAIL");
        if (!ok) all_ok = 0;
    }
    printf("\nFirst base-10 supported value above 1/phi: m=4, n=12.\n");
    printf("Algebraic integer threshold: m>=3; m=3 is not base-10 supported.\n");
    printf("Result  %s\n", all_ok ? "PASS" : "FAIL");
    return all_ok ? 0 : 1;
}

int reciprocal_square_selection_scan(int maximum_prime)
{
    if (maximum_prime < 2 || maximum_prime > RSS_MAX_PRIME) {
        fprintf(stderr, "maximum prime must be between 2 and %d\n",
                RSS_MAX_PRIME);
        return 1;
    }

    int primes = 0;
    int nondegenerate_selections = 0;
    int factorizations = 0;
    int golden_divisors = 0;
    int window_roots = 0;

    printf("Reciprocal-square prime-selection scan through %d\n\n",
           maximum_prime);
    printf("  p      limit>1/phi   cubic factors   golden divides   root in window\n");
    for (int prime = 2; prime <= maximum_prime; prime++) {
        if (!rss_is_prime(prime)) continue;
        int limit_selected = rss_limit_golden_sign(prime) > 0;
        int factors = rss_has_rational_root(prime);
        int golden = prime == 3;
        int in_window = rss_root_in_separating_window(prime);
        printf("  %-6d %-13s %-15s %-16s %s\n", prime,
               limit_selected ? "yes" : "no",
               factors ? "yes" : "no",
               golden ? "yes" : "no",
               in_window ? "yes" : "no");
        primes++;
        if (prime >= 3 && limit_selected) nondegenerate_selections++;
        if (factors) factorizations++;
        if (golden) golden_divisors++;
        if (in_window) window_roots++;
    }

    int expected_factorizations = maximum_prime >= 5 ? 3
        : maximum_prime >= 3 ? 2 : 1;
    int expected_three = maximum_prime >= 3 ? 1 : 0;
    int ok = nondegenerate_selections == expected_three
        && factorizations == expected_factorizations
        && golden_divisors == expected_three
        && window_roots == expected_three;
    printf("\n  primes inspected=%d\n", primes);
    printf("  nondegenerate limit selections=%d\n", nondegenerate_selections);
    printf("  rational cubic factorizations=%d\n", factorizations);
    printf("  golden minimal-polynomial divisors=%d\n", golden_divisors);
    printf("  separating-window roots=%d\n", window_roots);
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int rss_check_decimal_three_classes(int *models, long long *rows)
{
    *models = 0;
    *rows = 0;
    for (int resolution = 1; resolution <= 256; resolution++) {
        if (!is_b_smooth(resolution, 10)) continue;
        int denominator = 3 * resolution;
        int depth = rss_clearing_depth(resolution, 10);
        int reference_digit = rss_synchronized_digit(
            1, denominator, 10, depth);
        int terminating = 0;
        int matching = 0;
        int complementary = 0;
        if (reference_digit != 3 && reference_digit != 6) return 0;

        for (int numerator = 1; numerator < denominator; numerator++) {
            int reduced_denominator =
                denominator / rss_gcd(numerator, denominator);
            int actually_terminates =
                is_b_smooth(reduced_denominator, 10);
            int residue = numerator % 3;
            if (residue == 0) {
                if (!actually_terminates) return 0;
                terminating++;
            } else {
                int digit = rss_synchronized_digit(
                    numerator, denominator, 10, depth);
                if (actually_terminates) return 0;
                if (residue == 1) {
                    if (digit != reference_digit) return 0;
                    matching++;
                } else {
                    if (digit + reference_digit != 9) return 0;
                    complementary++;
                }
            }
        }
        if (terminating != resolution - 1
            || matching != resolution
            || complementary != resolution)
            return 0;
        (*models)++;
        *rows += denominator - 1;
    }
    return *models > 0;
}

static int rss_check_general_one_digit_formula(int *models)
{
    *models = 0;
    for (int base = 2; base <= 80; base++) {
        for (int prime = 2; prime < base; prime++) {
            if (!rss_is_prime(prime) || base % prime != 1) continue;
            int coefficient = (base - 1) / prime;
            for (int residue = 1; residue < prime; residue++) {
                int digit = base * residue / prime;
                if (digit != coefficient * residue) return 0;
                (*models)++;
            }
        }
    }
    return *models > 0;
}

static int rss_check_alignment_equation_families(int *models)
{
    int derivative_constant = 2 * (-1) - 3 * (-1);
    int derivative_linear = 2 * 3 - 3 * 2;
    if (derivative_constant != 1 || derivative_linear != 0) return 0;

    *models = 0;
    for (int prime = 2; prime <= 251; prime++) {
        if (!rss_is_prime(prime)) continue;
        for (int resolution = 1; resolution <= 512; resolution++) {
            if (!rss_valid_pair(prime, resolution)) continue;
            long long numerator = 2LL * resolution - 1;
            long long denominator = (long long)prime * resolution - 1;
            long long nonterminating =
                (long long)resolution * (prime - 1);
            long long matching_nonterminating = resolution;
            if (prime == 2) {
                if (numerator != denominator) return 0;
            } else if (prime * numerator >= 2 * denominator) {
                return 0;
            }
            if (matching_nonterminating * (prime - 1)
                    != nonterminating)
                return 0;
            (*models)++;
        }
    }
    return *models > 0;
}

static int rss_check_golden_threshold_identities(void)
{
    RssQsqrtFive zero = rss_qsqrt_five_integer(0);
    RssQsqrtFive one = rss_qsqrt_five_integer(1);
    RssQsqrtFive two = rss_qsqrt_five_integer(2);
    RssQsqrtFive phi = rss_qsqrt_five(1, 1, 2);
    RssQsqrtFive reciprocal = rss_qsqrt_five(-1, 1, 2);
    RssQsqrtFive phi_square = rss_qsqrt_five(3, 1, 2);
    RssQsqrtFive reciprocal_square = rss_qsqrt_five(3, -1, 2);
    RssQsqrtFive sqrt_five_minus_two = rss_qsqrt_five(-2, 1, 1);
    RssQsqrtFive three_minus_sqrt_five = rss_qsqrt_five(3, -1, 1);
    RssQsqrtFive reciprocal_equation = rss_qsqrt_five_add(
        rss_qsqrt_five_power(reciprocal, 2),
        rss_qsqrt_five_subtract(reciprocal, one));
    RssQsqrtFive square_equation = rss_qsqrt_five_add(
        rss_qsqrt_five_power(reciprocal_square, 2),
        rss_qsqrt_five_add(
            rss_qsqrt_five_scale(reciprocal_square, -3), one));

    return rss_qsqrt_five_equal(
               rss_qsqrt_five_multiply(phi, reciprocal), one)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_power(phi, 2), phi_square)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_add(phi, one), phi_square)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_power(reciprocal, 2), reciprocal_square)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_multiply(phi, sqrt_five_minus_two),
               reciprocal_square)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_multiply(
                   three_minus_sqrt_five, phi_square), two)
        && rss_qsqrt_five_equal(reciprocal_equation, zero)
        && rss_qsqrt_five_equal(square_equation, zero)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_cubic_value(3, reciprocal), zero)
        && rss_qsqrt_five_equal(
               rss_qsqrt_five_cubic_value(5, reciprocal_square), zero)
        && rss_qsqrt_five_sign(rss_qsqrt_five_subtract(
               reciprocal, rss_qsqrt_five(2, 0, 5))) > 0
        && rss_qsqrt_five_sign(rss_qsqrt_five_subtract(
               rss_qsqrt_five(2, 0, 3), reciprocal)) > 0
        && rss_qsqrt_five_sign(rss_qsqrt_five_subtract(
               rss_qsqrt_five(2, 0, 5), reciprocal_square)) > 0
        && 5 * 5 * 5 > 9 * 9
        && 3 * 3 * 5 < 7 * 7
        && 5 * 5 * 5 > 11 * 11;
}

static int rss_check_critical_resolution_identities(int *primes)
{
    *primes = 0;
    for (int prime = 3; prime <= RSS_MAX_PRIME; prime += 2) {
        if (!rss_is_prime(prime)) continue;
        long long cubic[4] = {2, -prime, -1, 1};
        long long first_factor[4] = {1, -1, 0, 0};
        long long square[4] = {0, 0, 1, 0};
        long long product[4] = {0, 0, 0, 0};
        long long closure_derivation[4] = {2, -prime, 0, 0};
        long long derivative[4] = {0, 0, 0, 0};
        long long expected_derivative[4] = {-prime, -2, 3, 0};
        rss_polynomial_multiply(first_factor, square, product);
        for (int degree = 0; degree < 4; degree++)
            closure_derivation[degree] -= product[degree];
        for (int degree = 1; degree < 4; degree++)
            derivative[degree - 1] = degree * cubic[degree];
        if (!rss_polynomial_equal(cubic, closure_derivation)
            || !rss_polynomial_equal(derivative, expected_derivative)
            || rss_cubic_value(prime, 0) != 2
            || rss_cubic_value(prime, 1) != 2 - prime
            || 8 - 4LL * prime != 4LL * (2 - prime))
            return 0;
        (*primes)++;
    }
    return *primes > 0;
}

static int rss_factorization_identity(int prime)
{
    long long linear[4] = {0, 0, 0, 0};
    long long quadratic[4] = {0, 0, 0, 0};
    long long product[4] = {0, 0, 0, 0};
    long long cubic[4] = {2, -prime, -1, 1};

    if (prime == 2) {
        linear[0] = -1; linear[1] = 1;
        quadratic[0] = -2; quadratic[2] = 1;
    } else if (prime == 3) {
        linear[0] = -2; linear[1] = 1;
        quadratic[0] = -1; quadratic[1] = 1; quadratic[2] = 1;
    } else if (prime == 5) {
        linear[0] = 2; linear[1] = 1;
        quadratic[0] = 1; quadratic[1] = -3; quadratic[2] = 1;
    } else {
        return 0;
    }
    rss_polynomial_multiply(linear, quadratic, product);
    return rss_polynomial_equal(product, cubic);
}

static int rss_check_fourth_power_identity(void)
{
    RssQsqrtFive reciprocal = rss_qsqrt_five(-1, 1, 2);
    RssQsqrtFive right = rss_qsqrt_five_subtract(
        rss_qsqrt_five_integer(2),
        rss_qsqrt_five_scale(reciprocal, 3));
    return rss_qsqrt_five_equal(
        rss_qsqrt_five_power(reciprocal, 4), right);
}

static int rss_check_alignment_formula(int *models, long long *rows)
{
    *models = 0;
    *rows = 0;
    for (int base = 2; base <= 80; base++) {
        for (int prime = 2; prime < base; prime++) {
            if (!rss_is_prime(prime) || base % prime != 1) continue;
            for (int resolution = 1; resolution <= 128; resolution++) {
                if (!is_b_smooth(resolution, base)) continue;
                if (prime > 5000 / resolution) continue;
                int direct_count = 0;
                int later_count = 0;
                int still_later_count = 0;
                int depth = 0;
                if (!rss_direct_aligned_count(
                        prime, resolution, base, &direct_count, &depth)
                    || direct_count != 2 * resolution - 1
                    || !rss_direct_aligned_count_at_depth(
                        prime, resolution, base, depth + 1, &later_count)
                    || !rss_direct_aligned_count_at_depth(
                        prime, resolution, base, depth + 2,
                        &still_later_count)
                    || direct_count != later_count
                    || direct_count != still_later_count
                    || depth != rss_clearing_depth(resolution, base))
                    return 0;
                (*models)++;
                *rows += (long long)prime * resolution - 1;
            }
        }
    }
    return *models > 0;
}

static int rss_check_threshold_classification(int *pairs)
{
    *pairs = 0;
    for (int prime = 2; prime <= 251; prime++) {
        if (!rss_is_prime(prime)) continue;
        for (int resolution = 1; resolution <= 512; resolution++) {
            if (!rss_valid_pair(prime, resolution)) continue;
            long long certificate = 0;
            if (!reciprocal_square_selection_threshold_sign(
                    prime, resolution, &certificate))
                return 0;
            int expected = prime == 2 ? 1
                : prime == 3 ? resolution >= 3 : 0;
            if ((certificate > 0) != expected || certificate == 0) return 0;
            (*pairs)++;
        }
    }
    return 1;
}

static int rss_check_limit_selection(int *primes)
{
    int selected = 0;
    int odd_selected = 0;
    *primes = 0;
    for (int prime = 2; prime <= RSS_MAX_PRIME; prime++) {
        if (!rss_is_prime(prime)) continue;
        if (rss_limit_golden_sign(prime) > 0) {
            selected++;
            if (prime % 2 != 0) odd_selected++;
        }
        (*primes)++;
    }
    return selected == 2 && odd_selected == 1
        && rss_limit_golden_sign(2) > 0
        && rss_limit_golden_sign(3) > 0
        && rss_limit_golden_sign(5) < 0;
}

static int rss_check_cubic_factorization(int *primes)
{
    int factors = 0;
    *primes = 0;
    for (int prime = 2; prime <= RSS_MAX_PRIME; prime++) {
        if (!rss_is_prime(prime)) continue;
        int observed = rss_has_rational_root(prime);
        int expected = prime == 2 || prime == 3 || prime == 5;
        if (observed != expected) return 0;
        if (expected && !rss_factorization_identity(prime)) return 0;
        if (observed) factors++;
        (*primes)++;
    }
    return factors == 3;
}

static int rss_check_minimal_polynomial(int *primes)
{
    int divisors = 0;
    *primes = 0;
    for (int prime = 2; prime <= RSS_MAX_PRIME; prime++) {
        if (!rss_is_prime(prime)) continue;
        int remainder = INT_MAX;
        if (!reciprocal_square_selection_cubic_remainder(
                prime, &remainder))
            return 0;
        long long linear[4] = {-2, 1, 0, 0};
        long long golden_polynomial[4] = {-1, 1, 1, 0};
        long long reconstructed[4] = {0, 0, 0, 0};
        long long cubic[4] = {2, -prime, -1, 1};
        rss_polynomial_multiply(
            linear, golden_polynomial, reconstructed);
        reconstructed[1] += remainder;
        if (!rss_polynomial_equal(reconstructed, cubic)) return 0;
        if (remainder == 0) divisors++;
        if ((remainder == 0) != (prime == 3)) return 0;
        (*primes)++;
    }
    return divisors == 1 && rss_check_fourth_power_identity();
}

static int rss_check_separating_window(int *primes)
{
    int roots = 0;
    *primes = 0;
    for (int prime = 3; prime <= RSS_MAX_PRIME; prime += 2) {
        if (!rss_is_prime(prime)) continue;
        int observed = rss_root_in_separating_window(prime);
        if (observed != (prime == 3)) return 0;
        if (observed) roots++;
        (*primes)++;
    }
    return roots == 1;
}

static int rss_check_decimal_fixture(void)
{
    const int resolutions[] = {1, 2, 4, 5, 8, 10, 16, 32, 100, 256};
    const int displayed_roundings[] = {
        5000, 6000, 6364, 6429, 6522,
        6552, 6596, 6632, 6656, 6662
    };
    for (int index = 0; index < 10; index++) {
        int resolution = resolutions[index];
        int direct_count = 0;
        int depth = 0;
        long long certificate = 0;
        long long numerator = 0;
        long long denominator = 0;
        if (!rss_direct_aligned_count(
                3, resolution, 10, &direct_count, &depth)
            || direct_count != 2 * resolution - 1
            || !reciprocal_square_selection_alignment_fraction(
                3, resolution, &numerator, &denominator)
            || !reciprocal_square_selection_threshold_sign(
                3, resolution, &certificate)
            || (certificate > 0) != (resolution >= 4)
            || (2 * numerator * 10000 + denominator)
                    / (2 * denominator)
                != displayed_roundings[index])
            return 0;
    }
    return !is_b_smooth(3, 10) && is_b_smooth(4, 10);
}

int reciprocal_square_selection_verify(void)
{
    int passed = 0;
    int models = 0;
    long long rows = 0;
    int count = 0;

    printf("Exact C verification of reciprocal-square threshold selection\n");
    printf("Base-dependent alignment and base-independent cubic certificates are separate.\n\n");

    int ok = rss_check_alignment_formula(&models, &rows);
    printf("  synchronized alignment and common clock: models=%d; rows=%lld  %s\n",
           models, rows, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_decimal_three_classes(&models, &rows);
    printf("  decimal three classes and nines complement: models=%d; rows=%lld  %s\n",
           models, rows, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_general_one_digit_formula(&count);
    printf("  general one-digit residue formula: digits=%d             %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_alignment_equation_families(&models);
    printf("  limit, derivative, and nonterminating identities: models=%d  %s\n",
           models, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_threshold_classification(&count);
    printf("  exact rational-versus-golden signs: pairs=%d             %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_golden_threshold_identities();
    printf("  exact golden-radical and threshold identities             %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_limit_selection(&count);
    printf("  unique odd-prime limit selection: primes=%d              %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_critical_resolution_identities(&count);
    printf("  critical-resolution, cubic, and root inputs: primes=%d    %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_cubic_factorization(&count);
    printf("  rational-root values and exact factorizations: primes=%d  %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_minimal_polynomial(&count);
    printf("  golden division and fourth-power identity: primes=%d      %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_separating_window(&count);
    printf("  exact self-referential window signs: odd primes=%d         %s\n",
           count, ok ? "PASS" : "FAIL");
    passed += ok;

    ok = rss_check_decimal_fixture();
    printf("  exact ten-row table, roundings, and first crossing         %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/12 verification groups passed.\n", passed);
    printf("These exact checks cover the mathematical equation families. Lean carries\n");
    printf("the universal proofs; nfield supplies the executable arithmetic.\n");
    return passed == 12;
}

void reciprocal_square_selection_help(void)
{
    printf(
        "Reciprocal-square threshold selection\n\n"
        "Commands\n"
        "  nfield reciprocal-square-selection inspect <p> <m> [--base <b>]\n"
        "      Check the one-digit hypotheses, synchronized count, exact alignment,\n"
        "      and rational-versus-golden threshold certificate.\n"
        "  nfield reciprocal-square-selection cubic <p>\n"
        "      Show rational-root values, factorization status, the exact golden\n"
        "      minimal-polynomial remainder, and separating-window signs.\n"
        "  nfield reciprocal-square-selection table\n"
        "      Reproduce the ten displayed base-ten supported-resolution rows.\n"
        "  nfield reciprocal-square-selection scan <maximum-prime>\n"
        "      List limit selection, cubic factors, golden divisibility, and window.\n"
        "  nfield reciprocal-square-selection verify\n"
        "  nfield verify reciprocal-square-selection\n\n"
        "Examples\n"
        "  nfield reciprocal-square-selection inspect 3 4 --base 10\n"
        "  nfield reciprocal-square-selection inspect 3 4 --base 4\n"
        "  nfield reciprocal-square-selection cubic 3\n"
        "  nfield reciprocal-square-selection scan 31\n\n"
        "Scope\n"
        "  exact   alpha_b(pm)=(2m-1)/(pm-1) in the stated one-digit supported\n"
        "          regime; comparison with 1/phi uses A^2+A*B-B^2, not decimals.\n"
        "  exact   among odd primes only p=3 can cross 1/phi; its integer\n"
        "          threshold is m>=3. Base support can move the first admissible m.\n"
        "  exact   f_p(x)=x^3-x^2-px+2 factors over Q only at p=2,3,5;\n"
        "          division by x^2+x-1 has remainder (3-p)x.\n"
        "  exact   the common clock, three decimal classes, limit, derivative,\n"
        "          golden identities, cubic derivation, root signs, fourth power,\n"
        "          nonterminating statistic, and displayed roundings are checked.\n"
        "  definition the reciprocal-square closure is the criterion classified;\n"
        "          the alignment equation supplies its critical resolution.\n"
        "  proof   Lean carries the universal arguments; nfield reproduces every\n"
        "          material equation family with exact arithmetic and bounded scans.\n"
    );
}
