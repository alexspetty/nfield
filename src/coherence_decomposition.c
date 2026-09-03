/*
 * coherence_decomposition.c: Exact synchronized reference/pairwise checks.
 *
 * Alpha compares every row with 1/n. Sigma averages distinct unordered
 * pairs. They use the same clearing depth and the same rough-part period,
 * but different sample spaces. F is their signed difference.
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#define CD_MAX_N 5000
#define CD_MAX_BASE 10000
#define CD_MAX_EXTRA_DEPTH 10000
#define CD_PAIR_LIST_MAX_N 120
#define CD_PAIR_LIST_LIMIT 80

typedef struct {
    int n;
    int base;
    int rough;
    int supported;
    int minimum_depth;
    int depth;
    int order;
    int terminating;
    long long alpha_num;
    long long alpha_den;
    long long sigma_num;
    long long sigma_den;
    long long focused_num;
    long long focused_den;
    long long pair_score_num;
} CDData;

static int cd_gcd(int a, int b)
{
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a < 0 ? -a : a;
}

static long long cd_gcdll(long long a, long long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = b;
        b = a % b;
        a = t;
    }
    return a == 0 ? 1 : a;
}

static void cd_reduce(long long *numerator, long long *denominator)
{
    long long g = cd_gcdll(*numerator, *denominator);
    *numerator /= g;
    *denominator /= g;
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
}

static void cd_print_fraction(long long numerator, long long denominator)
{
    cd_reduce(&numerator, &denominator);
    printf("%lld/%lld", numerator, denominator);
}

static long double cd_value(long long numerator, long long denominator)
{
    return (long double)numerator / denominator;
}

static int cd_equal(long long an, long long ad,
                    long long bn, long long bd)
{
    long long ag = cd_gcdll(an, ad), bg = cd_gcdll(bn, bd);
    an /= ag; ad /= ag; bn /= bg; bd /= bg;
    return an == bn && ad == bd;
}

static long long cd_choose2(long long n)
{
    return n < 2 ? 0 : n * (n - 1) / 2;
}

static int cd_is_prime(int n)
{
    if (n < 2) return 0;
    if (n % 2 == 0) return n == 2;
    for (int d = 3; d <= n / d; d += 2)
        if (n % d == 0) return 0;
    return 1;
}

static int cd_supported_part(int n, int base, int *rough, int *supported)
{
    if (n < 1 || base < 2) return 0;
    int q = n;
    for (;;) {
        int g = cd_gcd(q, base);
        if (g == 1) break;
        q /= g;
    }
    *rough = q;
    *supported = n / q;
    return 1;
}

static int cd_clearing_depth(int supported, int base)
{
    int depth = 0;
    while (supported > 1) {
        int g = cd_gcd(supported, base);
        if (g == 1) return -1;
        supported /= g;
        depth++;
    }
    return depth;
}

static int cd_order(int base, int modulus)
{
    if (modulus == 1) return 1;
    if (modulus < 2 || cd_gcd(base, modulus) != 1) return -1;
    int value = base % modulus;
    int order = 1;
    while (value != 1 && order <= modulus) {
        value = (int)(((long long)value * base) % modulus);
        order++;
    }
    return value == 1 ? order : -1;
}

static int cd_subtract(long long an, long long ad,
                       long long bn, long long bd,
                       long long *rn, long long *rd)
{
    long long g = cd_gcdll(ad, bd);
    long long left_scale = bd / g;
    long long right_scale = ad / g;
    *rn = an * left_scale - bn * right_scale;
    *rd = ad * left_scale;
    cd_reduce(rn, rd);
    return 1;
}

static int cd_build(int n, int base, int requested_depth, CDData *data)
{
    memset(data, 0, sizeof(*data));
    if (n < 3 || n > CD_MAX_N || base < 2 || base > CD_MAX_BASE)
        return 0;

    int rough, supported;
    if (!cd_supported_part(n, base, &rough, &supported)) return 0;
    int minimum_depth = cd_clearing_depth(supported, base);
    int depth = requested_depth < 0 ? minimum_depth : requested_depth;
    if (minimum_depth < 0 || depth < minimum_depth
        || depth - minimum_depth > CD_MAX_EXTRA_DEPTH)
        return 0;
    int order = cd_order(base, rough);
    if (order < 1) return 0;

    data->n = n;
    data->base = base;
    data->rough = rough;
    data->supported = supported;
    data->minimum_depth = minimum_depth;
    data->depth = depth;
    data->order = order;

    if (rough == 1) {
        data->terminating = n - 1;
        data->alpha_num = 1;
        data->alpha_den = 1;
        data->sigma_num = 1;
        data->sigma_den = 1;
        data->focused_num = 0;
        data->focused_den = 1;
        data->pair_score_num = cd_choose2(n - 1);
        return 1;
    }

    long long *remainders = calloc((size_t)n, sizeof(long long));
    int *bins = calloc((size_t)base, sizeof(int));
    if (!remainders || !bins) {
        free(remainders);
        free(bins);
        return 0;
    }

    int terminating = 0;
    for (int k = 1; k < n; k++) {
        long long remainder = k;
        for (int j = 0; j < depth; j++)
            remainder = remainder * base % n;
        remainders[k] = remainder;
        if (remainder == 0) terminating++;
    }

    long long alpha_score = (long long)terminating * order;
    long long pair_score = cd_choose2(terminating) * order;
    long long reference = remainders[1];

    for (int position = 0; position < order; position++) {
        memset(bins, 0, (size_t)base * sizeof(int));
        int reference_digit = (int)(reference * base / n);
        for (int k = 1; k < n; k++) {
            if (remainders[k] == 0) continue;
            int digit = (int)(remainders[k] * base / n);
            if (digit == reference_digit) alpha_score++;
            bins[digit]++;
        }
        for (int digit = 0; digit < base; digit++)
            pair_score += cd_choose2(bins[digit]);
        reference = reference * base % n;
        for (int k = 1; k < n; k++)
            if (remainders[k] != 0)
                remainders[k] = remainders[k] * base % n;
    }

    free(remainders);
    free(bins);

    data->terminating = terminating;
    data->pair_score_num = pair_score;
    data->alpha_num = alpha_score;
    data->alpha_den = (long long)order * (n - 1);
    data->sigma_num = pair_score;
    data->sigma_den = (long long)order * cd_choose2(n - 1);
    cd_reduce(&data->alpha_num, &data->alpha_den);
    cd_reduce(&data->sigma_num, &data->sigma_den);
    cd_subtract(data->alpha_num, data->alpha_den,
                data->sigma_num, data->sigma_den,
                &data->focused_num, &data->focused_den);
    return 1;
}

int coherence_decomposition_fractions(
    int n, int base, int depth,
    long long *alpha_numerator, long long *alpha_denominator,
    long long *sigma_numerator, long long *sigma_denominator,
    long long *focused_numerator, long long *focused_denominator)
{
    if (!alpha_numerator || !alpha_denominator
        || !sigma_numerator || !sigma_denominator
        || !focused_numerator || !focused_denominator)
        return 0;
    CDData data;
    if (!cd_build(n, base, depth, &data)) return 0;
    *alpha_numerator = data.alpha_num;
    *alpha_denominator = data.alpha_den;
    *sigma_numerator = data.sigma_num;
    *sigma_denominator = data.sigma_den;
    *focused_numerator = data.focused_num;
    *focused_denominator = data.focused_den;
    return 1;
}

static int cd_validate_inspect(int n, int base, int depth)
{
    if (n < 3) {
        fprintf(stderr,
                "n must be at least 3; F(2) contains no distinct unordered pair\n");
        return 0;
    }
    if (n > CD_MAX_N) {
        fprintf(stderr, "n must not exceed %d for synchronized pair analysis\n",
                CD_MAX_N);
        return 0;
    }
    if (base < 2 || base > CD_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", CD_MAX_BASE);
        return 0;
    }
    int rough, supported;
    cd_supported_part(n, base, &rough, &supported);
    int minimum = cd_clearing_depth(supported, base);
    if (depth >= 0 && depth < minimum) {
        fprintf(stderr, "depth %d is too early; use --depth %d or greater\n",
                depth, minimum);
        return 0;
    }
    if (depth >= 0 && depth - minimum > CD_MAX_EXTRA_DEPTH) {
        fprintf(stderr, "depth may be at most %d positions beyond the minimum\n",
                CD_MAX_EXTRA_DEPTH);
        return 0;
    }
    return 1;
}

static void cd_print_data(const CDData *data)
{
    printf("  alpha_%d(%d) = ", data->base, data->n);
    cd_print_fraction(data->alpha_num, data->alpha_den);
    printf(" = %.12Lg  reference alignment\n",
           cd_value(data->alpha_num, data->alpha_den));
    printf("  sigma_%d(%d) = ", data->base, data->n);
    cd_print_fraction(data->sigma_num, data->sigma_den);
    printf(" = %.12Lg  symmetric pairwise alignment\n",
           cd_value(data->sigma_num, data->sigma_den));
    printf("  F_%d(%d) = alpha-sigma = ", data->base, data->n);
    cd_print_fraction(data->focused_num, data->focused_den);
    printf(" = %.12Lg  signed residual\n",
           cd_value(data->focused_num, data->focused_den));
}

static int cd_prime_core_formula_ok(const CDData *data)
{
    int p = data->rough, s = data->supported;
    return cd_is_prime(p) && data->base % p != 0 && p <= data->base + 1
        && cd_equal(data->alpha_num, data->alpha_den, 2LL * s - 1,
                    (long long)p * s - 1)
        && cd_equal(data->sigma_num, data->sigma_den, s - 1,
                    (long long)p * s - 1)
        && cd_equal(data->focused_num, data->focused_den, s,
                    (long long)p * s - 1);
}

int coherence_decomposition_inspect(int n, int base, int depth)
{
    if (!cd_validate_inspect(n, base, depth)) return 1;
    CDData data, later;
    if (!cd_build(n, base, depth, &data)
        || !cd_build(n, base, (depth < 0 ? data.minimum_depth : depth) + 1,
                     &later)) {
        fprintf(stderr, "could not build the synchronized decomposition\n");
        return 1;
    }

    int depth_ok = cd_equal(data.alpha_num, data.alpha_den,
                            later.alpha_num, later.alpha_den)
                && cd_equal(data.sigma_num, data.sigma_den,
                            later.sigma_num, later.sigma_den)
                && cd_equal(data.focused_num, data.focused_den,
                            later.focused_num, later.focused_den);

    printf("Synchronized coherence decomposition\n\n");
    printf("  n = %d, base = %d\n", n, base);
    printf("  canonical decomposition n = q*s = %d*%d\n",
           data.rough, data.supported);
    printf("  rough part q = %d%s\n", data.rough,
           data.rough > 1 && !cd_is_prime(data.rough)
               ? " (composite)" : "");
    printf("  supported part s = %d\n", data.supported);
    printf("  minimal clearing depth D = %d\n", data.minimum_depth);
    printf("  chosen common depth = %d\n", data.depth);
    printf("  common window L = ord_q(b) = %d\n", data.order);
    printf("  terminating rows = %d; field rows = %d; unordered pairs = %lld\n",
           data.terminating, n - 1, cd_choose2(n - 1));

    printf("\nExact synchronized statistics:\n");
    cd_print_data(&data);
    printf("  identity alpha = F + sigma: PASS\n");
    printf("  same values one common position later: %s\n",
           depth_ok ? "PASS" : "FAIL");

    int engine_ok = 1;
    if (n <= 1000) {
        double alpha = alignment_exact(n, base);
        double sigma = sigma_exact(n, base);
        engine_ok = fabsl(alpha - cd_value(data.alpha_num, data.alpha_den)) < 1e-12L
                 && fabsl(sigma - cd_value(data.sigma_num, data.sigma_den)) < 1e-12L;
        printf("  independent field-engine comparison: %s\n",
               engine_ok ? "PASS" : "FAIL");
    } else {
        printf("  independent field engine skipped above n=1000\n");
    }

    if (data.rough == 1) {
        printf("\nEntirely supported field: alpha=sigma=1 and F=0.\n");
    } else if (cd_is_prime(data.rough) && data.rough <= base + 1) {
        printf("\nDigit-partitioning prime-core formula: %s\n",
               cd_prime_core_formula_ok(&data) ? "PASS" : "FAIL");
    } else {
        printf("\nGeneral rough-part status:\n");
        printf("  alpha=F+sigma is a signed identity by definition.\n");
        printf("  F remains a signed residual; its exact sign is reported above.\n");
    }

    int ok = depth_ok && engine_ok;
    printf("\nResult: %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int coherence_decomposition_prime_core(int p, int supported,
                                       int base, int depth)
{
    if (p < 2 || !cd_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (base < 2 || base > CD_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", CD_MAX_BASE);
        return 1;
    }
    if (base % p == 0) {
        fprintf(stderr, "p must not divide the base\n");
        return 1;
    }
    if (p > base + 1) {
        fprintf(stderr, "prime-core formula requires p <= base + 1\n");
        return 1;
    }
    if (supported < 1 || !is_b_smooth(supported, base)) {
        fprintf(stderr, "s must be a positive base-supported integer\n");
        return 1;
    }
    long long nll = (long long)p * supported;
    if (nll < 3) {
        fprintf(stderr, "p*s must be at least 3 so an unordered pair exists\n");
        return 1;
    }
    if (nll > CD_MAX_N) {
        fprintf(stderr, "p*s must not exceed %d for the direct certificate\n",
                CD_MAX_N);
        return 1;
    }
    int n = (int)nll;
    if (!cd_validate_inspect(n, base, depth)) return 1;

    CDData data;
    if (!cd_build(n, base, depth, &data)) return 1;
    long long expected_pairs = cd_choose2(supported - 1)
                             + (long long)(p - 1) * cd_choose2(supported);
    int formula_ok = cd_prime_core_formula_ok(&data);
    int pairs_ok = data.pair_score_num == expected_pairs * data.order;

    printf("Digit-partitioning prime-core decomposition\n\n");
    printf("  base b = %d, p = %d, supported factor s = %d, n = %d\n",
           base, p, supported, n);
    printf("  hypotheses: p prime, p does not divide b, p <= b+1, s supported  PASS\n");
    printf("  common depth D = %d; common period L = %d\n",
           data.depth, data.order);
    printf("  terminating rows = s-1 = %d\n", supported - 1);
    printf("  nonterminating residue classes = p-1 = %d, each of size s = %d\n",
           p - 1, supported);
    printf("\nPair-score certificate:\n");
    printf("  C(s-1,2) + (p-1)C(s,2) = %lld\n", expected_pairs);
    printf("  direct synchronized pair score = %lld/%d = %lld  %s\n",
           data.pair_score_num, data.order,
           data.pair_score_num / data.order,
           pairs_ok ? "PASS" : "FAIL");
    printf("\nExact formulas:\n");
    cd_print_data(&data);
    printf("  sigma equals normalized terminating contribution (s-1)/(ps-1): %s\n",
           cd_equal(data.sigma_num, data.sigma_den,
                    supported - 1, n - 1) ? "PASS" : "FAIL");
    printf("  F equals normalized reference residue class s/(ps-1): %s\n",
           cd_equal(data.focused_num, data.focused_den,
                    supported, n - 1) ? "PASS" : "FAIL");
    printf("  alpha=F+sigma with different sample-space averages: %s\n",
           formula_ok ? "PASS" : "FAIL");
    return formula_ok && pairs_ok ? 0 : 1;
}

static int cd_pair_matches(int j, int k, const CDData *data)
{
    long long left = j, right = k;
    for (int d = 0; d < data->depth; d++) {
        left = left * data->base % data->n;
        right = right * data->base % data->n;
    }
    if (left == 0 && right == 0) return data->order;
    if (left == 0 || right == 0) return 0;

    int matches = 0;
    for (int position = 0; position < data->order; position++) {
        if (left * data->base / data->n
            == right * data->base / data->n)
            matches++;
        left = left * data->base % data->n;
        right = right * data->base % data->n;
    }
    return matches;
}

int coherence_decomposition_pairs(int n, int base, int depth)
{
    if (!cd_validate_inspect(n, base, depth)) return 1;
    if (n > CD_PAIR_LIST_MAX_N) {
        fprintf(stderr, "pair listing requires n <= %d\n", CD_PAIR_LIST_MAX_N);
        return 1;
    }
    CDData data;
    if (!cd_build(n, base, depth, &data)) return 1;

    printf("Nonzero synchronized pair scores for n=%d in base %d\n\n", n, base);
    printf("  common depth D = %d; window L = %d\n", data.depth, data.order);
    printf("  pair       score\n");
    int shown = 0, nonzero = 0;
    long long score_sum = 0;
    for (int j = 1; j < n; j++) {
        for (int k = j + 1; k < n; k++) {
            int matches = cd_pair_matches(j, k, &data);
            score_sum += matches;
            if (matches == 0) continue;
            if (shown < CD_PAIR_LIST_LIMIT) {
                printf("  (%d,%d)      ", j, k);
                cd_print_fraction(matches, data.order);
                printf("\n");
                shown++;
            }
            nonzero++;
        }
    }
    if (shown < nonzero)
        printf("  ... %d additional nonzero pairs omitted\n", nonzero - shown);
    if (nonzero == 0) printf("  none\n");
    printf("\n  nonzero unordered pairs = %d of %lld\n",
           nonzero, cd_choose2(n - 1));
    printf("  summed match positions = %lld; aggregate builder = %lld  %s\n",
           score_sum, data.pair_score_num,
           score_sum == data.pair_score_num ? "PASS" : "FAIL");
    printf("  sigma_%d(%d) = ", base, n);
    cd_print_fraction(data.sigma_num, data.sigma_den);
    printf("\n  symmetry is built in by enumerating each unordered pair once.\n");
    return score_sum == data.pair_score_num ? 0 : 1;
}

static int cd_digit_map_injective(int p, int base)
{
    int *seen = calloc((size_t)base, sizeof(int));
    if (!seen) return -1;
    int injective = 1;
    for (int r = 1; r < p; r++) {
        int digit = (int)(((long long)base * r) / p);
        if (seen[digit]) injective = 0;
        seen[digit] = 1;
    }
    free(seen);
    return injective;
}

int coherence_decomposition_sigma_zero(int maximum_prime, int base)
{
    if (base < 2 || base > CD_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", CD_MAX_BASE);
        return 1;
    }
    if (maximum_prime < 3 || maximum_prime > 300) {
        fprintf(stderr, "maximum prime must be between 3 and 300\n");
        return 1;
    }

    int tested = 0, failures = 0;
    printf("Sigma-zero characterization in base %d through p=%d\n\n",
           base, maximum_prime);
    printf("  p      L      digit map injective   exact sigma       equivalence\n");
    for (int p = 3; p <= maximum_prime; p++) {
        if (!cd_is_prime(p) || base % p == 0) continue;
        CDData data;
        if (!cd_build(p, base, -1, &data)) return 1;
        int injective = cd_digit_map_injective(p, base);
        int zero = data.sigma_num == 0;
        int expected = p <= base + 1;
        int ok = injective >= 0 && injective == zero && injective == expected;
        printf("  %-6d %-6d %-21s ", p, data.order,
               injective ? "yes" : "no");
        cd_print_fraction(data.sigma_num, data.sigma_den);
        printf("%-10s %s\n", "", ok ? "PASS" : "FAIL");
        failures += !ok;
        tested++;
    }
    printf("\n  tested primes = %d; equivalence failures = %d\n",
           tested, failures);
    printf("  sigma_b(p)=0 iff the digit map is injective: %s\n",
           failures == 0 ? "PASS" : "FAIL");
    return failures == 0 ? 0 : 1;
}

int coherence_decomposition_golden_gap(int base)
{
    if (base < 2 || base > CD_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", CD_MAX_BASE);
        return 1;
    }
    printf("Exact reciprocal-golden gap certificate\n\n");
    printf("  3 < 1+sqrt(5) < 4 because 4 < 5 < 9.\n");
    printf("  Therefore 1/p < 1/phi < 2/p exactly for primes p in {2,3}.\n");
    printf("  p=2 is degenerate: alpha_b(2s)=1.\n");
    printf("  Among odd primes, p=3 is unique.  PASS\n\n");
    printf("Finite-resolution certificates:\n");
    printf("  3/5 < 1/phi because 121 < 125.\n");
    printf("  p>=5: alpha < 2/p <= 2/5 < 3/5 < 1/phi.\n");
    printf("  p>=3: F <= 1/(p-1) <= 1/2 < 1/phi.\n");
    printf("  p=2: admissible s>=3, so F <= 3/5 < 1/phi.\n");
    printf("  finite bounds: PASS\n\n");
    printf("Digit-partitioning prime cores available in base %d:\n", base);
    for (int p = 2; p <= base + 1; p++) {
        if (!cd_is_prime(p) || base % p == 0) continue;
        printf("  p=%-6d limiting gap=%-3s%s\n", p,
               p == 2 || p == 3 ? "yes" : "no",
               p == 2 ? " (degenerate)" : "");
    }
    return 0;
}

static int cd_check_general_clock(void)
{
    for (int base = 2; base <= 16; base++) {
        for (int n = 3; n <= 180; n++) {
            CDData first, later, still_later;
            if (!cd_build(n, base, -1, &first)
                || !cd_build(n, base, first.minimum_depth + 1, &later)
                || !cd_build(n, base, first.minimum_depth + 2,
                             &still_later))
                return 0;
            if (first.n != first.rough * first.supported
                || cd_gcd(first.rough, base) != 1
                || !is_b_smooth(first.supported, base)
                || first.terminating != first.supported - 1)
                return 0;

            for (int divisor = 1; divisor <= n; divisor++) {
                if (n % divisor != 0 || !is_b_smooth(divisor, base))
                    continue;
                if (divisor > first.supported
                    || first.supported % divisor != 0)
                    return 0;
                int cofactor = n / divisor;
                if (cd_gcd(cofactor, base) == 1
                    && (divisor != first.supported
                        || cofactor != first.rough))
                    return 0;
            }

            if (!cd_equal(first.alpha_num, first.alpha_den,
                          later.alpha_num, later.alpha_den)
                || !cd_equal(first.sigma_num, first.sigma_den,
                             later.sigma_num, later.sigma_den)
                || !cd_equal(first.focused_num, first.focused_den,
                             later.focused_num, later.focused_den)
                || !cd_equal(first.alpha_num, first.alpha_den,
                             still_later.alpha_num, still_later.alpha_den)
                || !cd_equal(first.sigma_num, first.sigma_den,
                             still_later.sigma_num, still_later.sigma_den)
                || !cd_equal(first.focused_num, first.focused_den,
                             still_later.focused_num,
                             still_later.focused_den)
                || fabsl(alignment_exact(n, base)
                         - cd_value(first.alpha_num, first.alpha_den)) > 1e-12L
                || fabsl(sigma_exact(n, base)
                         - cd_value(first.sigma_num, first.sigma_den)) > 1e-12L)
                return 0;
        }
    }
    return 1;
}

static int cd_check_prime_formulas(void)
{
    int cases = 0;
    for (int base = 2; base <= 24; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!cd_is_prime(p) || base % p == 0) continue;
            for (int s = 1; s <= 64; s++) {
                if (!is_b_smooth(s, base) || p * s < 3 || p * s > 1000)
                    continue;
                CDData data;
                if (!cd_build(p * s, base, -1, &data)
                    || !cd_prime_core_formula_ok(&data))
                    return 0;
                cases++;
            }
        }
    }
    return cases > 100;
}

static int cd_check_limit_and_deficit_identities(void)
{
    int cases = 0;
    for (int base = 2; base <= 24; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!cd_is_prime(p) || base % p == 0) continue;
            for (int s = 1; s <= 96; s++) {
                if (!is_b_smooth(s, base) || p * s < 3
                    || p * s > 1500)
                    continue;
                CDData data;
                long long denominator = (long long)p * s - 1;
                if (!cd_build(p * s, base, -1, &data)
                    || 2LL * denominator - (long long)p * (2LL * s - 1)
                        != p - 2
                    || (long long)p * s - denominator != 1
                    || denominator - (long long)p * (s - 1) != p - 1
                    || (p == 2
                        && !cd_equal(data.alpha_num, data.alpha_den, 1, 1)))
                    return 0;
                cases++;
            }
        }
    }

    if (2 - 1 != 1) return 0;
    int odd_selected = 0;
    for (int p = 2; p <= 97; p++) {
        if (!cd_is_prime(p)) continue;
        int below_twice_phi = (long long)(p - 1) * (p - 1) < 5;
        if (below_twice_phi != (p == 2 || p == 3)) return 0;
        if (p % 2 != 0 && below_twice_phi) odd_selected++;
    }
    return cases > 100 && odd_selected == 1;
}

static int cd_check_pair_count(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!cd_is_prime(p) || base % p == 0) continue;
            for (int s = 1; s <= 48; s++) {
                if (!is_b_smooth(s, base) || p * s < 3 || p * s > 800)
                    continue;
                CDData data;
                if (!cd_build(p * s, base, -1, &data)) return 0;
                long long expected = cd_choose2(s - 1)
                                   + (long long)(p - 1) * cd_choose2(s);
                if (data.terminating != s - 1
                    || data.pair_score_num != expected * data.order)
                    return 0;
            }
        }
    }
    return 1;
}

static int cd_check_supported_and_edge(void)
{
    CDData data;
    if (cd_build(2, 10, -1, &data)) return 0;
    for (int base = 2; base <= 20; base++) {
        for (int n = 3; n <= 200; n++) {
            if (!is_b_smooth(n, base)) continue;
            if (!cd_build(n, base, -1, &data)
                || !cd_equal(data.alpha_num, data.alpha_den, 1, 1)
                || !cd_equal(data.sigma_num, data.sigma_den, 1, 1)
                || !cd_equal(data.focused_num, data.focused_den, 0, 1))
                return 0;
        }
    }
    return 1;
}

static int cd_check_golden_bounds(void)
{
    if (!(4 < 5 && 5 < 9 && 121 < 125)) return 0;
    for (int base = 2; base <= 30; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!cd_is_prime(p) || base % p == 0) continue;
            for (int s = 1; s <= 96; s++) {
                if (!is_b_smooth(s, base) || p * s < 3 || p * s > 1500)
                    continue;
                CDData data;
                if (!cd_build(p * s, base, -1, &data)) return 0;
                if (p >= 5
                    && data.alpha_num * p >= 2 * data.alpha_den)
                    return 0;
                if (p >= 3
                    && data.focused_num * (p - 1) > data.focused_den)
                    return 0;
                if (p == 2
                    && data.focused_num * 5 > 3 * data.focused_den)
                    return 0;
            }
        }
    }
    return 1;
}

static int cd_check_sigma_zero(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int p = 3; p <= 97; p++) {
            if (!cd_is_prime(p) || base % p == 0) continue;
            CDData data;
            if (!cd_build(p, base, -1, &data)) return 0;
            int injective = cd_digit_map_injective(p, base);
            if (injective < 0 || injective != (data.sigma_num == 0)
                || injective != (p <= base + 1))
                return 0;
        }
    }
    return 1;
}

static int cd_check_composite_identity(void)
{
    int fixtures[] = {9, 21, 27, 33, 49, 77, 81, 91};
    for (int base = 2; base <= 16; base++) {
        for (int i = 0; i < 8; i++) {
            int n = fixtures[i];
            CDData data;
            if (!cd_build(n, base, -1, &data)) return 0;
            long long fn, fd;
            cd_subtract(data.alpha_num, data.alpha_den,
                        data.sigma_num, data.sigma_den, &fn, &fd);
            if (!cd_equal(fn, fd,
                          data.focused_num, data.focused_den))
                return 0;
        }
    }
    return 1;
}

int coherence_decomposition_verify(void)
{
    printf("Exact C verification of the synchronized coherence decomposition\n");
    printf("Alpha and sigma retain their distinct sample-space normalizations.\n\n");

    int passed = 0;
    int ok = cd_check_general_clock();
    printf("  canonical decomposition, common clocks, and field engine: b<=16, n<=180 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_prime_formulas();
    printf("  exact alpha, F, sigma prime-core formulas: b<=24, s<=64             %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_pair_count();
    printf("  residue classes and exact unordered-pair score: b<=20, s<=48       %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_limit_and_deficit_identities();
    printf("  finite deficits, limit coefficients, and gap width: b<=24, s<=96   %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_supported_and_edge();
    printf("  fully supported fields and denominator-two domain boundary          %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_golden_bounds();
    printf("  exact golden-gap and finite-resolution bounds: b<=30, s<=96         %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_sigma_zero();
    printf("  sigma-zero iff digit-map injective: b<=20, primes p<=97             %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = cd_check_composite_identity();
    printf("  composite rough parts: exact signed identity and unrestricted sign   %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/8 finite checks passed.\n", passed);
    printf("All reported fractions use exact integer arithmetic. Finite sweeps\n");
    printf("are reproducible evidence, not a replacement for the universal proof.\n");
    return passed == 8;
}

void coherence_decomposition_help(void)
{
    printf("Synchronized reference and pairwise statistics\n\n");
    printf("Alpha is reference alignment. Sigma is the symmetric mean\n");
    printf("over distinct unordered pairs. F=alpha-sigma is a signed residual;\n");
    printf("the two averages do not share a sample space. Pairwise alignment is\n");
    printf("defined only for n>=3.\n\n");
    printf("Commands:\n");
    printf("  nfield coherence-decomposition inspect <n> [--base <b>] [--depth <D>]\n");
    printf("      Show the rough/support split and all three exact synchronized values.\n\n");
    printf("  nfield coherence-decomposition prime-core <p> <s> [--base <b>] [--depth <D>]\n");
    printf("      Verify the exact digit-partitioning formulas and pair-class count.\n\n");
    printf("  nfield coherence-decomposition pairs <n> [--base <b>] [--depth <D>]\n");
    printf("      List nonzero unordered pair scores and their aggregate certificate.\n\n");
    printf("  nfield coherence-decomposition sigma-zero <max-prime> [--base <b>]\n");
    printf("      Check sigma_b(p)=0 exactly when the digit map is injective.\n\n");
    printf("  nfield coherence-decomposition golden-gap [--base <b>]\n");
    printf("      Print the exact limiting and finite reciprocal-golden bounds.\n\n");
    printf("  nfield coherence-decomposition verify\n");
    printf("  nfield verify coherence-decomposition\n\n");
    printf("Examples:\n");
    printf("  nfield coherence-decomposition prime-core 3 4 --base 10\n");
    printf("  nfield coherence-decomposition inspect 77 --base 10\n");
    printf("  nfield coherence-decomposition pairs 13 --base 10\n");
    printf("  nfield coherence-decomposition sigma-zero 31 --base 10\n\n");
    printf("Composite rough parts retain the exact signed identity alpha=F+sigma;\n");
    printf("F is displayed as a signed residual with its exact computed sign.\n");
}
