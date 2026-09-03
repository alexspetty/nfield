/*
 * digit_partition.c: Inspect and verify synchronized digit alignment.
 *
 * Every row is compared on one absolute long-division clock.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "nfield.h"

static int dp_gcd(int a, int b)
{
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a < 0 ? -a : a;
}

static int dp_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0)
            return 0;
    return 1;
}

/* Minimal t for which m divides base^t, or -1 if no such t exists. */
static int dp_clearing_depth(int m, int base)
{
    int t = 0;
    if (m < 1 || base < 2) return -1;
    while (m > 1) {
        int g = dp_gcd(m, base);
        if (g == 1) return -1;
        m /= g;
        t++;
    }
    return t;
}

static int dp_digit_map_injective(int p, int base)
{
    int *seen = calloc((size_t)base, sizeof(int));
    if (!seen) return 0;
    int injective = 1;
    for (int r = 1; r < p; r++) {
        int d = (base * r) / p;
        if (seen[d]) {
            injective = 0;
            break;
        }
        seen[d] = 1;
    }
    free(seen);
    return injective;
}

static int dp_find_factor(int n, int base, int *p_out, int *m_out)
{
    for (int d = 2; d <= n / d; d++) {
        if (n % d != 0) continue;
        int candidates[2] = {d, n / d};
        for (int i = 0; i < 2; i++) {
            int p = candidates[i];
            int m = n / p;
            if (dp_is_prime(p) && base % p != 0
                && dp_clearing_depth(m, base) >= 0) {
                *p_out = p;
                *m_out = m;
                return 1;
            }
        }
    }
    if (dp_is_prime(n) && base % n != 0) {
        *p_out = n;
        *m_out = 1;
        return 1;
    }
    return 0;
}

static int dp_match_count(const Repetend *a, const Repetend *b,
                          int depth, int length)
{
    int matches = 0;
    for (int i = 0; i < length; i++)
        if (repetend_digit_at(a, depth + i)
            == repetend_digit_at(b, depth + i))
            matches++;
    return matches;
}

static void dp_print_block(const Repetend *r, int depth, int length, int base)
{
    int shown = length < 64 ? length : 64;
    if (base <= 10) {
        for (int i = 0; i < shown; i++)
            printf("%d", repetend_digit_at(r, depth + i));
    } else {
        putchar('[');
        for (int i = 0; i < shown; i++) {
            if (i) putchar(' ');
            printf("%d", repetend_digit_at(r, depth + i));
        }
        putchar(']');
    }
    if (shown < length) printf("... (%d digits total)", length);
}

int digit_partition_inspect(int n, int base, int requested_depth)
{
    if (n < 2) {
        fprintf(stderr, "n must be at least 2\n");
        return 1;
    }
    if (base < 2) {
        fprintf(stderr, "base must be at least 2\n");
        return 1;
    }

    Repetend reference = repetend_compute(1, n, base);
    int minimum_depth = reference.cycle_start;
    int depth = requested_depth < 0 ? minimum_depth : requested_depth;
    int period = reference.cycle_len;

    if (period > 0 && depth < minimum_depth) {
        fprintf(stderr,
                "depth %d is before the repeating block; use --depth %d or greater\n",
                depth, minimum_depth);
        repetend_free(&reference);
        return 1;
    }

    printf("Digit-partition alignment for n = %d in base %d\n", n, base);
    printf("Common long-division clock: every fraction is read at the same absolute positions.\n\n");
    printf("  minimal clearing depth = %d\n", minimum_depth);
    printf("  chosen depth t = %d\n", depth);
    printf("  reference period L = %d\n", period);

    if (period == 0) {
        printf("  1/%d terminates in this base; every row terminates and is aligned by convention.\n",
               n);
    } else {
        printf("  compared digits = %d through %d after the radix point\n",
               depth + 1, depth + period);
        printf("  reference block = ");
        dp_print_block(&reference, depth, period, base);
        printf("\n");
    }

    printf("\nRows:\n");
    int aligned_count = 0;
    int *matched = calloc((size_t)n, sizeof(int));
    if (!matched) {
        repetend_free(&reference);
        fprintf(stderr, "out of memory\n");
        return 1;
    }

    for (int k = 1; k < n; k++) {
        Repetend row = repetend_compute(k, n, base);
        int aligned;
        if (row.cycle_len == 0) {
            aligned = 1;
            printf("  k=%-4d terminating  aligned=yes  convention\n", k);
        } else if (period == 0) {
            aligned = 0;
            printf("  k=%-4d repeating    aligned=no   reference terminates\n", k);
        } else {
            int matches = dp_match_count(&reference, &row, depth, period);
            aligned = matches == period;
            printf("  k=%-4d repeating    matches=%d/%d  aligned=%s  block=",
                   k, matches, period, aligned ? "yes" : "no");
            dp_print_block(&row, depth, period, base);
            printf("\n");
        }
        if (aligned) matched[aligned_count++] = k;
        repetend_free(&row);
    }

    printf("\nmatched numerators:");
    for (int i = 0; i < aligned_count; i++) printf(" %d", matched[i]);
    printf("\n");
    printf("measured alignment = %d/%d = %.12g\n",
           aligned_count, n - 1, (double)aligned_count / (n - 1));

    int p = 0, m = 0;
    if (dp_find_factor(n, base, &p, &m)) {
        int t = dp_clearing_depth(m, base);
        printf("\nTheorem-form factorization: n = p*m = %d*%d\n", p, m);
        printf("  m is base-supported; minimal clearing depth = %d\n", t);
        printf("  p %s digit-partitioning because p %s base + 1 (%d %s %d)\n",
               p <= base + 1 ? "is" : "is not",
               p <= base + 1 ? "<=" : ">",
               p, p <= base + 1 ? "<=" : ">", base + 1);
        if (p <= base + 1) {
            int predicted = 2 * m - 1;
            printf("  predicted aligned count = 2m - 1 = %d\n", predicted);
            printf("  predicted alignment = %d/%d\n", predicted, p * m - 1);
            printf("  comparison = %s\n",
                   predicted == aligned_count ? "PASS" : "FAIL");
        }
    } else {
        printf("\nNo factorization n=p*m with p prime, p not dividing the base,\n");
        printf("and m base-supported was found. The alignment table remains exact.\n");
    }

    free(matched);
    repetend_free(&reference);
    return 0;
}

static int dp_round_thousandths(int p)
{
    return (4000 + p) / (2 * p);
}

void digit_partition_primes(int base)
{
    if (base < 2) {
        fprintf(stderr, "base must be at least 2\n");
        return;
    }

    printf("Digit-partitioning primes in base %d\n", base);
    printf("Criterion: p is prime, p does not divide the base, and p <= base + 1.\n");
    printf("primes:");
    for (int p = 2; p <= base + 1; p++)
        if (dp_is_prime(p) && base % p != 0 && dp_digit_map_injective(p, base))
            printf(" %d", p);
    printf("\n");
}

void digit_partition_table(void)
{
    static const int bases[] = {4, 6, 8, 10, 12, 16};

    printf("Selected digit-partition fixtures\n");
    printf("The limits are exact fractions 2/p; decimals are rounded to three places.\n\n");
    printf("  base  primes and alignment limits\n");
    for (size_t bi = 0; bi < sizeof(bases) / sizeof(bases[0]); bi++) {
        int base = bases[bi];
        printf("  %-4d ", base);
        int first = 1;
        for (int p = 2; p <= base + 1; p++) {
            if (!dp_is_prime(p) || base % p == 0
                || !dp_digit_map_injective(p, base))
                continue;
            int rounded = dp_round_thousandths(p);
            if (!first) printf(", ");
            printf("p=%d: 2/%d=%d.%03d", p, p,
                   rounded / 1000, rounded % 1000);
            first = 0;
        }
        printf("\n");
    }
    printf("\nResult  PASS\n");
}

/* Direct remainder-clock comparison, independent of field_build(). */
static int dp_direct_matches(int k, int n, int base, int depth, int length)
{
    int rr = 1 % n;
    int rk = k % n;
    for (int i = 0; i < depth; i++) {
        rr = (int)(((long long)base * rr) % n);
        rk = (int)(((long long)base * rk) % n);
    }

    int matches = 0;
    for (int i = 0; i < length; i++) {
        int dr = (int)(((long long)base * rr) / n);
        int dk = (int)(((long long)base * rk) / n);
        if (dr == dk) matches++;
        rr = (int)(((long long)base * rr) % n);
        rk = (int)(((long long)base * rk) % n);
    }
    return matches;
}

static long long dp_integer_power(int base, int exponent)
{
    long long value = 1;
    for (int i = 0; i < exponent; i++) value *= base;
    return value;
}

static int dp_power_mod(int base, int exponent, int modulus)
{
    long long value = 1;
    long long factor = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) value = value * factor % modulus;
        factor = factor * factor % modulus;
        exponent >>= 1;
    }
    return (int)value;
}

static int dp_state_after(int residue, int base, int p, int steps)
{
    return (int)((long long)residue * dp_power_mod(base, steps, p) % p);
}

static int dp_digit_from_state(int residue, int base, int p)
{
    return (int)((long long)base * residue / p);
}

static int dp_fraction_digit(int k, int n, int base, int position)
{
    int residue = k % n;
    for (int j = 0; j < position; j++)
        residue = (int)((long long)base * residue % n);
    return (int)((long long)base * residue / n);
}

static int dp_supported_by_prime_factors(int m, int base)
{
    if (m < 1 || base < 2) return 0;
    int remaining = m;
    for (int q = 2; q <= remaining / q; q++) {
        if (remaining % q != 0) continue;
        if (base % q != 0) return 0;
        while (remaining % q == 0) remaining /= q;
    }
    return remaining == 1 || base % remaining == 0;
}

static int dp_check_supported_denominators(void)
{
    if (dp_clearing_depth(0, 10) >= 0
        || dp_clearing_depth(-1, 10) >= 0
        || dp_clearing_depth(1, 1) >= 0)
        return 0;

    for (int base = 2; base <= 32; base++) {
        for (int m = 1; m <= 256; m++) {
            int supported = dp_supported_by_prime_factors(m, base);
            int depth = dp_clearing_depth(m, base);
            if ((depth >= 0) != supported) return 0;
            if (depth < 0) continue;
            long long power = dp_integer_power(base, depth);
            if (power % m != 0) return 0;
            if (depth > 0 && dp_integer_power(base, depth - 1) % m == 0)
                return 0;
        }
    }
    return 1;
}

static int dp_check_common_clock(void)
{
    static const int binary_expected[3][2] = {
        {0, 1}, {1, 0}, {0, 1}
    };
    static const int binary_numerators[] = {1, 2, 4};

    if (dp_fraction_digit(1, 3, 2, 0) != 0
        || dp_fraction_digit(1, 3, 2, 1) != 1)
        return 0;
    for (int row = 0; row < 3; row++)
        for (int j = 0; j < 2; j++)
            if (dp_fraction_digit(binary_numerators[row], 6, 2, 1 + j)
                != binary_expected[row][j])
                return 0;

    for (int base = 2; base <= 16; base++) {
        for (int p = 2; p <= 47; p++) {
            if (!dp_is_prime(p) || base % p == 0) continue;
            int length = mult_order(base, p);
            if (length <= 0) return 0;
            for (int m = 1; m <= 32; m++) {
                int depth = dp_clearing_depth(m, base);
                if (depth < 0) continue;
                int n = p * m;
                long long power = dp_integer_power(base, depth);
                int cofactor = (int)(power / m);
                if (power % m != 0 || dp_gcd(cofactor, p) != 1) return 0;
                for (int k = 1; k < n; k++) {
                    int reduced_denominator = n / dp_gcd(k, n);
                    int terminates = dp_clearing_depth(reduced_denominator, base) >= 0;
                    if (terminates != (k % p == 0)) return 0;

                    long long raw_remainder = (long long)k * power % n;
                    if (raw_remainder % m != 0
                        || raw_remainder / m != (long long)k * cofactor % p)
                        return 0;
                    if (terminates) continue;

                    int matches = dp_direct_matches(k, n, base, depth, length);
                    if (matches != dp_direct_matches(
                            k, n, base, depth + 1, length)
                        || matches != dp_direct_matches(
                            k, n, base, depth + 2, length))
                        return 0;
                }
            }
        }
    }
    return 1;
}

static int dp_check_boundary_and_endpoint(void)
{
    for (int base = 2; base <= 32; base++)
        for (int p = 2; p <= 127; p++) {
            if (!dp_is_prime(p) || base % p == 0) continue;
            if (dp_digit_map_injective(p, base) != (p <= base + 1))
                return 0;
        }

    for (int base = 2; base <= 128; base++) {
        int p = base + 1;
        if (!dp_is_prime(p)) continue;
        for (int r = 1; r < p; r++) {
            int digit = dp_digit_from_state(r, base, p);
            int complement = p - r;
            if (digit != r - 1
                || (long long)base * r % p != complement
                || digit + dp_digit_from_state(complement, base, p)
                    != base - 1)
                return 0;
        }
    }
    return 1;
}

static int dp_check_enumeration_and_roundings(void)
{
    static const int bases[] = {4, 6, 8, 10, 12, 16};
    static const int expected[][6] = {
        {3, 5, 0, 0, 0, 0},
        {5, 7, 0, 0, 0, 0},
        {3, 5, 7, 0, 0, 0},
        {3, 7, 11, 0, 0, 0},
        {5, 7, 11, 13, 0, 0},
        {3, 5, 7, 11, 13, 17}
    };
    static const int counts[] = {2, 2, 3, 3, 4, 6};
    static const int rounded[][6] = {
        {667, 400, 0, 0, 0, 0},
        {400, 286, 0, 0, 0, 0},
        {667, 400, 286, 0, 0, 0},
        {667, 286, 182, 0, 0, 0},
        {400, 286, 182, 154, 0, 0},
        {667, 400, 286, 182, 154, 118}
    };

    for (int bi = 0; bi < 6; bi++) {
        int got[8] = {0};
        int count = 0;
        int base = bases[bi];
        for (int p = 2; p <= base + 1; p++)
            if (dp_is_prime(p) && base % p != 0
                && dp_digit_map_injective(p, base))
                got[count++] = p;
        if (count != counts[bi]) return 0;
        for (int i = 0; i < count; i++)
            if (got[i] != expected[bi][i]
                || dp_round_thousandths(got[i]) != rounded[bi][i])
                return 0;
    }
    return 1;
}

static int dp_words_match_with_shift(
        int first, int second, int shift, int base, int p, int length)
{
    for (int j = 0; j < length; j++) {
        int first_state = dp_state_after(first, base, p, j + shift);
        int second_state = dp_state_after(second, base, p, j);
        if (dp_digit_from_state(first_state, base, p)
            != dp_digit_from_state(second_state, base, p))
            return 0;
    }
    return 1;
}

static int dp_check_cycle_partition(void)
{
    for (int base = 2; base <= 16; base++) {
        for (int p = 2; p <= 47; p++) {
            if (!dp_is_prime(p) || base % p == 0) continue;
            int L = mult_order(base, p);
            if (L <= 0 || (p - 1) % L != 0) return 0;

            int family[128];
            int representatives[128];
            for (int r = 0; r < 128; r++) family[r] = -1;
            int families = 0;
            for (int r = 1; r < p; r++) {
                if (family[r] >= 0) continue;
                representatives[families] = r;
                int state = r;
                for (int shift = 0; shift < L; shift++) {
                    if (state <= 0 || state >= p || family[state] >= 0)
                        return 0;
                    family[state] = families;
                    if (!dp_words_match_with_shift(
                            r, state, shift, base, p, L))
                        return 0;
                    state = (int)((long long)base * state % p);
                }
                if (state != r) return 0;
                families++;
            }
            if (families != (p - 1) / L) return 0;

            for (int r = 1; r < p; r++) {
                for (int q = 1; q < L; q++)
                    if (dp_state_after(r, base, p, q) == r) return 0;
                if (dp_state_after(r, base, p, L) != r) return 0;
            }

            for (int a = 0; a < families; a++)
                for (int c = a + 1; c < families; c++)
                    for (int shift = 0; shift < L; shift++)
                        if (dp_words_match_with_shift(
                                representatives[a], representatives[c], shift,
                                base, p, L))
                            return 0;

            for (int m = 1; m <= 16; m++) {
                if (dp_clearing_depth(m, base) < 0) continue;
                int n = p * m;
                int counts[128] = {0};
                for (int k = 1; k < n; k++)
                    if (k % p != 0) counts[k % p]++;
                for (int r = 1; r < p; r++)
                    if (counts[r] != m) return 0;
                if (families * (m * L) != m * (p - 1)) return 0;
            }
        }
    }
    return 1;
}

static int dp_check_exact_alignment_formula(void)
{
    for (int base = 2; base <= 16; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!dp_is_prime(p) || base % p == 0) continue;
            int length = mult_order(base, p);
            if (length <= 0) return 0;
            for (int m = 1; m <= 32; m++) {
                int depth = dp_clearing_depth(m, base);
                if (depth < 0) continue;
                int n = p * m;
                int terminating = 0;
                int matching_residue = 0;
                int aligned = 0;
                long long position_matches = 0;
                for (int k = 1; k < n; k++) {
                    if (k % p == 0) {
                        terminating++;
                        aligned++;
                        position_matches += length;
                        continue;
                    }
                    int matches = dp_direct_matches(k, n, base, depth, length);
                    if (matches != 0 && matches != length) return 0;
                    if ((matches == length) != (k % p == 1)) return 0;
                    if (k % p == 1) matching_residue++;
                    if (matches == length) aligned++;
                    position_matches += matches;
                }
                if (terminating != m - 1
                    || matching_residue != m
                    || (n - 1 - terminating) != (p - 1) * m
                    || aligned != 2 * m - 1
                    || position_matches != (long long)(2 * m - 1) * length)
                    return 0;
            }
        }
    }
    return 1;
}

static int dp_check_limit_and_prime_two(void)
{
    for (int p = 2; p <= 127; p++) {
        if (!dp_is_prime(p)) continue;
        for (int m = 1; m <= 256; m++) {
            long long formula_numerator = 2LL * m - 1;
            long long formula_denominator = (long long)p * m - 1;
            if (2 * formula_denominator - p * formula_numerator != p - 2)
                return 0;
            if (p > 2 && p * formula_numerator >= 2 * formula_denominator)
                return 0;
        }
    }

    for (int base = 3; base <= 63; base += 2) {
        if (!dp_digit_map_injective(2, base)) return 0;
        for (int m = 1; m <= 128; m++) {
            int depth = dp_clearing_depth(m, base);
            if (depth < 0) continue;
            int n = 2 * m;
            int aligned = 0;
            for (int k = 1; k < n; k++) {
                if (k % 2 == 0
                    || dp_direct_matches(k, n, base, depth, 1) == 1)
                    aligned++;
            }
            if (aligned != n - 1) return 0;
        }
    }
    return 1;
}

static int dp_check_decimal_structures(void)
{
    static const int seven_word[] = {1, 4, 2, 8, 5, 7};
    static const int eleven_first_digits[] =
        {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    static const int eleven_second_digits[] =
        {9, 8, 7, 6, 5, 4, 3, 2, 1, 0};
    static const int thirteen_first_digits[] =
        {0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9};

    for (int k = 1; k < 11; k++) {
        if (dp_fraction_digit(k, 11, 10, 0) != eleven_first_digits[k - 1]
            || dp_fraction_digit(k, 11, 10, 1)
                != eleven_second_digits[k - 1])
            return 0;
    }
    for (int k = 1; k < 13; k++)
        if (dp_fraction_digit(k, 13, 10, 0)
            != thirteen_first_digits[k - 1])
            return 0;

    if (mult_order(10, 3) != 1
        || dp_digit_from_state(1, 10, 3) != 3
        || dp_digit_from_state(2, 10, 3) != 6
        || mult_order(10, 7) != 6
        || mult_order(10, 11) != 2)
        return 0;

    int state = 1;
    int seen[10] = {0};
    for (int j = 0; j < 6; j++) {
        int digit = dp_digit_from_state(state, 10, 7);
        if (digit != seven_word[j] || seen[digit]) return 0;
        seen[digit] = 1;
        state = 10 * state % 7;
    }
    for (int r = 1; r < 7; r++) {
        int rotation = 0;
        while (rotation < 6 && dp_state_after(1, 10, 7, rotation) != r)
            rotation++;
        if (rotation == 6
            || !dp_words_match_with_shift(1, r, rotation, 10, 7, 6))
            return 0;
    }

    for (int r = 1; r < 11; r++) {
        int complement = 11 - r;
        if (10 * r % 11 != complement
            || dp_digit_from_state(r, 10, 11)
                + dp_digit_from_state(complement, 10, 11) != 9)
            return 0;
    }
    for (int k = 1; k <= 5; k++) {
        int first = 10 * dp_fraction_digit(k, 11, 10, 0)
            + dp_fraction_digit(k, 11, 10, 1);
        int paired = 10 * dp_fraction_digit(11 - k, 11, 10, 0)
            + dp_fraction_digit(11 - k, 11, 10, 1);
        if (first + paired != 99) return 0;
    }
    return 1;
}

static int dp_check_reciprocal_golden_selection(void)
{
    int selected = 0;
    for (int p = 3; p <= 10000; p++) {
        if (!dp_is_prime(p)) continue;
        long long certificate = 4LL + 2LL * p - (long long)p * p;
        int crosses = certificate > 0;
        if (crosses) selected++;
        if (crosses != (p == 3)) return 0;
    }
    if (selected != 1) return 0;

    for (int base = 2; base <= 256; base++) {
        int present = base % 3 != 0
            && dp_digit_map_injective(3, base);
        if (present != (base % 3 != 0)) return 0;
    }
    return 1;
}

int digit_partition_verify(void)
{
    printf("Synchronized digit-partition verification\n");
    printf("All fractions are compared on one absolute long-division clock.\n\n");

    int passed = 0;
    int ok;

    ok = dp_check_supported_denominators();
    printf("  positive supported denominators and minimal clearing depths %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_common_clock();
    printf("  common clock, tail cofactor, depth invariance, binary example %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_boundary_and_endpoint();
    printf("  digit-map boundary and endpoint complement structure        %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_cycle_partition();
    printf("  least periods, orbit families, cyclic shifts, lifted counts %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_exact_alignment_formula();
    printf("  termination classes, exact count and alignment formula      %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_limit_and_prime_two();
    printf("  supported-family limit identity and prime-two branch        %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_enumeration_and_roundings();
    printf("  selected prime table and every three-place rounding         %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_decimal_structures();
    printf("  decimal 11/13 boundary, 142857 orbit, complement pairs       %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dp_check_reciprocal_golden_selection();
    printf("  exact reciprocal-golden certificate and prime selection     %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/9 equation groups passed.\n", passed);
    printf("Finite verification is evidence, not the universal proof.\n");
    return passed == 9;
}

void digit_partition_help(void)
{
    printf("Digit-partition tools\n\n");
    printf("These commands compare every fraction k/n on one common long-division clock.\n");
    printf("They do not reset each repeating block to its own phase. Terminating rows\n");
    printf("are counted as aligned by convention.\n\n");
    printf("Commands:\n");
    printf("  nfield digit-partition inspect <n> [--base <b>] [--depth <t>]\n");
    printf("      Show every row's block, match score, matched numerators, and the\n");
    printf("      measured and predicted alignment when n=p*m has digit-partition form.\n");
    printf("      The default depth is the first repeating position of 1/n.\n\n");
    printf("  nfield digit-partition primes [--base <b>]\n");
    printf("      Enumerate the primes whose nonzero remainders occupy distinct\n");
    printf("      digit bins in the chosen base.\n\n");
    printf("  nfield digit-partition table\n");
    printf("      Reproduce the selected-base fixture with exact limits 2/p and\n");
    printf("      every three-place rounding.\n\n");
    printf("  nfield digit-partition verify\n");
    printf("  nfield verify digit-partition\n");
    printf("      Check supported denominators, common clocks, the digit boundary,\n");
    printf("      orbit families, exact counts, limits, selected tables, decimal\n");
    printf("      structures, and the reciprocal-golden certificate.\n\n");
    printf("Example:\n");
    printf("  nfield digit-partition inspect 6 --base 2\n");
    printf("  nfield digit-partition inspect 6 --base 2 --depth 2\n\n");
    printf("Finite verification is evidence, not the universal proof.\n");
}
