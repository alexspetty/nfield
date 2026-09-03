/*
 * bin_derangements.c
 *
 * Exact finite tools for the digit-bin zero gate and constructive
 * collision mass.
 *
 * All structural checks use integer arithmetic.  Bounded sweeps reproduce
 * instances of universal finite-group identities; they are not presented as
 * a replacement for the separate proofs.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#define BD_MAX_PRIME 257
#define BD_MAX_BASE 256

static int bd_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int bd_valid(int p, int base, int report)
{
    if (!bd_is_prime(p)) {
        if (report) fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (p > BD_MAX_PRIME) {
        if (report) fprintf(stderr, "prime must not exceed %d\n", BD_MAX_PRIME);
        return 0;
    }
    if (base < 2) {
        if (report) fprintf(stderr, "base must be at least 2\n");
        return 0;
    }
    if (base > BD_MAX_BASE) {
        if (report) fprintf(stderr, "base must not exceed %d\n", BD_MAX_BASE);
        return 0;
    }
    if (base >= p) {
        if (report) fprintf(stderr, "the gate-width domain requires 2 <= base < p\n");
        return 0;
    }
    return 1;
}

static int bd_normalize(long long value, int p)
{
    int result = (int)(value % p);
    return result < 0 ? result + p : result;
}

static int bd_inverse(int value, int p)
{
    long long old_r = value;
    long long r = p;
    long long old_s = 1;
    long long s = 0;
    while (r != 0) {
        long long q = old_r / r;
        long long next = old_r - q * r;
        old_r = r;
        r = next;
        next = old_s - q * s;
        old_s = s;
        s = next;
    }
    if (old_r != 1 && old_r != -1) return 0;
    if (old_r == -1) old_s = -old_s;
    return bd_normalize(old_s, p);
}

static int bd_power(int base, int exponent, int p)
{
    long long result = 1;
    long long power = bd_normalize(base, p);
    while (exponent > 0) {
        if (exponent & 1) result = result * power % p;
        power = power * power % p;
        exponent >>= 1;
    }
    return (int)result;
}

static int bd_digit(int residue, int p, int base)
{
    return (int)((long long)base * residue / p);
}

int bin_derangements_collision_count(int p, int base, int multiplier,
                                     int *count)
{
    if (!count || !bd_valid(p, base, 0)) return 0;
    int g = bd_normalize(multiplier, p);
    if (g == 0) return 0;
    int total = 0;
    for (int r = 1; r < p; r++) {
        int gr = (int)((long long)g * r % p);
        if (bd_digit(r, p, base) == bd_digit(gr, p, base)) total++;
    }
    *count = total;
    return 1;
}

static int bd_congruence_collision_count(int p, int base, int multiplier)
{
    int g = bd_normalize(multiplier, p);
    int total = 0;
    for (int x = 1; x < p; x++) {
        int gx = (int)((long long)g * x % p);
        if (x % base == gx % base) total++;
    }
    return total;
}

static int bd_c_parameter(int p, int base, int multiplier)
{
    int denominator = bd_normalize(1LL - multiplier, p);
    if (denominator == 0) return 0;
    return (int)((long long)base * bd_inverse(denominator, p) % p);
}

static int bd_family_value(int p, int base, int u)
{
    int denominator = base - u;
    return bd_normalize(-(long long)u * bd_inverse(denominator, p), p);
}

int bin_derangements_family_values(int p, int base, int *values,
                                   int capacity, int *count)
{
    if (!values || !count || !bd_valid(p, base, 0) || capacity < base - 1)
        return 0;
    for (int u = 1; u < base; u++) values[u - 1] = bd_family_value(p, base, u);
    *count = base - 1;
    return 1;
}

int bin_derangements_mean_fraction(int p, int base,
                                   long long *numerator,
                                   long long *denominator)
{
    if (!numerator || !denominator || !bd_valid(p, base, 0) || p <= base + 1)
        return 0;
    long long q = (p - 1) / base;
    long long remainder = (p - 1) % base;
    *numerator = q * (base * (q - 1) + 2 * remainder);
    *denominator = base * (q - 1) + remainder;
    return *denominator > 0;
}

static void bd_bin_sizes(int p, int base, int *sizes)
{
    memset(sizes, 0, (size_t)base * sizeof(*sizes));
    for (int r = 1; r < p; r++) sizes[bd_digit(r, p, base)]++;
}

static int bd_check_bin_distribution(int p, int base)
{
    int *sizes = calloc((size_t)base, sizeof(*sizes));
    if (!sizes) return 0;
    bd_bin_sizes(p, base, sizes);
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    int large = 0;
    int total = 0;
    long long square_sum = 0;
    int ok = 1;
    for (int d = 0; d < base; d++) {
        int floor_size = ((d + 1) * p) / base - (d * p) / base
                       - (d == base - 1 ? 1 : 0);
        if (sizes[d] != floor_size) ok = 0;
        if (sizes[d] != q && sizes[d] != q + 1) ok = 0;
        if (sizes[d] == q + 1) large++;
        total += sizes[d];
        square_sum += (long long)sizes[d] * sizes[d];
    }
    long long closed = (long long)base * q * q
                     + (long long)remainder * (2 * q + 1);
    ok = ok && large == remainder && total == p - 1 && square_sum == closed;
    free(sizes);
    return ok;
}

static int bd_check_conjugation(int p, int base)
{
    int *digit_to_class = malloc((size_t)base * sizeof(*digit_to_class));
    int *class_to_digit = malloc((size_t)base * sizeof(*class_to_digit));
    if (!digit_to_class || !class_to_digit) {
        free(digit_to_class);
        free(class_to_digit);
        return 0;
    }
    for (int i = 0; i < base; i++) {
        digit_to_class[i] = -1;
        class_to_digit[i] = -1;
    }
    int ok = 1;
    for (int r = 1; r < p; r++) {
        int digit = bd_digit(r, p, base);
        int x = (int)((long long)base * r % p);
        int residue_class = x % base;
        if ((long long)base * r != (long long)p * digit + x) {
            ok = 0;
            break;
        }
        if ((digit_to_class[digit] >= 0 &&
             digit_to_class[digit] != residue_class) ||
            (class_to_digit[residue_class] >= 0 &&
             class_to_digit[residue_class] != digit)) {
            ok = 0;
            break;
        }
        digit_to_class[digit] = residue_class;
        class_to_digit[residue_class] = digit;
    }
    for (int i = 0; i < base; i++)
        if (digit_to_class[i] < 0 || class_to_digit[i] < 0) ok = 0;
    free(digit_to_class);
    free(class_to_digit);
    return ok;
}

static int bd_check_collision_congruence(int p, int base)
{
    for (int g = 1; g < p; g++) {
        int direct = 0;
        if (!bin_derangements_collision_count(p, base, g, &direct)) return 0;
        int pointwise_count = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)((long long)g * r % p);
            int x = (int)((long long)base * r % p);
            int gx = (int)((long long)g * x % p);
            int interval_match = bd_digit(r, p, base) == bd_digit(gr, p, base);
            int congruence_match = x % base == gx % base;
            if (interval_match != congruence_match) return 0;
            pointwise_count += congruence_match;
        }
        if (direct != pointwise_count ||
            direct != bd_congruence_collision_count(p, base, g))
            return 0;
    }
    return 1;
}

static int bd_check_c_sides(int p, int base)
{
    unsigned char *seen = calloc((size_t)p, 1);
    if (!seen) return 0;
    int ok = 1;
    for (int g = 2; g < p; g++) {
        int collision = 0;
        int c = bd_c_parameter(p, base, g);
        if (!bin_derangements_collision_count(p, base, g, &collision) ||
            c <= 0 || c == base || seen[c] ||
            bd_normalize((long long)c * (1 - g), p) != base ||
            ((c < base) != (collision == 0)) ||
            ((c > base) != (collision > 0))) {
            ok = 0;
            break;
        }
        seen[c] = 1;
    }
    for (int c = 1; c < p; c++)
        if ((c == base) == (seen[c] != 0)) ok = 0;
    free(seen);
    return ok;
}

static int bd_check_family(int p, int base)
{
    unsigned char *observed = calloc((size_t)p, 1);
    unsigned char *predicted = calloc((size_t)p, 1);
    if (!observed || !predicted) {
        free(observed);
        free(predicted);
        return 0;
    }
    int observed_count = 0;
    int predicted_count = 0;
    for (int g = 1; g < p; g++) {
        int collision = 0;
        bin_derangements_collision_count(p, base, g, &collision);
        if (collision == 0) {
            observed[g] = 1;
            observed_count++;
        }
    }
    for (int u = 1; u < base; u++) {
        int g = bd_family_value(p, base, u);
        if (g <= 0 || predicted[g]) {
            free(observed);
            free(predicted);
            return 0;
        }
        predicted[g] = 1;
        predicted_count++;
    }
    int ok = observed_count == base - 1 && predicted_count == base - 1;
    for (int g = 1; g < p; g++)
        if (observed[g] != predicted[g]) ok = 0;
    free(observed);
    free(predicted);
    return ok;
}

static int bd_check_inverse_pairing(int p, int base)
{
    for (int u = 1; u < base; u++) {
        int g = bd_family_value(p, base, u);
        int partner = bd_family_value(p, base, base - u);
        if ((long long)g * partner % p != 1) return 0;
    }
    if (base % 2 == 0 && bd_family_value(p, base, base / 2) != p - 1)
        return 0;
    return 1;
}

static int bd_check_ratio_set(int p, int base)
{
    unsigned char *ratios = calloc((size_t)p, 1);
    int *inverses = calloc((size_t)p, sizeof(*inverses));
    if (!ratios || !inverses) {
        free(ratios);
        free(inverses);
        return 0;
    }
    for (int r = 1; r < p; r++) inverses[r] = bd_inverse(r, p);
    for (int r = 1; r < p; r++) {
        for (int s = 1; s < p; s++) {
            if (bd_digit(r, p, base) == bd_digit(s, p, base)) {
                int ratio = (int)((long long)s * inverses[r] % p);
                ratios[ratio] = 1;
            }
        }
    }
    int count = 0;
    for (int g = 1; g < p; g++) count += ratios[g] != 0;
    free(ratios);
    free(inverses);
    return count == p - base;
}

static int bd_check_sum_rule(int p, int base)
{
    int *sizes = calloc((size_t)base, sizeof(*sizes));
    if (!sizes) return 0;
    bd_bin_sizes(p, base, sizes);
    long long collision_sum = 0;
    long long square_sum = 0;
    for (int g = 1; g < p; g++) {
        int collision = 0;
        bin_derangements_collision_count(p, base, g, &collision);
        collision_sum += collision;
    }
    for (int d = 0; d < base; d++)
        square_sum += (long long)sizes[d] * sizes[d];
    free(sizes);
    return collision_sum == square_sum;
}

static int bd_constructive_totals(int p, int base,
                                  long long *sum, long long *count)
{
    *sum = 0;
    *count = 0;
    for (int g = 2; g < p; g++) {
        int collision = 0;
        if (!bin_derangements_collision_count(p, base, g, &collision)) return 0;
        if (collision > 0) {
            *sum += collision;
            (*count)++;
        }
    }
    return 1;
}

static int bd_check_mean(int p, int base)
{
    if (p <= base + 1) return 1;
    long long direct_sum = 0;
    long long direct_count = 0;
    long long numerator = 0;
    long long denominator = 0;
    return bd_constructive_totals(p, base, &direct_sum, &direct_count) &&
           bin_derangements_mean_fraction(p, base, &numerator, &denominator) &&
           direct_sum == numerator && direct_count == denominator;
}

static int bd_check_special_ranges(int p, int base)
{
    if (p <= base + 1) return 1;
    long long numerator = 0;
    long long denominator = 0;
    if (!bin_derangements_mean_fraction(p, base, &numerator, &denominator))
        return 0;
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    if (remainder == 0 && numerator != (long long)q * denominator) return 0;
    int mean_is_two = numerator == 2 * denominator;
    int in_range = p > base + 1 && p <= 2 * base + 1;
    int bounded_correction = numerator >= (long long)q * denominator &&
                             numerator <= (long long)(q + 1) * denominator;
    return mean_is_two == in_range && bounded_correction;
}

/* Return -1 outside the primitive-root domain, otherwise return pass/fail. */
static int bd_check_zero_lags(int p, int base)
{
    if (mult_order(base, p) != p - 1) return -1;
    int zero_count = 0;
    for (int lag = 1; lag < p - 1; lag++) {
        int g = bd_power(base, lag, p);
        int collision = 0;
        int word_matches = 0;
        if (!bin_derangements_collision_count(p, base, g, &collision)) return 0;
        for (int j = 0; j < p - 1; j++) {
            int r = bd_power(base, j, p);
            int shifted = bd_power(base, (j + lag) % (p - 1), p);
            if (bd_digit(r, p, base) == bd_digit(shifted, p, base))
                word_matches++;
        }
        if (word_matches != collision) return 0;
        if (collision == 0) zero_count++;
    }
    return zero_count == base - 1;
}

static void bd_print_bins(int p, int base)
{
    for (int digit = 0; digit < base; digit++) {
        printf("  B_%d = {", digit);
        int first = 1;
        for (int r = 1; r < p; r++) {
            if (bd_digit(r, p, base) == digit) {
                printf("%s%d", first ? "" : ",", r);
                first = 0;
            }
        }
        printf("}\n");
    }
}

int bin_derangements_inspect(int p, int base)
{
    if (!bd_valid(p, base, 1)) return 1;
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    int bins = bd_check_bin_distribution(p, base);
    int conjugation = bd_check_conjugation(p, base);
    int congruence = bd_check_collision_congruence(p, base);
    int sides = bd_check_c_sides(p, base);
    int family = bd_check_family(p, base);
    int inverse = bd_check_inverse_pairing(p, base);
    int ratios = bd_check_ratio_set(p, base);
    int sum = bd_check_sum_rule(p, base);
    int mean = bd_check_mean(p, base);
    int ok = bins && conjugation && congruence && sides && family && inverse &&
             ratios && sum && mean;

    printf("Digit-bin zero gate and constructive collision mass\n\n");
    printf("p = %d, base b = %d\n", p, base);
    printf("p - 1 = b*Q + R = %d*%d + %d\n\n", base, q, remainder);
    printf("Digit bins\n");
    bd_print_bins(p, base);
    printf("\nNonidentity multiplier table\n");
    printf("  g     c(g)     C(g)     side\n");
    for (int g = 2; g < p; g++) {
        int collision = 0;
        int c = bd_c_parameter(p, base, g);
        bin_derangements_collision_count(p, base, g, &collision);
        printf("  %-5d %-8d %-8d %s\n", g, c, collision,
               c < base ? "zero" : "positive");
    }
    printf("\nExact checks\n");
    printf("  endpoint-corrected floor sizes and Q/Q+1 distribution %s\n", bins ? "PASS" : "FAIL");
    printf("  r -> [b*r]_p conjugates bins to classes modulo b   %s\n", conjugation ? "PASS" : "FAIL");
    printf("  interval and congruence collision counts agree     %s\n", congruence ? "PASS" : "FAIL");
    printf("  c(g)<b iff C(g)=0; c(g)>b iff C(g)>0               %s\n", sides ? "PASS" : "FAIL");
    printf("  explicit family is exactly the zero set            %s\n", family ? "PASS" : "FAIL");
    printf("  u and b-u give inverse multipliers                  %s\n", inverse ? "PASS" : "FAIL");
    printf("  within-bin ratio-set size is p-b = %d               %s\n", p - base, ratios ? "PASS" : "FAIL");
    printf("  sum_g C(g) equals sum_d |B_d|^2                    %s\n", sum ? "PASS" : "FAIL");
    if (p > base + 1)
        printf("  exact constructive mean formula                     %s\n", mean ? "PASS" : "FAIL");
    else
        printf("  constructive mean requires p>b+1                   not applicable\n");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int bin_derangements_family(int p, int base)
{
    if (!bd_valid(p, base, 1)) return 1;
    int ok = bd_check_family(p, base) && bd_check_inverse_pairing(p, base);

    printf("Bin-deranging multiplier family\n\n");
    printf("g(u) = -u/(b-u) mod p, p=%d, b=%d\n\n", p, base);
    printf("  u     g(u)     g(b-u)     product     C(g)\n");
    for (int u = 1; u < base; u++) {
        int g = bd_family_value(p, base, u);
        int partner = bd_family_value(p, base, base - u);
        int collision = 0;
        bin_derangements_collision_count(p, base, g, &collision);
        printf("  %-5d %-8d %-10d %-11d %d\n", u, g, partner,
               (int)((long long)g * partner % p), collision);
    }
    printf("\nObserved zero set in residue order = {");
    int first = 1;
    for (int g = 1; g < p; g++) {
        int collision = 0;
        bin_derangements_collision_count(p, base, g, &collision);
        if (collision == 0) {
            printf("%s%d", first ? "" : ",", g);
            first = 0;
        }
    }
    printf("}\n");
    printf("gate width = %d; expected b-1 = %d  %s\n", base - 1, base - 1,
           ok ? "PASS" : "FAIL");
    if (base % 2 == 0)
        printf("middle parameter u=b/2 gives -1 mod p = %d  %s\n", p - 1,
               bd_family_value(p, base, base / 2) == p - 1 ? "PASS" : "FAIL");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int bin_derangements_mean(int p, int base)
{
    if (!bd_valid(p, base, 1)) return 1;
    if (p <= base + 1) {
        fprintf(stderr, "constructive mean requires p > base + 1\n");
        return 1;
    }
    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    long long actual_sum = 0;
    long long actual_count = 0;
    long long numerator = 0;
    long long denominator = 0;
    bd_constructive_totals(p, base, &actual_sum, &actual_count);
    bin_derangements_mean_fraction(p, base, &numerator, &denominator);
    int formula = actual_sum == numerator && actual_count == denominator;
    int sum = bd_check_sum_rule(p, base);
    int special = bd_check_special_ranges(p, base);
    int ok = formula && sum && special;

    printf("Mean constructive collision count\n\n");
    printf("p=%d, b=%d, Q=%d, R=%d\n", p, base, q, remainder);
    printf("constructive multipliers = %lld; formula denominator = %lld  %s\n",
           actual_count, denominator, actual_count == denominator ? "PASS" : "FAIL");
    printf("constructive collision mass = %lld; formula numerator = %lld  %s\n",
           actual_sum, numerator, actual_sum == numerator ? "PASS" : "FAIL");
    printf("mean = %lld/%lld = %.12g\n", numerator, denominator,
           (double)numerator / (double)denominator);
    printf("sum_g C(g) = sum_d |B_d|^2  %s\n", sum ? "PASS" : "FAIL");
    printf("mean=2 iff b+1<p<=2b+1 for this instance  %s\n", special ? "PASS" : "FAIL");
    printf("Q <= mean <= Q+1 for this instance         %s\n", special ? "PASS" : "FAIL");
    if (remainder == 0)
        printf("R=0 gives mean Q=%d  %s\n", q,
               numerator == (long long)q * denominator ? "PASS" : "FAIL");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int bin_derangements_lags(int p, int base)
{
    if (!bd_valid(p, base, 1)) return 1;
    int order = mult_order(base, p);
    if (order != p - 1) {
        fprintf(stderr,
                "complete zero-lag identification requires the base to be a primitive root; ord_p(b)=%d, not p-1=%d\n",
                order, p - 1);
        return 1;
    }
    int zero_count = 0;
    int all_equal = 1;
    printf("Primitive-root zero lags\n\n");
    printf("p=%d, b=%d, ord_p(b)=%d=p-1\n", p, base, order);
    printf("  lag     b^lag mod p     R(lag)=C(b^lag)\n");
    for (int lag = 1; lag < p - 1; lag++) {
        int g = bd_power(base, lag, p);
        int collision = 0;
        int word_matches = 0;
        bin_derangements_collision_count(p, base, g, &collision);
        for (int j = 0; j < p - 1; j++) {
            int r = bd_power(base, j, p);
            int shifted = bd_power(base, (j + lag) % (p - 1), p);
            if (bd_digit(r, p, base) == bd_digit(shifted, p, base))
                word_matches++;
        }
        if (word_matches != collision) all_equal = 0;
        if (collision == 0) zero_count++;
        printf("  %-7d %-15d %d%s\n", lag, g, collision,
               collision == 0 ? "  zero" : "");
    }
    int ok = all_equal && zero_count == base - 1;
    printf("\nR(lag)=C([b^lag]_p) at every nonzero lag  %s\n",
           all_equal ? "PASS" : "FAIL");
    printf("zero lags = %d; expected b-1 = %d  %s\n", zero_count, base - 1,
           zero_count == base - 1 ? "PASS" : "FAIL");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int bin_derangements_examples(void)
{
    int passed = 0;
    int collision[13] = {0};
    int expected_zero[] = {2, 3, 4, 5, 7, 8, 9, 10, 12};
    int thirteen = bd_check_family(13, 10);
    for (int g = 1; g < 13; g++)
        bin_derangements_collision_count(13, 10, g, &collision[g]);
    for (size_t i = 0; i < sizeof(expected_zero) / sizeof(expected_zero[0]); i++)
        thirteen = thirteen && collision[expected_zero[i]] == 0;
    thirteen = thirteen && collision[6] == 2 && collision[11] == 2;
    int mean_two = bd_check_mean(13, 10) && bd_check_special_ranges(13, 10);
    int lags = bd_check_zero_lags(17, 10) == 1;
    int r_zero = bd_check_mean(31, 10) && bd_check_special_ranges(31, 10);
    long long numerator = 0;
    long long denominator = 0;
    bin_derangements_mean_fraction(31, 10, &numerator, &denominator);
    r_zero = r_zero && numerator == 3 * denominator;

    printf("Digit-bin zero-gate exact examples\n\n");
    printf("decimal p=13 zero set is {2,3,4,5,7,8,9,10,12}; C(6)=C(11)=2  %s\n",
           thirteen ? "PASS" : "FAIL");
    if (thirteen) passed++;
    printf("decimal p=13 constructive mean is exactly 2  %s\n",
           mean_two ? "PASS" : "FAIL");
    if (mean_two) passed++;
    printf("decimal p=17 primitive-root cycle has nine zero lags  %s\n",
           lags ? "PASS" : "FAIL");
    if (lags) passed++;
    printf("decimal p=31 has R=0 and constructive mean Q=3  %s\n",
           r_zero ? "PASS" : "FAIL");
    if (r_zero) passed++;
    printf("\n%d/4 exact examples passed.\n", passed);
    return passed == 4 ? 0 : 1;
}

int bin_derangements_verify(void)
{
    int bins = 1;
    int conjugation = 1;
    int congruence = 1;
    int c_sides = 1;
    int family = 1;
    int inverse = 1;
    int ratio = 1;
    int sum = 1;
    int mean = 1;
    int special = 1;
    int lags = 1;
    int models = 0;
    int primitive_models = 0;

    for (int base = 2; base <= 16; base++) {
        for (int p = base + 1; p <= 127; p++) {
            if (!bd_is_prime(p)) continue;
            models++;
            bins = bins && bd_check_bin_distribution(p, base);
            conjugation = conjugation && bd_check_conjugation(p, base);
            congruence = congruence && bd_check_collision_congruence(p, base);
            c_sides = c_sides && bd_check_c_sides(p, base);
            family = family && bd_check_family(p, base);
            inverse = inverse && bd_check_inverse_pairing(p, base);
            ratio = ratio && bd_check_ratio_set(p, base);
            sum = sum && bd_check_sum_rule(p, base);
            mean = mean && bd_check_mean(p, base);
            special = special && bd_check_special_ranges(p, base);
            int lag_check = bd_check_zero_lags(p, base);
            if (lag_check >= 0) {
                primitive_models++;
                lags = lags && lag_check;
            }
        }
    }

    int named = bin_derangements_examples() == 0;
    int checks[] = {bins, conjugation, congruence, c_sides, family, inverse,
                    ratio, sum, mean, special, lags, named};
    const char *labels[] = {
        "endpoint floor bins, Q/Q+1 distribution, and square mass",
        "bin-to-residue-class conjugation",
        "direct collision count equals congruence count",
        "zero and positive c(g) sides",
        "explicit deranging family and gate width b-1",
        "inverse pairing and even-base self-inverse element",
        "within-bin ratio-set size p-b",
        "collision sum rule",
        "exact constructive count, mass, and mean formula",
        "R=0, mean-two range, and bounded correction",
        "primitive-root zero-lag identification",
        "named decimal examples"
    };
    int passed = 0;
    printf("\nFinite C verification of digit-bin zero-gate geometry\n");
    printf("Exact integer sweep: %d (base, prime) models; %d primitive-root models.\n\n",
           models, primitive_models);
    for (size_t i = 0; i < sizeof(checks) / sizeof(checks[0]); i++) {
        printf("  %-62s %s\n", labels[i], checks[i] ? "PASS" : "FAIL");
        if (checks[i]) passed++;
    }
    printf("\n%d/12 verification groups passed.\n", passed);
    printf("The sweep checks exact finite instances; the universal identities are proved separately in Lean.\n");
    return passed == 12;
}

void bin_derangements_help(void)
{
    printf(
        "Digit-bin zero gate and constructive collision mass\n\n"
        "Usage:\n"
        "  nfield bin-derangements inspect <p> [--base <b>]\n"
        "  nfield bin-derangements family <p> [--base <b>]\n"
        "  nfield bin-derangements mean <p> [--base <b>]\n"
        "  nfield bin-derangements lags <p> [--base <b>]\n"
        "  nfield bin-derangements examples\n"
        "  nfield bin-derangements verify\n"
        "  nfield verify bin-derangements\n"
        "  nfield help bin-derangements\n\n"
        "The domain is prime p with 2 <= b < p. inspect checks the digit-bin\n"
        "conjugation, collision congruence, c-parameter split, exact zero\n"
        "family, inverse pairing, ratio set, sum rule, and constructive mean.\n"
        "family lists -u/(b-u) modulo p and checks that these are exactly the\n"
        "b-1 collision-free multipliers. mean compares the exact observed\n"
        "constructive mass and count with the exact rational formula.\n"
        "lags is intentionally restricted to bases that are primitive roots,\n"
        "which is exactly the domain of the complete repetend-lag statement.\n\n"
        "All structural comparisons use exact integer arithmetic. The bounded\n"
        "verification sweep is computational evidence for the universal\n"
        "finite-group identities proved separately in Lean, not a replacement proof.\n"
    );
}
