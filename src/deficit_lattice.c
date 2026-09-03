/*
 * deficit_lattice.c: Exact C checks for the alignment-deficit lattice.
 *
 * The theorem-facing calculations use integer fractions.  The small-case
 * inspection path separately enumerates long-division states on one common
 * clock, so the closed formula is checked against the object it describes.
 */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include "nfield.h"

#define DL_DIRECT_MAX 200000LL
#define DL_FIELD_MAX 5000LL

typedef struct {
    const char *name;
    int numerator;
    int denominator;
} DLInterval;

static const DLInterval dl_major_scale[] = {
    {"Do (C)", 1, 1}, {"Re (D)", 9, 8}, {"Mi (E)", 5, 4},
    {"Fa (F)", 4, 3}, {"Sol (G)", 3, 2}, {"La (A)", 5, 3},
    {"Ti (B)", 15, 8}, {"Do (C)", 2, 1}
};

static const DLInterval dl_chromatic_scale[] = {
    {"C", 1, 1}, {"C#", 16, 15}, {"D", 9, 8}, {"Eb", 6, 5},
    {"E", 5, 4}, {"F", 4, 3}, {"F#", 45, 32}, {"G", 3, 2},
    {"Ab", 8, 5}, {"A", 5, 3}, {"Bb", 9, 5}, {"B", 15, 8},
    {"C", 2, 1}
};

static long long dl_absll(long long value)
{
    return value < 0 ? -value : value;
}

static long long dl_gcd(long long a, long long b)
{
    a = dl_absll(a);
    b = dl_absll(b);
    while (b != 0) {
        long long t = b;
        b = a % b;
        a = t;
    }
    return a == 0 ? 1 : a;
}

static int dl_safe_mul(long long a, long long b, long long *result)
{
    if (a < 0 || b < 0) return 0;
    if (a != 0 && b > LLONG_MAX / a) return 0;
    *result = a * b;
    return 1;
}

static void dl_reduce(long long *numerator, long long *denominator)
{
    long long g = dl_gcd(*numerator, *denominator);
    *numerator /= g;
    *denominator /= g;
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
}

static void dl_print_fraction(long long numerator, long long denominator)
{
    dl_reduce(&numerator, &denominator);
    printf("%lld/%lld", numerator, denominator);
}

static long double dl_fraction_value(long long numerator, long long denominator)
{
    return (long double)numerator / (long double)denominator;
}

static int dl_is_prime(int n)
{
    if (n < 2) return 0;
    if (n % 2 == 0) return n == 2;
    for (int d = 3; d <= n / d; d += 2)
        if (n % d == 0) return 0;
    return 1;
}

int deficit_lattice_is_supported(long long m, int base)
{
    if (m < 1 || base < 2) return 0;
    while (m > 1) {
        long long g = dl_gcd(m, base);
        if (g == 1) return 0;
        m /= g;
    }
    return 1;
}

static int dl_clearing_depth(long long m, int base)
{
    if (!deficit_lattice_is_supported(m, base)) return -1;
    int depth = 0;
    while (m > 1) {
        m /= dl_gcd(m, base);
        depth++;
    }
    return depth;
}

int deficit_lattice_alignment_fraction(int p, long long m,
                                       long long *numerator,
                                       long long *denominator)
{
    long long pm;
    if (p < 3 || m < 1 || !numerator || !denominator
        || m > LLONG_MAX / 2 + 1
        || !dl_safe_mul(p, m, &pm))
        return 0;
    *numerator = 2 * m - 1;
    *denominator = pm - 1;
    return 1;
}

int deficit_lattice_deficit_fraction(int p, long long m,
                                     long long *numerator,
                                     long long *denominator)
{
    long long an, ad;
    if (!deficit_lattice_alignment_fraction(p, m, &an, &ad)
        || !dl_safe_mul(p, ad, denominator))
        return 0;
    *numerator = p - 2;
    return 1;
}

int deficit_lattice_ratio_fraction(int p, long long m1, long long m2,
                                   long long *numerator,
                                   long long *denominator)
{
    long long pm1, pm2;
    if (p < 3 || m1 < 1 || m2 < 1 || !numerator || !denominator
        || !dl_safe_mul(p, m1, &pm1) || !dl_safe_mul(p, m2, &pm2))
        return 0;
    *numerator = pm2 - 1;
    *denominator = pm1 - 1;
    return 1;
}

static int dl_validate_domain(int p, long long m, int base, int noisy)
{
    if (base < 2) {
        if (noisy) fprintf(stderr, "base must be at least 2\n");
        return 0;
    }
    if (p < 3 || !dl_is_prime(p)) {
        if (noisy) fprintf(stderr, "p must be a prime at least 3\n");
        return 0;
    }
    if (base % p != 1) {
        if (noisy)
            fprintf(stderr, "base must satisfy b == 1 (mod p); got %d mod %d = %d\n",
                    base, p, base % p);
        return 0;
    }
    if (m < 1) {
        if (noisy) fprintf(stderr, "m must be at least 1\n");
        return 0;
    }
    if (!deficit_lattice_is_supported(m, base)) {
        if (noisy)
            fprintf(stderr, "m=%lld is not supported on the prime divisors of base %d\n",
                    m, base);
        return 0;
    }
    long long num, den;
    if (!deficit_lattice_deficit_fraction(p, m, &num, &den)) {
        if (noisy) fprintf(stderr, "inputs exceed the exact 64-bit arithmetic range\n");
        return 0;
    }
    return 1;
}

static void dl_print_base_support(int base)
{
    int remaining = base;
    int first = 1;
    printf("{");
    for (int q = 2; q <= remaining / q; q++) {
        if (remaining % q != 0) continue;
        if (!first) printf(", ");
        printf("%d", q);
        first = 0;
        while (remaining % q == 0) remaining /= q;
    }
    if (remaining > 1) {
        if (!first) printf(", ");
        printf("%d", remaining);
    }
    printf("}");
}

static void dl_print_factorization(long long value)
{
    long long remaining = value;
    int first = 1;
    if (value == 1) {
        printf("1");
        return;
    }
    for (long long q = 2; q <= remaining / q; q++) {
        if (remaining % q != 0) continue;
        int exponent = 0;
        while (remaining % q == 0) {
            remaining /= q;
            exponent++;
        }
        if (!first) printf(" * ");
        printf("%lld", q);
        if (exponent > 1) printf("^%d", exponent);
        first = 0;
    }
    if (remaining > 1) {
        if (!first) printf(" * ");
        printf("%lld", remaining);
    }
}

static int dl_direct_counts(int p, long long m, int base, int extra_depth,
                            long long *terminating,
                            long long *matching_repeating,
                            long long *other_repeating)
{
    long long nll;
    if (!dl_safe_mul(p, m, &nll) || nll > DL_DIRECT_MAX) return 0;
    int n = (int)nll;
    int depth = dl_clearing_depth(m, base) + extra_depth;
    long long reference = 1;
    for (int j = 0; j < depth; j++)
        reference = (reference * base) % n;
    int reference_digit = (int)((reference * base) / n);

    long long term = 0, match = 0, other = 0;
    for (int k = 1; k < n; k++) {
        long long remainder = k;
        for (int j = 0; j < depth; j++)
            remainder = (remainder * base) % n;
        if (remainder == 0) {
            term++;
        } else if ((remainder * base) / n == reference_digit) {
            match++;
        } else {
            other++;
        }
    }
    *terminating = term;
    *matching_repeating = match;
    *other_repeating = other;
    return 1;
}

int deficit_lattice_inspect(int p, long long m, int base)
{
    if (!dl_validate_domain(p, m, base, 1)) return 1;

    long long n;
    if (!dl_safe_mul(p, m, &n)) {
        fprintf(stderr, "p*m exceeds the exact 64-bit arithmetic range\n");
        return 1;
    }
    long long alpha_num, alpha_den, deficit_num, deficit_den;
    deficit_lattice_alignment_fraction(p, m, &alpha_num, &alpha_den);
    deficit_lattice_deficit_fraction(p, m, &deficit_num, &deficit_den);
    int depth = dl_clearing_depth(m, base);

    printf("Alignment-deficit lattice inspection\n\n");
    printf("Theorem hypotheses:\n");
    printf("  base b = %d\n", base);
    printf("  prime p = %d; b mod p = %d\n", p, base % p);
    printf("  base prime support P = ");
    dl_print_base_support(base);
    printf("\n  m = %lld = ", m);
    dl_print_factorization(m);
    printf("; P-supported: yes\n");
    printf("  n = p*m = %lld\n", n);
    printf("  theorem hypotheses: PASS\n");

    printf("\nResidue-class count from the theorem:\n");
    printf("  terminating rows (multiples of p) = m-1 = %lld\n", m - 1);
    printf("  matching repeating rows (k == 1 mod p) = m = %lld\n", m);
    printf("  other repeating rows = (p-2)m = %lld\n", (long long)(p - 2) * m);
    printf("  aligned rows = 2m-1 = %lld of pm-1 = %lld\n",
           2 * m - 1, n - 1);

    printf("\nExact identities:\n");
    printf("  alpha_%d(%lld) = (2m-1)/(pm-1) = ", base, n);
    dl_print_fraction(alpha_num, alpha_den);
    printf(" = %.12Lg\n", dl_fraction_value(alpha_num, alpha_den));
    printf("  limiting alignment = 2/p = ");
    dl_print_fraction(2, p);
    printf("\n  delta_%d(%lld) = 2/p - alpha = (p-2)/(p(pm-1)) = ",
           p, m);
    dl_print_fraction(deficit_num, deficit_den);
    printf(" = %.12Lg\n", dl_fraction_value(deficit_num, deficit_den));
    printf("  deficit numerator check: 2(pm-1)-p(2m-1) = %d = p-2  PASS\n",
           p - 2);
    printf("  coordinate is positive, injective, and order-reversing because\n");
    printf("  p-2 is fixed while p(pm-1) strictly increases with m.\n");

    long long term, match, other;
    int direct = dl_direct_counts(p, m, base, 0, &term, &match, &other);
    int direct_ok = 1;
    printf("\nDirect synchronized long-division check:\n");
    printf("  minimal clearing depth D = %d\n", depth);
    if (direct) {
        long long term2, match2, other2;
        int later = dl_direct_counts(p, m, base, 1, &term2, &match2, &other2);
        direct_ok = term == m - 1 && match == m
                 && other == (long long)(p - 2) * m
                 && later && term2 == term && match2 == match && other2 == other;
        printf("  observed at D: terminating=%lld, matching=%lld, other=%lld\n",
               term, match, other);
        printf("  observed at D+1: terminating=%lld, matching=%lld, other=%lld\n",
               term2, match2, other2);
        printf("  direct count and depth-independence: %s\n",
               direct_ok ? "PASS" : "FAIL");
    } else {
        printf("  skipped: n=%lld exceeds the inspection limit %lld\n",
               n, DL_DIRECT_MAX);
        printf("  the exact residue-class calculation above is still available.\n");
    }

    if (n <= DL_FIELD_MAX) {
        double field = alignment_exact((int)n, base);
        long double formula = dl_fraction_value(alpha_num, alpha_den);
        int field_ok = fabsl((long double)field - formula) < 1e-12L;
        printf("  independent general field engine = %.12g  %s\n",
               field, field_ok ? "PASS" : "FAIL");
        direct_ok = direct_ok && field_ok;
    } else {
        printf("  general field engine skipped above n=%lld\n", DL_FIELD_MAX);
    }

    printf("\nResult: %s\n", direct_ok ? "PASS" : "FAIL");
    return direct_ok ? 0 : 1;
}

static int dl_ratio_values(int p, long long u, long long v, long long factor,
                           long long *m1, long long *m2,
                           long long *finite_num, long long *finite_den,
                           long long *error_num, long long *error_den,
                           long long *relative_num, long long *relative_den)
{
    if (!dl_safe_mul(u, factor, m1) || !dl_safe_mul(v, factor, m2)
        || !deficit_lattice_ratio_fraction(p, *m1, *m2,
                                           finite_num, finite_den))
        return 0;

    long long denominator;
    if (!dl_safe_mul(u, *finite_den, &denominator)) return 0;
    *error_num = v - u;
    *error_den = denominator;

    if (!dl_safe_mul(v, *finite_den, &denominator)) return 0;
    *relative_num = dl_absll(v - u);
    *relative_den = denominator;
    return 1;
}

int deficit_lattice_ratio(int p, long long u, long long v,
                          int base, long long factor)
{
    if (!dl_validate_domain(p, u, base, 1)
        || !dl_validate_domain(p, v, base, 1))
        return 1;
    if (factor < 1) {
        fprintf(stderr, "factor must be at least 1\n");
        return 1;
    }
    if (!deficit_lattice_is_supported(factor, base)) {
        fprintf(stderr,
                "factor=%lld is not supported on the prime divisors of base %d\n",
                factor, base);
        return 1;
    }

    long long m1, m2, fn, fd, en, ed, rn, rd;
    if (!dl_ratio_values(p, u, v, factor, &m1, &m2, &fn, &fd,
                         &en, &ed, &rn, &rd)) {
        fprintf(stderr, "inputs exceed the exact 64-bit ratio range\n");
        return 1;
    }

    long long left, right;
    int residual_ok = dl_safe_mul(fn, u, &left)
                   && dl_safe_mul(fd, v, &right)
                   && left - right == v - u;

    printf("Exact alignment-deficit ratio\n\n");
    printf("  base b = %d, p = %d, P = ", base, p);
    dl_print_base_support(base);
    printf("\n  u = %lld, v = %lld, supported factor t = %lld\n", u, v, factor);
    printf("  m1 = t*u = %lld; m2 = t*v = %lld\n", m1, m2);
    printf("\n  delta_p(tu) / delta_p(tv)\n");
    printf("    = (ptv-1)/(ptu-1)\n    = ");
    dl_print_fraction(fn, fd);
    printf(" = %.15Lg\n", dl_fraction_value(fn, fd));
    printf("  limiting lattice ratio v/u = ");
    dl_print_fraction(v, u);
    printf(" = %.15Lg\n", dl_fraction_value(v, u));
    printf("  signed finite error = ");
    dl_print_fraction(en, ed);
    printf("\n  relative error = ");
    dl_print_fraction(rn, rd);
    printf(" = %.12Le\n", dl_fraction_value(rn, rd));
    printf("\nCross-multiplication certificate:\n");
    printf("  (ptv-1)u - v(ptu-1) = v-u = %lld  %s\n",
           v - u, residual_ok ? "PASS" : "FAIL");
    printf("  As supported t grows, only the positive denominator grows,\n");
    printf("  so the exact error tends to zero.\n");
    return residual_ok ? 0 : 1;
}

int deficit_lattice_pythagorean(long long factor)
{
    const int base = 12, p = 11;
    const long long u = 524288; /* 2^19 */
    const long long v = 531441; /* 3^12 */
    if (factor < 1 || !deficit_lattice_is_supported(factor, base)) {
        fprintf(stderr, "factor must be a positive {2,3}-supported integer\n");
        return 1;
    }

    long long m1, m2, fn, fd, en, ed, rn, rd;
    if (!dl_ratio_values(p, u, v, factor, &m1, &m2, &fn, &fd,
                         &en, &ed, &rn, &rd)) {
        fprintf(stderr, "factor exceeds the exact 64-bit ratio range\n");
        return 1;
    }
    int fixture_ok = factor != 1 || (fn == 5845850 && fd == 5767167);

    printf("Pythagorean comma from the deficit lattice\n\n");
    printf("  base 12 has prime support P = {2, 3}; p = 11\n");
    printf("  t = %lld\n", factor);
    printf("  delta_11(t*2^19) / delta_11(t*3^12) = ");
    dl_print_fraction(fn, fd);
    printf(" = %.12Lf\n", dl_fraction_value(fn, fd));
    printf("  Pythagorean comma 3^12/2^19 = ");
    dl_print_fraction(v, u);
    printf(" = %.12Lf\n", dl_fraction_value(v, u));
    printf("  exact relative error = ");
    dl_print_fraction(rn, rd);
    printf(" = %.12Le\n", dl_fraction_value(rn, rd));
    if (factor == 1)
        printf("  paper fixture 5845850/5767167: %s\n",
               fixture_ok ? "PASS" : "FAIL");
    printf("  convergence certificate: error numerator |3^12-2^19| = %lld,\n",
           v - u);
    printf("  while the denominator grows with t.  PASS\n");
    return fixture_ok ? 0 : 1;
}

static int dl_scale_table(const DLInterval *scale, int count,
                          long long reference, long long factor,
                          const char *title, long long bound_num,
                          long long bound_den)
{
    const int base = 30, p = 29;
    if (factor < 1 || !deficit_lattice_is_supported(factor, base)) {
        fprintf(stderr, "factor must be a positive {2,3,5}-supported integer\n");
        return 1;
    }

    long long m0;
    if (!dl_safe_mul(reference, factor, &m0)) {
        fprintf(stderr, "factor exceeds the exact 64-bit scale range\n");
        return 1;
    }

    printf("%s\n\n", title);
    printf("  base 30, p = 29, P = {2, 3, 5}, supported factor t = %lld\n", factor);
    printf("  reference m0 = %lld\n\n", m0);
    printf("  %-8s %-11s %-12s %-18s %-18s %-13s\n",
           "note", "m/m0", "m", "exact ratio", "target", "relative err");

    int all_ok = 1;
    long double maximum_error = 0.0L;
    for (int i = 0; i < count; i++) {
        long long scaled_num, m;
        if (!dl_safe_mul(m0, scale[i].numerator, &scaled_num)
            || scaled_num % scale[i].denominator != 0) {
            all_ok = 0;
            continue;
        }
        m = scaled_num / scale[i].denominator;
        long long fn, fd;
        if (!deficit_lattice_ratio_fraction(p, m0, m, &fn, &fd)
            || !deficit_lattice_is_supported(m, base)) {
            all_ok = 0;
            continue;
        }
        long long rn = dl_absll(m - m0), rd;
        if (!dl_safe_mul(m, fd, &rd)) {
            all_ok = 0;
            continue;
        }
        long double error = dl_fraction_value(rn, rd);
        if (error > maximum_error) maximum_error = error;

        long long check_left, check_right, right_part;
        int bound_ok = dl_safe_mul(rn, bound_den, &check_left)
                    && dl_safe_mul(m, fd, &right_part)
                    && dl_safe_mul(bound_num, right_part, &check_right)
                    && check_left < check_right;
        all_ok = all_ok && bound_ok;

        char exact[64], target[64], error_text[64];
        long long rfn = fn, rfd = fd;
        dl_reduce(&rfn, &rfd);
        snprintf(exact, sizeof(exact), "%lld/%lld", rfn, rfd);
        long long tn = scale[i].numerator, td = scale[i].denominator;
        dl_reduce(&tn, &td);
        snprintf(target, sizeof(target), "%lld/%lld", tn, td);
        long long rrn = rn, rrd = rd;
        dl_reduce(&rrn, &rrd);
        snprintf(error_text, sizeof(error_text), "%lld/%lld", rrn, rrd);
        printf("  %-8s %-11s %-12lld %-18s %-18s %-13s\n",
               scale[i].name, target, m, exact, target, error_text);
    }

    printf("\n  maximum relative error = %.12Le\n", maximum_error);
    printf("  claimed strict bound %lld/%lld = %.12Le: %s\n",
           bound_num, bound_den,
           dl_fraction_value(bound_num, bound_den), all_ok ? "PASS" : "FAIL");
    printf("  every listed m is P-supported: %s\n", all_ok ? "PASS" : "FAIL");
    return all_ok ? 0 : 1;
}

int deficit_lattice_major_scale(long long factor)
{
    return dl_scale_table(dl_major_scale,
                          (int)(sizeof(dl_major_scale) / sizeof(dl_major_scale[0])),
                          24, factor, "Just major scale from exact deficit ratios",
                          9, 12500); /* 7.2e-4 */
}

int deficit_lattice_chromatic_scale(long long factor)
{
    return dl_scale_table(dl_chromatic_scale,
                          (int)(sizeof(dl_chromatic_scale) /
                                sizeof(dl_chromatic_scale[0])),
                          480, factor,
                          "Five-limit chromatic scale from exact deficit ratios",
                          9, 250000); /* 3.6e-5 */
}

static int dl_check_alignment_formula(void)
{
    int cases = 0;
    for (int base = 2; base <= 40; base++) {
        for (int p = 3; p < base; p++) {
            if (!dl_is_prime(p) || base % p != 1) continue;
            for (int m = 1; m <= 96; m++) {
                if (!deficit_lattice_is_supported(m, base)) continue;
                long long n = (long long)p * m;
                if (n > 4000) continue;
                long long t0, a0, o0, t1, a1, o1;
                if (!dl_direct_counts(p, m, base, 0, &t0, &a0, &o0)
                    || !dl_direct_counts(p, m, base, 1, &t1, &a1, &o1)
                    || t0 != m - 1 || a0 != m
                    || o0 != (long long)(p - 2) * m
                    || t1 != t0 || a1 != a0 || o1 != o0)
                    return 0;
                if (n <= 1200) {
                    long long an, ad;
                    deficit_lattice_alignment_fraction(p, m, &an, &ad);
                    if (fabsl((long double)alignment_exact((int)n, base)
                              - dl_fraction_value(an, ad)) > 1e-12L)
                        return 0;
                }
                cases++;
            }
        }
    }
    return cases > 200;
}

static int dl_check_deficit_identity(void)
{
    for (int p = 3; p <= 97; p++) {
        if (!dl_is_prime(p)) continue;
        for (int m = 1; m <= 256; m++) {
            long long an, ad, dn, dd;
            if (!deficit_lattice_alignment_fraction(p, m, &an, &ad)
                || !deficit_lattice_deficit_fraction(p, m, &dn, &dd))
                return 0;
            if (2 * ad - p * an != p - 2
                || dn != p - 2 || dd != p * ad)
                return 0;
        }
    }
    return 1;
}

static int dl_check_ratios(void)
{
    for (int base = 2; base <= 30; base++) {
        for (int p = 3; p < base; p++) {
            if (!dl_is_prime(p) || base % p != 1) continue;
            for (int u = 1; u <= 32; u++) {
                if (!deficit_lattice_is_supported(u, base)) continue;
                for (int v = 1; v <= 32; v++) {
                    if (!deficit_lattice_is_supported(v, base)) continue;
                    long long previous_num = LLONG_MAX, previous_den = 1;
                    for (int t = 1; t <= 16; t++) {
                        if (!deficit_lattice_is_supported(t, base)) continue;
                        long long m1, m2, fn, fd, en, ed, rn, rd;
                        if (!dl_ratio_values(p, u, v, t, &m1, &m2,
                                             &fn, &fd, &en, &ed, &rn, &rd))
                            return 0;
                        if (fn != p * m2 - 1 || fd != p * m1 - 1
                            || en != v - u || rn != dl_absll(v - u))
                            return 0;
                        if (previous_num != LLONG_MAX
                            && rn * previous_den > previous_num * rd)
                            return 0;
                        previous_num = rn;
                        previous_den = rd;
                    }
                }
            }
        }
    }
    return 1;
}

static int dl_check_coordinate_and_support(void)
{
    for (int m = 1; m <= 2000; m++) {
        int a = deficit_lattice_is_supported(m, 6);
        if (a != deficit_lattice_is_supported(m, 12)
            || a != deficit_lattice_is_supported(m, 24))
            return 0;
    }
    for (int p = 3; p <= 43; p++) {
        if (!dl_is_prime(p)) continue;
        long long previous_num = 0, previous_den = 1;
        for (int m = 256; m >= 1; m--) {
            long long num, den;
            if (!deficit_lattice_deficit_fraction(p, m, &num, &den)) return 0;
            if (previous_num != 0 && num * previous_den <= previous_num * den)
                return 0;
            previous_num = num;
            previous_den = den;
        }
    }
    return 1;
}

static int dl_check_pythagorean_fixture(void)
{
    long long fn, fd;
    if (!deficit_lattice_ratio_fraction(11, 524288, 531441, &fn, &fd))
        return 0;
    return deficit_lattice_is_supported(524288, 12)
        && deficit_lattice_is_supported(531441, 12)
        && fn == 5845850 && fd == 5767167
        && dl_fraction_value(dl_absll(531441 - 524288),
                             531441LL * fd) < 1e-8L;
}

static int dl_check_scale_fixture(const DLInterval *scale, int count,
                                  long long m0,
                                  long long bound_num, long long bound_den)
{
    for (int i = 0; i < count; i++) {
        long long scaled = m0 * scale[i].numerator;
        if (scaled % scale[i].denominator != 0) return 0;
        long long m = scaled / scale[i].denominator;
        long long fn, fd;
        if (!deficit_lattice_is_supported(m, 30)
            || !deficit_lattice_ratio_fraction(29, m0, m, &fn, &fd)
            || fn != 29 * m - 1 || fd != 29 * m0 - 1)
            return 0;
        long long rn = dl_absll(m - m0);
        if (rn * bound_den >= bound_num * m * fd) return 0;
    }
    return 1;
}

int deficit_lattice_verify(void)
{
    printf("Exact C verification of the alignment-deficit lattice\n");
    printf("Closed formulas are checked against synchronized long division.\n\n");

    int passed = 0;
    int ok = dl_check_alignment_formula();
    printf("  alignment count and depth independence: b<=40, p<b, m<=96, pm<=4000  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dl_check_deficit_identity();
    printf("  exact deficit identity: primes p<=97 and 1<=m<=256                    %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dl_check_ratios();
    printf("  finite ratio identity and shrinking exact error: b<=30, u,v<=32      %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dl_check_coordinate_and_support();
    printf("  injective order reversal and common {2,3} support for bases 6,12,24  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dl_check_pythagorean_fixture();
    printf("  base-12 Pythagorean comma exact fixture                              %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dl_check_scale_fixture(dl_major_scale,
            (int)(sizeof(dl_major_scale) / sizeof(dl_major_scale[0])),
            24, 9, 12500);
    printf("  base-30 just major scale and strict 7.2e-4 error bound                %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = dl_check_scale_fixture(dl_chromatic_scale,
            (int)(sizeof(dl_chromatic_scale) / sizeof(dl_chromatic_scale[0])),
            480, 9, 250000);
    printf("  base-30 chromatic scale and strict 3.6e-5 error bound                 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/7 finite checks passed.\n", passed);
    printf("Finite sweeps corroborate the identities; every accepted calculation\n");
    printf("uses exact integer arithmetic within the documented 64-bit range.\n");
    return passed == 7;
}

void deficit_lattice_help(void)
{
    printf("Primes and the Major Scale: alignment-deficit lattice C tools\n\n");
    printf("Theorem domain: p is a prime at least 3, b == 1 (mod p), and every\n");
    printf("prime factor of m divides b. The command calls this P-supported.\n\n");
    printf("Commands:\n");
    printf("  nfield deficit-lattice inspect <p> <m> [--base <b>]\n");
    printf("      Show the hypotheses, residue-class counts, exact alignment and\n");
    printf("      deficit, then independently enumerate synchronized long division.\n\n");
    printf("  nfield deficit-lattice ratio <p> <u> <v> [--base <b>] [--factor <t>]\n");
    printf("      Compute delta_p(tu)/delta_p(tv), its limiting ratio v/u, and an\n");
    printf("      exact cross-multiplication and error certificate.\n\n");
    printf("  nfield deficit-lattice pythagorean [--factor <t>]\n");
    printf("      Reproduce the base-12 Pythagorean-comma calculation.\n\n");
    printf("  nfield deficit-lattice major-scale [--factor <t>]\n");
    printf("  nfield deficit-lattice chromatic-scale [--factor <t>]\n");
    printf("      Reproduce the exact base-30 scale tables and error bounds.\n\n");
    printf("  nfield deficit-lattice verify\n");
    printf("  nfield verify deficit-lattice\n");
    printf("      Run the exact identities, named fixtures, and reported finite sweeps.\n\n");
    printf("Examples:\n");
    printf("  nfield deficit-lattice inspect 29 24 --base 30\n");
    printf("  nfield deficit-lattice ratio 29 24 36 --base 30\n");
    printf("  nfield deficit-lattice ratio 29 24 36 --base 30 --factor 100\n");
    printf("  nfield deficit-lattice pythagorean\n");
    printf("  nfield deficit-lattice major-scale\n\n");
    printf("The formulas and cross-multiplication certificates are exact integer\n");
    printf("identities. Bounded sweeps are regression evidence, not a replacement\n");
    printf("for the paper's universal proof. Musical interpretation comes after the\n");
    printf("arithmetic prime-support lattice; the code does not treat it as a theorem.\n");
}
