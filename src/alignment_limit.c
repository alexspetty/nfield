/*
 * alignment_limit.c: Exact coset correction and alignment-limit tools.
 *
 * The finite formula is evaluated with integer arithmetic.  Direct field
 * evaluation is used as a separate comparison in the inspector and verifier.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <limits.h>
#include "nfield.h"

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

typedef struct {
    int p;
    int m;
    int base;
    int n;
    int minimum_depth;
    int depth;
    int order;
    int start;
    int bin_square_sum;
    int coset_bin_sum;
    int q;
    int r;
    int max_bin;
    int equidistributed;
    int *bins;
    int *coset;
    long long exact_num;
    long long exact_den;
    long long baseline_num;
    long long baseline_den;
    long long correction_num;
    long long correction_den;
    long long limit_num;
    long long limit_den;
} AlignmentData;

static long long al_gcdll(long long a, long long b)
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

static int al_gcd(int a, int b)
{
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a < 0 ? -a : a;
}

static int al_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0)
            return 0;
    return 1;
}

static int al_clearing_depth(int m, int base)
{
    int depth = 0;
    if (m < 1 || base < 2) return -1;
    while (m > 1) {
        int g = al_gcd(m, base);
        if (g == 1) return -1;
        m /= g;
        depth++;
    }
    return depth;
}

static int al_power_mod(int base, int exponent, int modulus)
{
    long long result = 1;
    long long factor = base % modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * factor % modulus;
        factor = factor * factor % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int al_inverse_mod_prime(int value, int p)
{
    return al_power_mod(value, p - 2, p);
}

static int al_order(int base, int p)
{
    if (al_gcd(base, p) != 1) return 0;
    int value = base % p;
    int order = 1;
    while (value != 1 && order < p) {
        value = (int)(((long long)value * base) % p);
        order++;
    }
    return value == 1 ? order : 0;
}

static void al_reduce(long long *numerator, long long *denominator)
{
    long long g = al_gcdll(*numerator, *denominator);
    *numerator /= g;
    *denominator /= g;
}

static void al_print_fraction(long long numerator, long long denominator)
{
    al_reduce(&numerator, &denominator);
    printf("%lld/%lld", numerator, denominator);
}

static int al_build(int p, int m, int base, int requested_depth,
                    AlignmentData *data)
{
    memset(data, 0, sizeof(*data));
    if (!al_is_prime(p) || m < 1 || base < 2 || base % p == 0)
        return 0;
    if ((long long)p * m > INT_MAX) return 0;

    int minimum_depth = al_clearing_depth(m, base);
    if (minimum_depth < 0) return 0;
    int depth = requested_depth < 0 ? minimum_depth : requested_depth;
    if (depth < minimum_depth) return 0;

    int order = al_order(base, p);
    if (order <= 0) return 0;

    int *bins = calloc((size_t)base, sizeof(int));
    int *coset = calloc((size_t)order, sizeof(int));
    if (!bins || !coset) {
        free(bins);
        free(coset);
        return 0;
    }

    for (int residue = 1; residue < p; residue++) {
        int digit = (int)(((long long)base * residue) / p);
        bins[digit]++;
    }

    int S = 0;
    int max_bin = 0;
    for (int digit = 0; digit < base; digit++) {
        S += bins[digit] * bins[digit];
        if (bins[digit] > max_bin) max_bin = bins[digit];
    }

    int start = (int)(((long long)al_power_mod(base, depth, p)
                       * al_inverse_mod_prime(m % p, p)) % p);
    int state = start;
    int T = 0;
    for (int i = 0; i < order; i++) {
        coset[i] = state;
        int digit = (int)(((long long)base * state) / p);
        T += bins[digit];
        state = (int)(((long long)state * base) % p);
    }

    data->p = p;
    data->m = m;
    data->base = base;
    data->n = p * m;
    data->minimum_depth = minimum_depth;
    data->depth = depth;
    data->order = order;
    data->start = start;
    data->bin_square_sum = S;
    data->coset_bin_sum = T;
    data->q = (p - 1) / base;
    data->r = (p - 1) % base;
    data->max_bin = max_bin;
    data->equidistributed =
        (long long)T * (p - 1) == (long long)order * S;
    data->bins = bins;
    data->coset = coset;

    data->exact_num = (long long)(m - 1) * order + (long long)m * T;
    data->exact_den = (long long)order * ((long long)p * m - 1);
    data->baseline_num = 2LL * m - 1;
    data->baseline_den = (long long)p * m - 1;
    data->correction_num = (long long)m * (T - order);
    data->correction_den = (long long)order * ((long long)p * m - 1);
    data->limit_num = order + T;
    data->limit_den = (long long)p * order;
    return 1;
}

static void al_free(AlignmentData *data)
{
    free(data->bins);
    free(data->coset);
    data->bins = NULL;
    data->coset = NULL;
}

static void al_print_bins(const AlignmentData *data)
{
    printf("  bin sizes n_d:");
    if (data->base <= 64) {
        for (int digit = 0; digit < data->base; digit++)
            printf(" %d:%d", digit, data->bins[digit]);
    } else {
        int occupied = 0;
        for (int digit = 0; digit < data->base; digit++)
            if (data->bins[digit] > 0) occupied++;
        printf(" %d occupied of %d; maximum size %d",
               occupied, data->base, data->max_bin);
    }
    printf("\n");
}

static void al_print_coset_states(const AlignmentData *data)
{
    int shown = data->order < 80 ? data->order : 80;
    printf("  selected coset states:");
    for (int i = 0; i < shown; i++) printf(" %d", data->coset[i]);
    if (shown < data->order) printf(" ... (%d states total)", data->order);
    printf("\n");

    printf("  state contributions r:digit/bin-size:");
    for (int i = 0; i < shown; i++) {
        int state = data->coset[i];
        int digit = (int)(((long long)data->base * state) / data->p);
        printf(" %d:%d/%d", state, digit, data->bins[digit]);
    }
    if (shown < data->order) printf(" ...");
    printf("\n");
}

static void al_print_fourier_energy(const AlignmentData *data)
{
    long long exact_total = (long long)data->base * data->bin_square_sum;
    printf("  exact Fourier energy sum_j |n_hat(j)|^2 = %lld\n", exact_total);
    printf("  normalized Fourier energy = %lld/%d = %d\n",
           exact_total, data->base, data->bin_square_sum);

    if (data->base <= 1024) {
        long double numerical_total = 0.0L;
        for (int j = 0; j < data->base; j++) {
            long double real_part = 0.0L;
            long double imag_part = 0.0L;
            for (int digit = 0; digit < data->base; digit++) {
                long double angle = 2.0L * (long double)M_PI * j * digit
                                  / data->base;
                real_part += data->bins[digit] * cosl(angle);
                imag_part += data->bins[digit] * sinl(angle);
            }
            numerical_total += real_part * real_part
                             + imag_part * imag_part;
        }
        printf("  direct DFT check: (1/b) energy = %.12Lf; error = %.3Le\n",
               numerical_total / data->base,
               fabsl(numerical_total / data->base
                     - data->bin_square_sum));
    }
}

int alignment_limit_inspect(int p, int m, int base, int depth)
{
    if (!al_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (m < 1 || base < 2) {
        fprintf(stderr, "m must be positive and base must be at least 2\n");
        return 1;
    }
    int minimum_depth = al_clearing_depth(m, base);
    if (minimum_depth < 0) {
        fprintf(stderr, "m=%d is not supported on the prime factors of base %d\n",
                m, base);
        return 1;
    }
    if ((long long)p * m > INT_MAX) {
        fprintf(stderr, "p*m exceeds the supported integer range\n");
        return 1;
    }

    printf("Exact synchronized alignment limit data\n\n");
    printf("  p = %d\n  m = %d\n  n = p*m = %d\n  base = %d\n",
           p, m, p * m, base);

    if (base % p == 0) {
        double measured = alignment_exact(p * m, base);
        printf("\nThe prime divides the base, so n is base-supported.\n");
        printf("Every fraction terminates and alignment = 1.\n");
        printf("comparison with synchronized field = %s (%.12g)\n",
               fabs(measured - 1.0) < 1e-12 ? "PASS" : "FAIL", measured);
        return fabs(measured - 1.0) < 1e-12 ? 0 : 1;
    }

    if (depth >= 0 && depth < minimum_depth) {
        fprintf(stderr, "depth %d is too early; use --depth %d or greater\n",
                depth, minimum_depth);
        return 1;
    }

    AlignmentData data;
    if (!al_build(p, m, base, depth, &data)) {
        fprintf(stderr, "could not construct alignment-limit data\n");
        return 1;
    }

    printf("\nCommon clock and coset:\n");
    printf("  minimal clearing depth = %d\n", data.minimum_depth);
    printf("  chosen clearing depth t = %d\n", data.depth);
    printf("  multiplicative order L = %d\n", data.order);
    printf("  selected coset start u = %d\n", data.start);
    al_print_coset_states(&data);

    printf("\nDigit bins and collisions:\n");
    al_print_bins(&data);
    printf("  p - 1 = b*q + r = %d*%d + %d\n",
           base, data.q, data.r);
    printf("  bin square sum S = %d\n", data.bin_square_sum);
    printf("  closed form b*q^2 + r*(2q+1) = %d\n",
           base * data.q * data.q + data.r * (2 * data.q + 1));
    printf("  coset bin sum T(C) = %d\n", data.coset_bin_sum);
    printf("  expected bin size for one uniform remainder = ");
    al_print_fraction(data.bin_square_sum, p - 1);
    printf("\n  collision probability for two uniform remainders = ");
    al_print_fraction(data.bin_square_sum, (long long)(p - 1) * (p - 1));
    printf("\n");
    al_print_fourier_energy(&data);

    printf("\nFinite alignment:\n");
    printf("  terminating contribution = m - 1 = %d\n", m - 1);
    printf("  nonterminating contribution = m*T/L = %d*%d/%d\n",
           m, data.coset_bin_sum, data.order);
    printf("  collision-free baseline = ");
    al_print_fraction(data.baseline_num, data.baseline_den);
    printf("\n  correction = ");
    al_print_fraction(data.correction_num, data.correction_den);
    printf("\n  exact alignment = ");
    al_print_fraction(data.exact_num, data.exact_den);
    printf(" = %.12g\n", (double)data.exact_num / data.exact_den);

    double measured = alignment_exact(data.n, base);
    double predicted = (double)data.exact_num / data.exact_den;
    printf("  synchronized field measurement = %.12g\n", measured);
    printf("  comparison with synchronized field = %s\n",
           fabs(measured - predicted) < 1e-12 ? "PASS" : "FAIL");

    printf("\nLimit selected by this coset:\n  (L + T)/(pL) = ");
    al_print_fraction(data.limit_num, data.limit_den);
    printf(" = %.12g\n", (double)data.limit_num / data.limit_den);
    printf("  selected coset equidistributed by bin sum: %s\n",
           data.equidistributed ? "yes" : "no");
    if (data.equidistributed) {
        printf("  closed-form limit (p-1+S)/(p(p-1)) = ");
        al_print_fraction((p - 1) + data.bin_square_sum,
                          (long long)p * (p - 1));
        printf("\n");
    }

    printf("\nSharp-bound status:\n");
    if (p >= 5) {
        int c = ((p - 1) + base - 1) / base;
        long long margin_num = 3 * data.exact_den - 5 * data.exact_num;
        long long margin_den = 5 * data.exact_den;
        printf("  maximum bin size c = ceil((p-1)/b) = %d\n", c);
        printf("  finite margin 3/5 - alignment = ");
        al_print_fraction(margin_num, margin_den);
        printf("\n  finite alignment < 3/5: %s\n",
               margin_num > 0 ? "yes" : "NO");
        printf("  coset limit <= 3/5: %s\n",
               5 * data.limit_num <= 3 * data.limit_den ? "yes" : "NO");
    } else if (p == 2) {
        printf("  p=2 is degenerate: alignment is one in every base.\n");
    } else {
        double golden = (sqrt(5.0) - 1.0) / 2.0;
        printf("  the uniform p>=5 bound does not apply to p=3.\n");
        printf("  finite alignment %s 1/phi (1/phi = %.12g).\n",
               predicted >= golden ? "is at or above" : "is below", golden);
    }

    int ok = fabs(measured - predicted) < 1e-12;
    al_free(&data);
    return ok ? 0 : 1;
}

static int al_collect_cosets(int p, int base, int print_rows,
                             int *all_equidistributed,
                             long long *subgroup_num,
                             long long *subgroup_den,
                             long long *other_num,
                             long long *other_den,
                             int *coset_count_out)
{
    int order = al_order(base, p);
    int *bins = calloc((size_t)base, sizeof(int));
    int *visited = calloc((size_t)p, sizeof(int));
    if (!bins || !visited || order <= 0) {
        free(bins);
        free(visited);
        return 0;
    }

    for (int residue = 1; residue < p; residue++)
        bins[(int)(((long long)base * residue) / p)]++;
    int S = 0;
    for (int digit = 0; digit < base; digit++) S += bins[digit] * bins[digit];

    int all_eq = 1;
    int coset_count = 0;
    long long first_other_n = 0, first_other_d = 1;
    if (print_rows)
        printf("  representative  T(C)  equidist  coset limit       states\n");

    for (int representative = 1; representative < p; representative++) {
        if (visited[representative]) continue;
        int state = representative;
        int T = 0;
        int contains_one = 0;
        int shown = 0;
        int states[80];
        for (int i = 0; i < order; i++) {
            visited[state] = 1;
            if (state == 1) contains_one = 1;
            int digit = (int)(((long long)base * state) / p);
            T += bins[digit];
            if (shown < 80) states[shown++] = state;
            state = (int)(((long long)state * base) % p);
        }

        int eq = (long long)T * (p - 1) == (long long)order * S;
        if (!eq) all_eq = 0;
        long long ln = order + T;
        long long ld = (long long)p * order;
        long long reduced_n = ln, reduced_d = ld;
        al_reduce(&reduced_n, &reduced_d);
        if (contains_one) {
            *subgroup_num = reduced_n;
            *subgroup_den = reduced_d;
        } else if (first_other_n == 0
                   && (reduced_n != *subgroup_num
                       || reduced_d != *subgroup_den)) {
            first_other_n = reduced_n;
            first_other_d = reduced_d;
        }

        if (print_rows) {
            printf("  %-14d  %-4d  %-8s  %lld/%-11lld ",
                   representative, T, eq ? "yes" : "no",
                   reduced_n, reduced_d);
            for (int i = 0; i < shown; i++) printf("%s%d", i ? "," : "", states[i]);
            if (shown < order) printf(",...");
            if (contains_one) printf("  <H>");
            printf("\n");
        }
        coset_count++;
    }

    if (first_other_n != 0) {
        *other_num = first_other_n;
        *other_den = first_other_d;
    } else {
        *other_num = *subgroup_num;
        *other_den = *subgroup_den;
    }
    *all_equidistributed = all_eq;
    *coset_count_out = coset_count;
    free(bins);
    free(visited);
    return 1;
}

int alignment_limit_cosets(int p, int base)
{
    if (!al_is_prime(p) || base < 2) {
        fprintf(stderr, "p must be prime and base must be at least 2\n");
        return 1;
    }
    if (base % p == 0) {
        printf("p=%d divides base %d; this is the terminating case, with alignment one.\n",
               p, base);
        return 0;
    }

    int order = al_order(base, p);
    int count_expected = (p - 1) / order;
    printf("Alignment-limit cosets for p=%d in base %d\n", p, base);
    printf("multiplicative order L=%d; %d multiplicative cosets\n\n",
           order, count_expected);

    int all_eq = 0, count = 0;
    long long subgroup_n = 0, subgroup_d = 1, other_n = 0, other_d = 1;
    if (!al_collect_cosets(p, base, 1, &all_eq,
                           &subgroup_n, &subgroup_d,
                           &other_n, &other_d, &count)) {
        fprintf(stderr, "could not enumerate cosets\n");
        return 1;
    }

    printf("\nall cosets equidistributed: %s\n", all_eq ? "yes" : "no");
    if (all_eq) {
        printf("unique alignment limit: %lld/%lld\n", subgroup_n, subgroup_d);
    } else {
        printf("subgroup alignment limit: %lld/%lld\n", subgroup_n, subgroup_d);
        printf("another alignment limit: %lld/%lld\n", other_n, other_d);
    }
    return count == count_expected ? 0 : 1;
}

int alignment_limit_table(int base, int max_prime)
{
    if (base < 2 || max_prime < 3) {
        fprintf(stderr, "base must be at least 2 and max-prime at least 3\n");
        return 1;
    }

    printf("Alignment-limit table in base %d\n", base);
    printf("The value column shows the subgroup limit; alternatives are listed when present.\n\n");
    printf("  p     L       S  equidist  subgroup limit    decimal       alternative\n");

    for (int p = 3; p <= max_prime; p++) {
        if (!al_is_prime(p) || base % p == 0) continue;
        int bins_sum = 0;
        int *bins = calloc((size_t)base, sizeof(int));
        if (!bins) return 1;
        for (int residue = 1; residue < p; residue++)
            bins[(int)(((long long)base * residue) / p)]++;
        for (int digit = 0; digit < base; digit++) bins_sum += bins[digit] * bins[digit];
        free(bins);

        int all_eq = 0, count = 0;
        long long sn = 0, sd = 1, on = 0, od = 1;
        if (!al_collect_cosets(p, base, 0, &all_eq, &sn, &sd,
                               &on, &od, &count)) return 1;
        printf("  %-5d %-7d %-3d %-9s %lld/%-14lld %.10f",
               p, al_order(base, p), bins_sum, all_eq ? "yes" : "no",
               sn, sd, (double)sn / sd);
        if (!all_eq && (sn != on || sd != od))
            printf(" %lld/%lld", on, od);
        printf("\n");
    }
    return 0;
}

int alignment_limit_sharpness(int steps)
{
    if (steps < 1 || steps > 30) {
        fprintf(stderr, "steps must be between 1 and 30\n");
        return 1;
    }

    printf("Sharpness family: p=5, base=2, m=2^a\n");
    printf("Exact alignment is (3m-1)/(5m-1); finite values are strictly below 3/5.\n\n");
    printf("  a          m       exact alignment       decimal        gap to 3/5\n");
    long long m = 1;
    for (int a = 0; a < steps; a++) {
        long long numerator = 3 * m - 1;
        long long denominator = 5 * m - 1;
        long long gap_n = 3 * denominator - 5 * numerator;
        long long gap_d = 5 * denominator;
        long long rn = numerator, rd = denominator;
        al_reduce(&rn, &rd);
        printf("  %-10d %-7lld %lld/%-16lld %.12f  ",
               a, m, rn, rd, (double)numerator / denominator);
        al_print_fraction(gap_n, gap_d);
        printf("\n");
        m *= 2;
    }
    printf("\nlimiting supremum = 3/5\n");
    return 0;
}

/* Exact aggregate score numerator on a denominator-n long-division clock. */
static long long al_direct_score_numerator(int p, int m, int base,
                                           int depth, int order)
{
    int n = p * m;
    long long total = 0;
    for (int k = 1; k < n; k++) {
        if (k % p == 0) {
            total += order;
            continue;
        }
        int reference = 1;
        int row = k;
        for (int i = 0; i < depth; i++) {
            reference = (int)(((long long)base * reference) % n);
            row = (int)(((long long)base * row) % n);
        }
        for (int i = 0; i < order; i++) {
            int reference_digit = (int)(((long long)base * reference) / n);
            int row_digit = (int)(((long long)base * row) / n);
            if (reference_digit == row_digit) total++;
            reference = (int)(((long long)base * reference) % n);
            row = (int)(((long long)base * row) % n);
        }
    }
    return total;
}

static int al_check_bins_and_fourier(void)
{
    for (int base = 2; base <= 32; base++) {
        for (int p = 2; p <= 127; p++) {
            if (!al_is_prime(p) || base % p == 0) continue;
            int *bins = calloc((size_t)base, sizeof(int));
            if (!bins) return 0;
            for (int residue = 1; residue < p; residue++)
                bins[(int)(((long long)base * residue) / p)]++;
            int S = 0, large = 0, max_bin = 0;
            int q = (p - 1) / base;
            int r = (p - 1) % base;
            for (int digit = 0; digit < base; digit++) {
                S += bins[digit] * bins[digit];
                if (bins[digit] > max_bin) max_bin = bins[digit];
                if (bins[digit] == q + 1) large++;
                else if (bins[digit] != q) {
                    free(bins);
                    return 0;
                }
            }
            int formula = base * q * q + r * (2 * q + 1);
            long long collision_pairs = 0;
            for (int x = 1; x < p; x++)
                for (int y = 1; y < p; y++)
                    if (((long long)base * x) / p
                        == ((long long)base * y) / p)
                        collision_pairs++;

            long double numerical_energy = 0.0L;
            for (int j = 0; j < base; j++) {
                long double real_part = 0.0L, imag_part = 0.0L;
                for (int digit = 0; digit < base; digit++) {
                    long double angle = 2.0L * (long double)M_PI
                                      * j * digit / base;
                    real_part += bins[digit] * cosl(angle);
                    imag_part += bins[digit] * sinl(angle);
                }
                numerical_energy += real_part * real_part
                                  + imag_part * imag_part;
            }
            free(bins);
            if (large != r || S != formula
                || collision_pairs != S
                || ((max_bin <= 1) != (p <= base + 1))
                || (p <= base + 1 && S != p - 1)
                || fabsl(numerical_energy / base - S) > 1e-8L)
                return 0;
        }
    }
    return 1;
}

static int al_check_exact_formula(void)
{
    for (int base = 2; base <= 16; base++) {
        for (int p = 2; p <= 31; p++) {
            if (!al_is_prime(p) || base % p == 0) continue;
            for (int m = 1; m <= 24; m++) {
                if (al_clearing_depth(m, base) < 0) continue;
                AlignmentData data;
                if (!al_build(p, m, base, -1, &data)) return 0;
                long long direct = al_direct_score_numerator(
                    p, m, base, data.depth, data.order);
                double field = alignment_exact(p * m, base);
                double formula = (double)data.exact_num / data.exact_den;
                int ok = direct == data.exact_num
                      && fabs(field - formula) < 1e-12;
                al_free(&data);
                if (!ok) return 0;
            }
        }
    }

    /* If p divides the base, p*m remains supported and every row terminates. */
    for (int base = 2; base <= 16; base++)
        for (int p = 2; p <= base; p++) {
            if (!al_is_prime(p) || base % p != 0) continue;
            for (int m = 1; m <= 24; m++) {
                if (al_clearing_depth(m, base) < 0) continue;
                if (fabs(alignment_exact(p * m, base) - 1.0) > 1e-12)
                    return 0;
            }
        }

    AlignmentData one_digit, odd_base_two;
    if (!al_build(3, 4, 4, -1, &one_digit)
        || !al_build(2, 3, 3, -1, &odd_base_two))
        return 0;
    int edge_fixtures_ok = one_digit.order == 1
                        && one_digit.coset_bin_sum == 1
                        && one_digit.exact_num == 7
                        && one_digit.exact_den == 11
                        && odd_base_two.order == 1
                        && odd_base_two.coset_bin_sum == 1
                        && odd_base_two.exact_num == odd_base_two.exact_den;
    al_free(&one_digit);
    al_free(&odd_base_two);
    if (!edge_fixtures_ok) return 0;
    return 1;
}

static int al_check_correction(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int p = 2; p <= 67; p++) {
            if (!al_is_prime(p) || base % p == 0) continue;
            for (int m = 1; m <= 32; m++) {
                if (al_clearing_depth(m, base) < 0) continue;
                AlignmentData data;
                if (!al_build(p, m, base, -1, &data)) return 0;
                int all_singleton = 1;
                for (int i = 0; i < data.order; i++) {
                    int state = data.coset[i];
                    int digit = (int)(((long long)base * state) / p);
                    if (data.bins[digit] != 1) all_singleton = 0;
                }
                int correction_zero = data.coset_bin_sum == data.order;
                int ok = data.coset_bin_sum >= data.order
                      && correction_zero == all_singleton;
                al_free(&data);
                if (!ok) return 0;
            }
        }
    }

    AlignmentData zero_case, positive_case;
    if (!al_build(17, 3, 15, -1, &zero_case)
        || !al_build(53, 2, 10, -1, &positive_case))
        return 0;
    int fixtures_ok = zero_case.coset_bin_sum == zero_case.order
                   && positive_case.coset_bin_sum == 69
                   && positive_case.coset_bin_sum > positive_case.order;
    al_free(&zero_case);
    al_free(&positive_case);
    if (!fixtures_ok) return 0;
    return 1;
}

static int al_check_depth_independence(void)
{
    for (int base = 2; base <= 16; base++) {
        for (int p = 2; p <= 43; p++) {
            if (!al_is_prime(p) || base % p == 0) continue;
            for (int m = 1; m <= 24; m++) {
                int depth = al_clearing_depth(m, base);
                if (depth < 0) continue;
                AlignmentData first, next;
                if (!al_build(p, m, base, depth, &first)
                    || !al_build(p, m, base, depth + 1, &next))
                    return 0;
                long long direct_first = al_direct_score_numerator(
                    p, m, base, depth, first.order);
                long long direct_next = al_direct_score_numerator(
                    p, m, base, depth + 1, next.order);
                int ok = first.coset_bin_sum == next.coset_bin_sum
                      && first.exact_num == next.exact_num
                      && direct_first == direct_next;
                al_free(&first);
                al_free(&next);
                if (!ok) return 0;
            }
        }
    }
    return 1;
}

static int al_check_coset_limits(void)
{
    int exceptions[4] = {53, 73, 79, 89};
    int found[4] = {0, 0, 0, 0};
    for (int p = 3; p < 100; p++) {
        if (!al_is_prime(p) || p == 5) continue;
        int all_eq = 0, count = 0;
        long long sn = 0, sd = 1, on = 0, od = 1;
        if (!al_collect_cosets(p, 10, 0, &all_eq, &sn, &sd,
                               &on, &od, &count)) return 0;
        AlignmentData subgroup;
        if (!al_build(p, 1, 10, 0, &subgroup)) return 0;
        long long closed_num = (p - 1) + subgroup.bin_square_sum;
        long long closed_den = (long long)p * (p - 1);
        al_reduce(&closed_num, &closed_den);
        int global_formula_ok = !all_eq
            || (sn == closed_num && sd == closed_den);
        int coset_count_ok = count == (p - 1) / subgroup.order;
        al_free(&subgroup);
        if (!global_formula_ok || !coset_count_ok) return 0;
        int expected_exception = 0;
        for (int i = 0; i < 4; i++)
            if (p == exceptions[i]) {
                expected_exception = 1;
                found[i] = 1;
            }
        if (all_eq == expected_exception) return 0;
    }
    for (int i = 0; i < 4; i++) if (!found[i]) return 0;

    int all_eq = 0, count = 0;
    long long sn = 0, sd = 1, on = 0, od = 1;
    if (!al_collect_cosets(53, 10, 0, &all_eq, &sn, &sd,
                           &on, &od, &count)) return 0;
    if (all_eq || count != 4 || sn != 80 || sd != 689
        || on != 82 || od != 689)
        return 0;

    unsigned long long first_four_masks[4] = {0, 0, 0, 0};
    for (int a = 0; a < 8; a++) {
        AlignmentData data;
        int m = 1 << a;
        if (!al_build(53, m, 10, -1, &data)) return 0;
        unsigned long long mask = 0;
        for (int i = 0; i < data.order; i++)
            mask |= 1ULL << data.coset[i];
        long long ln = data.limit_num, ld = data.limit_den;
        al_reduce(&ln, &ld);
        int expected_T = (a % 2 == 0) ? 67 : 69;
        int expected_limit_num = (a % 2 == 0) ? 80 : 82;
        int ok = data.depth == a
              && data.start == al_power_mod(5, a, 53)
              && data.coset_bin_sum == expected_T
              && ln == expected_limit_num && ld == 689;
        if (a < 4) first_four_masks[a] = mask;
        else ok = ok && mask == first_four_masks[a % 4];
        al_free(&data);
        if (!ok) return 0;
    }
    for (int i = 0; i < 4; i++)
        for (int j = i + 1; j < 4; j++)
            if (first_four_masks[i] == first_four_masks[j]) return 0;

    AlignmentData representative_two;
    if (!al_build(53, 5, 10, -1, &representative_two)) return 0;
    unsigned long long representative_two_mask = 0;
    for (int i = 0; i < representative_two.order; i++)
        representative_two_mask |= 1ULL << representative_two.coset[i];
    int named_cosets_ok = representative_two.start == 2
                       && representative_two.coset_bin_sum == 69
                       && representative_two_mask == first_four_masks[3];
    al_free(&representative_two);
    return named_cosets_ok;
}

static int al_check_table(void)
{
    static const int primes[] =
        {3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
    static const int orders[] =
        {1, 6, 2, 6, 16, 18, 22, 28, 15, 3, 5, 21, 46, 13, 58, 60};
    static const int sums[] =
        {2, 6, 10, 16, 28, 34, 50, 80, 90, 132, 160, 178, 214, 272, 338, 360};
    static const long long nums[] =
        {2, 2, 2, 7, 11, 26, 36, 27, 4, 14, 5, 110, 130, 80, 198, 7};
    static const long long dens[] =
        {3, 7, 11, 39, 68, 171, 253, 203, 31, 111, 41, 903, 1081, 689, 1711, 61};
    static const int rounded_four_places[] =
        {6667, 2857, 1818, 1795, 1618, 1520, 1423, 1330,
         1290, 1261, 1220, 1218, 1203, 1161, 1157, 1148};

    for (int i = 0; i < 16; i++) {
        int p = primes[i];
        AlignmentData subgroup;
        if (!al_build(p, 1, 10, 0, &subgroup)) return 0;
        long long ln = subgroup.limit_num, ld = subgroup.limit_den;
        al_reduce(&ln, &ld);
        int all_eq = 0, count = 0;
        long long sn = 0, sd = 1, on = 0, od = 1;
        if (!al_collect_cosets(p, 10, 0, &all_eq, &sn, &sd,
                               &on, &od, &count)) {
            al_free(&subgroup);
            return 0;
        }
        int rounded = (int)((10000 * ln + ld / 2) / ld);
        int ok = subgroup.order == orders[i]
              && subgroup.bin_square_sum == sums[i]
              && ln == nums[i] && ld == dens[i]
              && rounded == rounded_four_places[i]
              && all_eq == (p != 53)
              && sn == nums[i] && sd == dens[i]
              && count == (p - 1) / orders[i]
              && (p != 53 || (on == 82 && od == 689));
        al_free(&subgroup);
        if (!ok) return 0;
    }
    return 1;
}

static int al_check_sharp_bound(void)
{
    for (int base = 2; base <= 24; base++) {
        for (int p = 5; p <= 97; p++) {
            if (!al_is_prime(p) || base % p == 0) continue;
            int all_eq = 0, count = 0;
            long long sn = 0, sd = 1, on = 0, od = 1;
            if (!al_collect_cosets(p, base, 0, &all_eq, &sn, &sd,
                                   &on, &od, &count)) return 0;

            int order = al_order(base, p);
            int *visited = calloc((size_t)p, sizeof(int));
            int *bins = calloc((size_t)base, sizeof(int));
            if (!visited || !bins) {
                free(visited); free(bins); return 0;
            }
            for (int residue = 1; residue < p; residue++)
                bins[(int)(((long long)base * residue) / p)]++;
            for (int rep = 1; rep < p; rep++) {
                if (visited[rep]) continue;
                int state = rep, T = 0;
                for (int i = 0; i < order; i++) {
                    visited[state] = 1;
                    int digit = (int)(((long long)base * state) / p);
                    T += bins[digit];
                    state = (int)(((long long)state * base) % p);
                }
                if (5LL * (order + T) > 3LL * p * order) {
                    free(visited); free(bins); return 0;
                }
            }
            free(visited);
            free(bins);

            for (int m = 1; m <= 48; m++) {
                if (al_clearing_depth(m, base) < 0) continue;
                AlignmentData data;
                if (!al_build(p, m, base, -1, &data)) return 0;
                int c = ((p - 1) + base - 1) / base;
                long long envelope_num = (long long)m - 1 + (long long)m * c;
                long long envelope_den = (long long)p * m - 1;
                long long strict_difference =
                    (long long)(1 + c) * envelope_den
                    - (long long)p * envelope_num;
                int ok = data.max_bin == c
                      && data.coset_bin_sum <= data.order * c
                      && data.exact_num * envelope_den
                         <= envelope_num * data.exact_den
                      && strict_difference == p - 1 - c
                      && strict_difference > 0
                      && 2 * (1 + c) <= p + 1
                      && 5 * (p + 1) <= 6 * p
                      && 5 * data.exact_num < 3 * data.exact_den;
                al_free(&data);
                if (!ok) return 0;
            }
        }
    }

    for (int exponent = 0; exponent <= 20; exponent++) {
        int m = 1 << exponent;
        long long numerator = 3LL * m - 1;
        long long denominator = 5LL * m - 1;
        AlignmentData data;
        if (!al_build(5, m, 2, -1, &data)) return 0;
        int ok = data.order == 4 && data.coset_bin_sum == 8
              && data.exact_num * denominator
                 == numerator * data.exact_den
              && 3 * data.exact_den - 5 * data.exact_num
                 == 2 * data.order
              && 5 * numerator < 3 * denominator;
        al_free(&data);
        if (!ok) return 0;
    }
    return 45 < 49; /* 3*sqrt(5) < 7, hence 3/5 < 1/phi. */
}

int alignment_limit_verify(void)
{
    printf("Exact alignment-limit verification\n");
    printf("The finite formula and direct synchronized clocks are checked independently.\n\n");

    int passed = 0;
    int ok = al_check_bins_and_fourier();
    printf("  bin counts, collision normalization, Fourier energy: bases 2..32, p<=127  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = al_check_exact_formula();
    printf("  exact coset formula incl. p=2/base divisors: bases 2..16, p<=31       %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = al_check_correction();
    printf("  nonnegative correction and singleton equality: bases 2..20, p<=67    %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = al_check_depth_independence();
    printf("  clearing-depth independence: bases 2..16, p<=43, m<=24                %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = al_check_coset_limits();
    printf("  base-10 cosets below 100, named p=53 values and period-four cycle     %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = al_check_table();
    printf("  exact base-10 table, equidistribution flags and roundings through 61   %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    ok = al_check_sharp_bound();
    printf("  finite < 3/5, golden certificate, coset limits and sharp family        %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/7 finite checks passed.\n", passed);
    printf("Finite verification is evidence, not the universal proof.\n");
    return passed == 7;
}

void alignment_limit_help(void)
{
    printf("Alignment-limit tools\n\n");
    printf("For n=p*m, these commands evaluate the exact synchronized alignment\n");
    printf("on one common long-division clock. Here p is prime and m is supported\n");
    printf("on the prime factors of the base. Above the digit-partition boundary,\n");
    printf("digit collisions produce a nonnegative coset correction.\n\n");
    printf("The verifier checks coset enumeration, exceptional base-ten primes,\n");
    printf("displayed values, and the sharpness family across stated finite ranges.\n\n");
    printf("Commands:\n");
    printf("  nfield alignment-limit inspect <p> <m> [--base <b>] [--depth <t>]\n");
    printf("      Show the selected clearing coset, bins, T(C), baseline, exact\n");
    printf("      correction, finite alignment, limit, Fourier energy, collision\n");
    printf("      probability, and sharp-bound margin.\n\n");
    printf("  nfield alignment-limit cosets <p> [--base <b>]\n");
    printf("      Enumerate every multiplicative coset and its subsequential limit;\n");
    printf("      report whether all cosets have equidistributed bin sum.\n\n");
    printf("  nfield alignment-limit table [--base <b>] [--max-prime <P>]\n");
    printf("      Compute prime orders, bin energies, equidistribution status, and\n");
    printf("      subgroup and alternative limits.\n\n");
    printf("  nfield alignment-limit sharpness [--steps <N>]\n");
    printf("      Follow p=5, base=2, m=2^a: every finite value is below 3/5,\n");
    printf("      while 3/5 is the optimal limiting supremum.\n\n");
    printf("  nfield alignment-limit verify\n");
    printf("  nfield verify alignment-limit\n");
    printf("      Run independent exact finite checks and print their ranges.\n\n");
    printf("Examples:\n");
    printf("  nfield alignment-limit inspect 53 2 --base 10\n");
    printf("  nfield alignment-limit cosets 53 --base 10\n");
    printf("  nfield alignment-limit inspect 5 32 --base 2\n\n");
    printf("Finite verification is evidence, not the universal proof.\n");
}
