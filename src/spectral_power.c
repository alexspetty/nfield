/*
 * spectral_power.c
 *
 * Additive digit-bin spectral power on Z/pZ.  The defining transform uses
 * the intrinsic digit coordinate; multiplicative orbit order is separate.
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

#define SPECTRAL_POWER_MAX_PRIME 997
#define SPECTRAL_POWER_MAX_BASE 1000

static int spectral_power_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int spectral_power_valid(int p, int base, int report)
{
    if (!spectral_power_is_prime(p)) {
        if (report) fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (p > SPECTRAL_POWER_MAX_PRIME) {
        if (report)
            fprintf(stderr, "prime must not exceed %d\n",
                    SPECTRAL_POWER_MAX_PRIME);
        return 0;
    }
    if (base < 2) {
        if (report) fprintf(stderr, "base must be at least 2\n");
        return 0;
    }
    if (base > SPECTRAL_POWER_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must not exceed %d\n",
                    SPECTRAL_POWER_MAX_BASE);
        return 0;
    }
    if (base % p == 0) {
        if (report) fprintf(stderr, "p must not divide the base\n");
        return 0;
    }
    return 1;
}

static int ceil_div_ll(long long numerator, int denominator)
{
    return (int)((numerator + denominator - 1) / denominator);
}

int spectral_power_bin_sizes(int p, int base, int *sizes,
                             int capacity, int *count)
{
    if (!spectral_power_valid(p, base, 0) || !sizes || !count ||
        capacity < base)
        return 0;

    memset(sizes, 0, (size_t)base * sizeof(*sizes));
    for (int r = 1; r < p; r++) {
        int digit = (int)(((long long)base * r) / p);
        sizes[digit]++;
    }
    *count = base;
    return 1;
}

int spectral_power_values(int p, int base, double *values,
                          int capacity, int *count)
{
    if (!spectral_power_valid(p, base, 0) || !values || !count ||
        capacity < p)
        return 0;

    double *real = calloc((size_t)base, sizeof(*real));
    double *imag = calloc((size_t)base, sizeof(*imag));
    if (!real || !imag) {
        free(real);
        free(imag);
        return 0;
    }

    for (int k = 0; k < p; k++) {
        memset(real, 0, (size_t)base * sizeof(*real));
        memset(imag, 0, (size_t)base * sizeof(*imag));
        for (int r = 1; r < p; r++) {
            int digit = (int)(((long long)base * r) / p);
            double angle = -2.0 * M_PI * k * r / (double)p;
            real[digit] += cos(angle);
            imag[digit] += sin(angle);
        }
        double power = 0.0;
        for (int digit = 0; digit < base; digit++)
            power += real[digit] * real[digit]
                   + imag[digit] * imag[digit];
        values[k] = power;
    }

    free(real);
    free(imag);
    *count = p;
    return 1;
}

int spectral_power_overlap_values(int p, int base, int *values,
                                  int capacity, int *count)
{
    if (!spectral_power_valid(p, base, 0) || !values || !count ||
        capacity < p)
        return 0;

    int *digit = malloc((size_t)p * sizeof(*digit));
    if (!digit) return 0;
    digit[0] = -1;
    for (int r = 1; r < p; r++)
        digit[r] = (int)(((long long)base * r) / p);

    for (int h = 0; h < p; h++) {
        int overlap = 0;
        for (int r = 0; r < p; r++) {
            int shifted = r + h;
            if (shifted >= p) shifted -= p;
            if (digit[r] >= 0 && digit[r] == digit[shifted]) overlap++;
        }
        values[h] = overlap;
    }

    free(digit);
    *count = p;
    return 1;
}

int spectral_power_triangular_values(int p, int base, int *values,
                                     int capacity, int *count)
{
    if (!spectral_power_valid(p, base, 0) || !values || !count ||
        capacity < p)
        return 0;

    int q = (p - 1) / base;
    int rho = (p - 1) % base;
    for (int h = 0; h < p; h++) {
        int distance = h < p - h ? h : p - h;
        int small = q - distance;
        int large = q + 1 - distance;
        if (small < 0) small = 0;
        if (large < 0) large = 0;
        values[h] = (base - rho) * small + rho * large;
    }
    *count = p;
    return 1;
}

static double interval_kernel(int p, int n, int k)
{
    if (n == 0) return 0.0;
    if (k == 0) return (double)n * n;
    double numerator = sin(M_PI * k * n / (double)p);
    double denominator = sin(M_PI * k / (double)p);
    double ratio = numerator / denominator;
    return ratio * ratio;
}

static void two_length_values(int p, int base, double *values)
{
    int q = (p - 1) / base;
    int rho = (p - 1) % base;
    for (int k = 0; k < p; k++)
        values[k] = (base - rho) * interval_kernel(p, q, k)
                  + rho * interval_kernel(p, q + 1, k);
}

static int consecutive_bins_hold(int p, int base, const int *sizes)
{
    for (int digit = 0; digit < base; digit++) {
        int lower = ceil_div_ll((long long)digit * p, base);
        int upper = ceil_div_ll((long long)(digit + 1) * p, base) - 1;
        if (lower < 1) lower = 1;
        if (upper > p - 1) upper = p - 1;
        int expected = upper >= lower ? upper - lower + 1 : 0;
        if (sizes[digit] != expected) return 0;
        for (int r = lower; r <= upper; r++)
            if (((long long)base * r) / p != digit) return 0;
    }
    return 1;
}

static int two_lengths_hold(int p, int base, const int *sizes)
{
    int q = (p - 1) / base;
    int rho = (p - 1) % base;
    int small = 0, large = 0;
    for (int digit = 0; digit < base; digit++) {
        if (sizes[digit] == q) small++;
        else if (sizes[digit] == q + 1) large++;
        else return 0;
    }
    return small == base - rho && large == rho;
}

static double maximum_difference(const double *left, const double *right,
                                 int count)
{
    double maximum = 0.0;
    for (int i = 0; i < count; i++) {
        double difference = fabs(left[i] - right[i]);
        if (difference > maximum) maximum = difference;
    }
    return maximum;
}

static double overlap_transform_error(int p, const int *overlap,
                                      const double *power)
{
    double maximum = 0.0;
    for (int k = 0; k < p; k++) {
        double real = 0.0, imag = 0.0;
        for (int h = 0; h < p; h++) {
            double angle = -2.0 * M_PI * k * h / (double)p;
            real += overlap[h] * cos(angle);
            imag += overlap[h] * sin(angle);
        }
        double difference = hypot(real - power[k], imag);
        if (difference > maximum) maximum = difference;
    }
    return maximum;
}

static double overlap_inverse_error(int p, const int *overlap,
                                    const double *power)
{
    double maximum = 0.0;
    for (int h = 0; h < p; h++) {
        double real = 0.0, imag = 0.0;
        for (int k = 0; k < p; k++) {
            double angle = 2.0 * M_PI * k * h / (double)p;
            real += power[k] * cos(angle);
            imag += power[k] * sin(angle);
        }
        double difference = hypot(real / p - overlap[h], imag / p);
        if (difference > maximum) maximum = difference;
    }
    return maximum;
}

static int power_is_flat(int p, const double *power)
{
    for (int k = 0; k < p; k++)
        if (fabs(power[k] - (p - 1)) > 1e-8 * p) return 0;
    return 1;
}

static int bins_are_injective(int base, const int *sizes)
{
    for (int digit = 0; digit < base; digit++)
        if (sizes[digit] > 1) return 0;
    return 1;
}

static int inspect_arrays(int p, int base, int **sizes_out,
                          double **direct_out, double **formula_out,
                          int **overlap_out)
{
    int *sizes = calloc((size_t)base, sizeof(*sizes));
    double *direct = calloc((size_t)p, sizeof(*direct));
    double *formula = calloc((size_t)p, sizeof(*formula));
    int *overlap = calloc((size_t)p, sizeof(*overlap));
    int count = 0;
    if (!sizes || !direct || !formula || !overlap ||
        !spectral_power_bin_sizes(p, base, sizes, base, &count) ||
        !spectral_power_values(p, base, direct, p, &count) ||
        !spectral_power_overlap_values(p, base, overlap, p, &count)) {
        free(sizes);
        free(direct);
        free(formula);
        free(overlap);
        return 0;
    }
    two_length_values(p, base, formula);
    *sizes_out = sizes;
    *direct_out = direct;
    *formula_out = formula;
    *overlap_out = overlap;
    return 1;
}

int spectral_power_inspect(int p, int base)
{
    if (!spectral_power_valid(p, base, 1)) return 1;

    int *sizes = NULL, *overlap = NULL;
    double *direct = NULL, *formula = NULL;
    if (!inspect_arrays(p, base, &sizes, &direct, &formula, &overlap)) {
        fprintf(stderr, "unable to allocate the spectral-power calculation\n");
        return 1;
    }
    int *triangular = calloc((size_t)p, sizeof(*triangular));
    int triangular_count = 0;
    if (!triangular ||
        !spectral_power_triangular_values(p, base, triangular, p,
                                          &triangular_count)) {
        fprintf(stderr, "unable to allocate the triangular-profile calculation\n");
        free(sizes); free(direct); free(formula); free(overlap);
        free(triangular);
        return 1;
    }

    int q = (p - 1) / base;
    int rho = (p - 1) % base;
    int phi_zero = 0;
    for (int digit = 0; digit < base; digit++)
        phi_zero += sizes[digit] * sizes[digit];
    int closed_zero = base * q * q + rho * (2 * q + 1);

    printf("Additive digit-bin spectral power\n");
    printf("p = %d, base = %d\n", p, base);
    printf("p is prime and does not divide the base  PASS\n\n");
    printf("Intrinsic coordinate E(r) = e_floor(br/p), with E(0) = 0\n");
    printf("p - 1 = b*q + rho gives q = %d and rho = %d\n\n", q, rho);

    printf("Consecutive digit bins\n");
    printf("%7s %13s %8s\n", "digit", "remainder set", "size");
    for (int digit = 0; digit < base; digit++) {
        int lower = ceil_div_ll((long long)digit * p, base);
        int upper = ceil_div_ll((long long)(digit + 1) * p, base) - 1;
        if (lower < 1) lower = 1;
        if (upper > p - 1) upper = p - 1;
        if (upper >= lower)
            printf("%7d %5d..%-5d %8d\n", digit, lower, upper,
                   sizes[digit]);
        else
            printf("%7d %13s %8d\n", digit, "empty", sizes[digit]);
    }
    printf("consecutive-bin endpoint formula  %s\n",
           consecutive_bins_hold(p, base, sizes) ? "PASS" : "FAIL");
    printf("%d bins of size %d and %d bins of size %d  %s\n\n",
           base - rho, q, rho, q + 1,
           two_lengths_hold(p, base, sizes) ? "PASS" : "FAIL");

    printf("Additive Fourier power\n");
    printf("%5s %18s %18s %13s\n",
           "k", "definition", "two-length", "difference");
    for (int k = 0; k < p; k++)
        printf("%5d %18.10f %18.10f %13.3g\n", k, direct[k],
               formula[k], fabs(direct[k] - formula[k]));

    double formula_error = maximum_difference(direct, formula, p);
    double total = 0.0;
    for (int k = 0; k < p; k++) total += direct[k];
    double parseval_target = (double)p * (p - 1);
    double transform_error = overlap_transform_error(p, overlap, direct);
    double inverse_error = overlap_inverse_error(p, overlap, direct);
    int overlap_sum = 0;
    for (int h = 0; h < p; h++) overlap_sum += overlap[h];
    int profile_ok = triangular_count == p;
    for (int h = 0; h < p && profile_ok; h++)
        if (overlap[h] != triangular[h]) profile_ok = 0;
    int injective = bins_are_injective(base, sizes);
    int boundary = p <= base + 1;
    int flat = power_is_flat(p, direct);

    printf("\nPhi(0) = sum n_d^2 = %d\n", phi_zero);
    printf("b*q^2 + rho*(2q+1) = %d  %s\n", closed_zero,
           phi_zero == closed_zero ? "PASS" : "FAIL");
    printf("two-length formula maximum numerical error = %.3g  %s\n",
           formula_error, formula_error <= 1e-8 * p ? "PASS" : "FAIL");
    printf("sum_k Phi(k) = %.12g; p(p-1) = %.12g  %s\n", total,
           parseval_target,
           fabs(total - parseval_target) <= 1e-8 * p * p ? "PASS" : "FAIL");
    printf("sum_h C_add(h) = %d; Phi(0) = %d  %s\n", overlap_sum, phi_zero,
           overlap_sum == phi_zero ? "PASS" : "FAIL");
    printf("exact two-triangular additive profile  %s\n",
           profile_ok ? "PASS" : "FAIL");
    printf("DFT of direct additive collision count matches Phi, max error %.3g  %s\n",
           transform_error, transform_error <= 1e-8 * p ? "PASS" : "FAIL");
    printf("inverse DFT of Phi matches C_add, max error %.3g  %s\n",
           inverse_error, inverse_error <= 1e-8 * p ? "PASS" : "FAIL");
    printf("digit map injective = %s\n", injective ? "yes" : "no");
    printf("p <= b+1 = %s\n", boundary ? "yes" : "no");
    printf("Phi is constant at p-1 = %s\n", flat ? "yes" : "no");
    printf("injective iff p<=b+1 iff Phi is constant  %s\n",
           injective == boundary && boundary == flat ? "PASS" : "FAIL");

    int ok = consecutive_bins_hold(p, base, sizes)
          && two_lengths_hold(p, base, sizes)
          && phi_zero == closed_zero
          && formula_error <= 1e-8 * p
          && fabs(total - parseval_target) <= 1e-8 * p * p
          && overlap_sum == phi_zero
          && profile_ok
          && transform_error <= 1e-8 * p
          && inverse_error <= 1e-8 * p
          && injective == boundary && boundary == flat;
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");

    free(sizes);
    free(direct);
    free(formula);
    free(overlap);
    free(triangular);
    return ok ? 0 : 1;
}

int spectral_power_overlap(int p, int base)
{
    if (!spectral_power_valid(p, base, 1)) return 1;

    int *sizes = NULL, *overlap = NULL;
    double *direct = NULL, *formula = NULL;
    if (!inspect_arrays(p, base, &sizes, &direct, &formula, &overlap)) {
        fprintf(stderr, "unable to allocate the additive-overlap calculation\n");
        return 1;
    }
    int *triangular = calloc((size_t)p, sizeof(*triangular));
    int triangular_count = 0;
    if (!triangular ||
        !spectral_power_triangular_values(p, base, triangular, p,
                                          &triangular_count)) {
        fprintf(stderr, "unable to allocate the triangular-profile calculation\n");
        free(sizes); free(direct); free(formula); free(overlap);
        free(triangular);
        return 1;
    }

    int phi_zero = 0, overlap_sum = 0;
    for (int digit = 0; digit < base; digit++)
        phi_zero += sizes[digit] * sizes[digit];
    for (int h = 0; h < p; h++) overlap_sum += overlap[h];
    double error = overlap_transform_error(p, overlap, direct);
    double inverse_error = overlap_inverse_error(p, overlap, direct);
    int profile_ok = triangular_count == p;
    for (int h = 0; h < p && profile_ok; h++)
        if (overlap[h] != triangular[h]) profile_ok = 0;

    printf("Additive digit-bin overlap\n");
    printf("p = %d, base = %d\n\n", p, base);
    printf("C_add(h) counts equal digit labels after additive shift h\n");
    printf("The zero coordinate contributes nothing\n\n");
    printf("%5s %10s %12s\n", "h", "direct", "triangular");
    for (int h = 0; h < p; h++)
        printf("%5d %10d %12d\n", h, overlap[h], triangular[h]);
    printf("\nC_add(0) = %d; p-1 = %d  %s\n", overlap[0], p - 1,
           overlap[0] == p - 1 ? "PASS" : "FAIL");
    printf("sum_h C_add(h) = %d; Phi(0) = %d  %s\n", overlap_sum, phi_zero,
           overlap_sum == phi_zero ? "PASS" : "FAIL");
    printf("C_add(h) = (b-rho)(q-t)_+ + rho(q+1-t)_+  %s\n",
           profile_ok ? "PASS" : "FAIL");
    printf("DFT_h C_add(h) equals Phi(k), maximum numerical error %.3g  %s\n",
           error, error <= 1e-8 * p ? "PASS" : "FAIL");
    printf("C_add(h) equals normalized inverse DFT of Phi, max error %.3g  %s\n",
           inverse_error, inverse_error <= 1e-8 * p ? "PASS" : "FAIL");
    printf("\nResult  %s\n",
           overlap[0] == p - 1 && overlap_sum == phi_zero && profile_ok &&
           error <= 1e-8 * p && inverse_error <= 1e-8 * p ? "PASS" : "FAIL");

    int ok = overlap[0] == p - 1 && overlap_sum == phi_zero
          && profile_ok && error <= 1e-8 * p && inverse_error <= 1e-8 * p;
    free(sizes);
    free(direct);
    free(formula);
    free(overlap);
    free(triangular);
    return ok ? 0 : 1;
}

int spectral_power_examples(void)
{
    int sizes[13] = {0}, count = 0;
    int overlap13[13] = {0}, triangular13[13] = {0};
    double power13[13] = {0.0};
    double power8[7] = {0.0}, power10[7] = {0.0};
    int expected[] = {1, 1, 1, 2, 1, 1, 2, 1, 1, 1};
    int bins_ok = spectral_power_bin_sizes(13, 10, sizes, 13, &count)
               && count == 10;
    for (int d = 0; d < 10 && bins_ok; d++)
        if (sizes[d] != expected[d]) bins_ok = 0;

    int values_ok = spectral_power_values(13, 10, power13, 13, &count);
    double cosine_sum = 0.0, total = 0.0;
    int formula_ok = values_ok;
    for (int k = 0; k < 13; k++) {
        total += power13[k];
        if (k > 0) {
            double c = cos(M_PI * k / 13.0);
            cosine_sum += c * c;
            double expected_power = 8.0 + 8.0 * c * c;
            if (fabs(power13[k] - expected_power) > 1e-9)
                formula_ok = 0;
        }
    }
    int phi_zero_ok = values_ok && fabs(power13[0] - 16.0) < 1e-9;
    int cosine_ok = fabs(cosine_sum - 5.5) < 1e-10;
    int total_ok = fabs(total - 156.0) < 1e-9;
    int profile_ok = spectral_power_overlap_values(13, 10, overlap13, 13,
                                                    &count)
                  && spectral_power_triangular_values(13, 10, triangular13,
                                                       13, &count);
    for (int h = 0; h < 13 && profile_ok; h++) {
        int expected_overlap = h == 0 ? 12 : (h == 1 || h == 12 ? 2 : 0);
        if (overlap13[h] != triangular13[h] ||
            overlap13[h] != expected_overlap)
            profile_ok = 0;
    }

    int flat8_ok = spectral_power_values(7, 8, power8, 7, &count)
                && power_is_flat(7, power8);
    int flat10_ok = spectral_power_values(7, 10, power10, 7, &count)
                 && power_is_flat(7, power10);
    int spectra_same = 1;
    for (int k = 0; k < 7; k++)
        if (fabs(power8[k] - power10[k]) > 1e-10) spectra_same = 0;
    int order8 = mult_order(8, 7);
    int order10 = mult_order(10, 7);
    int separation_ok = flat8_ok && flat10_ok && spectra_same
                     && order8 == 1 && order10 == 6;

    printf("Spectral-power exact examples and numerical Fourier checks\n\n");
    printf("Decimal prime thirteen\n");
    printf("bin sizes = 1 1 1 2 1 1 2 1 1 1  %s\n",
           bins_ok ? "PASS" : "FAIL");
    printf("q = 1 and rho = 2  %s\n", bins_ok ? "PASS" : "FAIL");
    printf("Phi(0) = 16  %s\n", phi_zero_ok ? "PASS" : "FAIL");
    printf("Phi(k) = 8 + 8 cos^2(pi*k/13) for nonzero k  %s\n",
           formula_ok ? "PASS" : "FAIL");
    printf("sum of cosine squares for k=1..12 = 11/2  %s\n",
           cosine_ok ? "PASS" : "FAIL");
    printf("sum_k Phi(k) = 156  %s\n\n", total_ok ? "PASS" : "FAIL");
    printf("additive profile = 12 2 0 0 0 0 0 0 0 0 0 0 2  %s\n\n",
           profile_ok ? "PASS" : "FAIL");

    printf("Flat magnitude does not determine multiplicative order\n");
    printf("p=7, base=8 has Phi(k)=6 and order 1  %s\n",
           flat8_ok && order8 == 1 ? "PASS" : "FAIL");
    printf("p=7, base=10 has Phi(k)=6 and order 6  %s\n",
           flat10_ok && order10 == 6 ? "PASS" : "FAIL");
    printf("same additive power with different multiplicative orders  %s\n",
           separation_ok ? "PASS" : "FAIL");
    printf("The orders are contrasting data and are not inputs to Phi\n");

    int ok = bins_ok && phi_zero_ok && formula_ok && cosine_ok && total_ok
          && profile_ok && separation_ok;
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int spectral_power_verify(void)
{
    int checks = 0, passed = 0;
    int consecutive_ok = 1, lengths_ok = 1, formula_ok = 1;
    int parseval_ok = 1, profile_ok = 1, overlap_ok = 1, flatness_ok = 1;

    printf("Finite C verification of digit-bin spectral power\n");
    printf("Sweep domain: 2 <= base <= 24, prime p <= 97, p does not divide base\n");
    printf("Integer checks are exact. Fourier comparisons use tolerance 1e-8 times p.\n\n");

    for (int base = 2; base <= 24; base++) {
        for (int p = 2; p <= 97; p++) {
            if (!spectral_power_is_prime(p) || base % p == 0) continue;
            int *sizes = calloc((size_t)base, sizeof(*sizes));
            double *direct = calloc((size_t)p, sizeof(*direct));
            double *formula = calloc((size_t)p, sizeof(*formula));
            int *overlap = calloc((size_t)p, sizeof(*overlap));
            int *triangular = calloc((size_t)p, sizeof(*triangular));
            int count = 0;
            if (!sizes || !direct || !formula || !overlap || !triangular ||
                !spectral_power_bin_sizes(p, base, sizes, base, &count) ||
                !spectral_power_values(p, base, direct, p, &count) ||
                !spectral_power_overlap_values(p, base, overlap, p, &count) ||
                !spectral_power_triangular_values(p, base, triangular, p,
                                                  &count)) {
                consecutive_ok = lengths_ok = formula_ok = 0;
                parseval_ok = profile_ok = overlap_ok = flatness_ok = 0;
                free(sizes); free(direct); free(formula); free(overlap);
                free(triangular);
                continue;
            }
            two_length_values(p, base, formula);
            if (!consecutive_bins_hold(p, base, sizes)) consecutive_ok = 0;
            if (!two_lengths_hold(p, base, sizes)) lengths_ok = 0;
            if (maximum_difference(direct, formula, p) > 1e-8 * p)
                formula_ok = 0;
            double total = 0.0;
            for (int k = 0; k < p; k++) total += direct[k];
            if (fabs(total - (double)p * (p - 1)) > 1e-8 * p * p)
                parseval_ok = 0;
            int phi_zero = 0, overlap_sum = 0;
            for (int d = 0; d < base; d++)
                phi_zero += sizes[d] * sizes[d];
            for (int h = 0; h < p; h++) overlap_sum += overlap[h];
            for (int h = 0; h < p; h++)
                if (overlap[h] != triangular[h]) profile_ok = 0;
            if (overlap[0] != p - 1 || overlap_sum != phi_zero ||
                overlap_transform_error(p, overlap, direct) > 1e-8 * p ||
                overlap_inverse_error(p, overlap, direct) > 1e-8 * p)
                overlap_ok = 0;
            int injective = bins_are_injective(base, sizes);
            int boundary = p <= base + 1;
            int flat = power_is_flat(p, direct);
            if (injective != boundary || boundary != flat) flatness_ok = 0;
            free(sizes); free(direct); free(formula); free(overlap);
            free(triangular);
        }
    }

#define REPORT_CHECK(label, condition) do { \
    int check_ok = (condition); \
    checks++; \
    if (check_ok) passed++; \
    printf("  %-58s %s\n", label, check_ok ? "PASS" : "FAIL"); \
} while (0)

    REPORT_CHECK("consecutive-bin endpoint formula", consecutive_ok);
    REPORT_CHECK("q or q+1 bin sizes with exact populations", lengths_ok);
    REPORT_CHECK("two-length kernel formula against defining DFT", formula_ok);
    REPORT_CHECK("Parseval total p(p-1)", parseval_ok);
    REPORT_CHECK("exact two-triangular additive profile", profile_ok);
    REPORT_CHECK("direct additive overlap transform equals Phi", overlap_ok);
    REPORT_CHECK("injective iff p<=b+1 iff flat power", flatness_ok);
    REPORT_CHECK("prime-thirteen fixture and flatness contrast",
                 spectral_power_examples() == 0);

#undef REPORT_CHECK

    printf("\n%d/%d finite checks passed.\n", passed, checks);
    printf("These bounded calculations verify finite instances.\n");
    printf("The Lean stack carries the universal identities.\n");
    return passed == checks;
}

void spectral_power_help(void)
{
    printf(
        "Additive digit-bin spectral power\n\n"
        "Commands\n"
        "  nfield spectral-power inspect <p> [--base <b>]\n"
        "  nfield spectral-power overlap <p> [--base <b>]\n"
        "  nfield spectral-power examples\n"
        "  nfield spectral-power verify\n"
        "  nfield verify spectral-power\n"
        "  nfield spectral <p> [--base <b>]\n\n"
        "The final command is a compatibility alias for inspect.\n\n"
        "The coordinate E(r) records only the intrinsic digit floor(br/p).\n"
        "The inspect command computes Phi from that coordinate-valued\n"
        "additive Fourier transform and independently checks the two-length\n"
        "interval-kernel formula, its zero mode, and the Parseval total.\n\n"
        "The overlap command counts additive shifts directly, checks the exact\n"
        "two-triangular profile determined by q and rho, and verifies that its\n"
        "Fourier transform is Phi and normalized inversion returns the counts.\n"
        "It does not use multiplicative\n"
        "orbit order.  The examples show why flat additive magnitude cannot\n"
        "recover that order.\n\n"
        "Bin endpoints, sizes, overlaps, zero modes, and totals use exact\n"
        "integer arithmetic.  Trigonometric Fourier comparisons are numerical\n"
        "cross-checks with explicit tolerances.  The Lean stack carries the\n"
        "universal identities; this command reports the bounded finite checks.\n"
    );
}

void spectral_print(int p, int base)
{
    (void)spectral_power_inspect(p, base);
}
