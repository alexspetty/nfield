/*
 * autocorrelation_formula.c
 *
 * Finite verification tools for the same-bin cross-spectrum and
 * multiplicative autocorrelation.
 * Exact integer routines build digit bins, multiplier collision counts, and
 * multiplicative-orbit autocorrelations.  Complex finite Fourier transforms
 * independently check the two-dimensional kernel transform, slice formula,
 * individual-orbit formula, and harmonic energies.
 */

#include <complex.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

#define AF_MAX_PRIME 257
#define AF_MAX_BASE 256
#define AF_TOL 1e-8

typedef struct {
    int p;
    int base;
    int order;
    int cosets;
    int occupied;
    int *digit;
    int *bin_label;
    int *bin_size;
    double complex *fourier;
    double complex *cross;
} AFModel;

static int af_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int af_valid(int p, int base, int report)
{
    if (!af_is_prime(p)) {
        if (report) fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (p > AF_MAX_PRIME) {
        if (report) fprintf(stderr, "prime must not exceed %d\n", AF_MAX_PRIME);
        return 0;
    }
    if (base < 2) {
        if (report) fprintf(stderr, "base must be at least 2\n");
        return 0;
    }
    if (base > AF_MAX_BASE) {
        if (report) fprintf(stderr, "base must not exceed %d\n", AF_MAX_BASE);
        return 0;
    }
    if (base % p == 0) {
        if (report) fprintf(stderr, "p must not divide the base\n");
        return 0;
    }
    return 1;
}

static int af_normalize(int value, int p)
{
    int result = value % p;
    return result < 0 ? result + p : result;
}

static int af_mod_pow(int base, int exponent, int modulus)
{
    long long result = 1;
    long long power = af_normalize(base, modulus);
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int af_inverse(int value, int p)
{
    value = af_normalize(value, p);
    return value == 0 ? 0 : af_mod_pow(value, p - 2, p);
}

static int af_order(int base, int p)
{
    int residue = 1;
    for (int length = 1; length <= p - 1; length++) {
        residue = (int)((long long)residue * base % p);
        if (residue == 1) return length;
    }
    return 0;
}

static void af_free(AFModel *model)
{
    if (!model) return;
    free(model->digit);
    free(model->bin_label);
    free(model->bin_size);
    free(model->fourier);
    free(model->cross);
    memset(model, 0, sizeof(*model));
}

static int af_build(int p, int base, AFModel *model)
{
    if (!model || !af_valid(p, base, 0)) return 0;
    memset(model, 0, sizeof(*model));
    model->p = p;
    model->base = base;
    model->order = af_order(base, p);
    model->cosets = (p - 1) / model->order;

    int *population = calloc((size_t)base, sizeof(*population));
    int *bin_index = malloc((size_t)base * sizeof(*bin_index));
    model->digit = malloc((size_t)p * sizeof(*model->digit));
    if (!population || !bin_index || !model->digit) {
        free(population);
        free(bin_index);
        af_free(model);
        return 0;
    }
    for (int d = 0; d < base; d++) bin_index[d] = -1;
    model->digit[0] = -1;
    for (int r = 1; r < p; r++) {
        int digit = (int)((long long)base * r / p);
        model->digit[r] = digit;
        population[digit]++;
    }
    for (int d = 0; d < base; d++)
        if (population[d] > 0) model->occupied++;

    model->bin_label = malloc((size_t)model->occupied * sizeof(*model->bin_label));
    model->bin_size = malloc((size_t)model->occupied * sizeof(*model->bin_size));
    model->fourier = calloc((size_t)model->occupied * p, sizeof(*model->fourier));
    model->cross = calloc((size_t)p * p, sizeof(*model->cross));
    if (!model->bin_label || !model->bin_size || !model->fourier || !model->cross) {
        free(population);
        free(bin_index);
        af_free(model);
        return 0;
    }

    int index = 0;
    for (int d = 0; d < base; d++) {
        if (population[d] == 0) continue;
        bin_index[d] = index;
        model->bin_label[index] = d;
        model->bin_size[index] = population[d];
        index++;
    }

    for (int r = 1; r < p; r++) {
        int bin = bin_index[model->digit[r]];
        for (int k = 0; k < p; k++) {
            double angle = -2.0 * M_PI * k * r / (double)p;
            model->fourier[bin * p + k] += cos(angle) + I * sin(angle);
        }
    }
    for (int k = 0; k < p; k++) {
        for (int kp = 0; kp < p; kp++) {
            double complex value = 0.0;
            for (int bin = 0; bin < model->occupied; bin++)
                value += model->fourier[bin * p + k]
                       * model->fourier[bin * p + kp];
            model->cross[k * p + kp] = value;
        }
    }

    free(population);
    free(bin_index);
    return 1;
}

int autocorrelation_collision_count(int p, int base, int multiplier,
                                    int *count)
{
    if (!count || !af_valid(p, base, 0)) return 0;
    int a = af_normalize(multiplier, p);
    if (a == 0) return 0;
    int matches = 0;
    for (int r = 1; r < p; r++) {
        int ar = (int)((long long)a * r % p);
        int left = (int)((long long)base * r / p);
        int right = (int)((long long)base * ar / p);
        if (left == right) matches++;
    }
    *count = matches;
    return 1;
}

int autocorrelation_aggregate_values(int p, int base, int *values,
                                     int capacity, int *length)
{
    if (!values || !length || !af_valid(p, base, 0)) return 0;
    int order = af_order(base, p);
    if (capacity < order) return 0;
    int multiplier = 1;
    for (int lag = 0; lag < order; lag++) {
        if (!autocorrelation_collision_count(p, base, multiplier,
                                             &values[lag]))
            return 0;
        multiplier = (int)((long long)multiplier * base % p);
    }
    *length = order;
    return 1;
}

int autocorrelation_orbit_values(int p, int base, int coset,
                                 int *values, int capacity, int *length)
{
    if (!values || !length || !af_valid(p, base, 0)) return 0;
    int c = af_normalize(coset, p);
    int order = af_order(base, p);
    if (c == 0 || capacity < order) return 0;

    int *residues = malloc((size_t)order * sizeof(*residues));
    if (!residues) return 0;
    residues[0] = c;
    for (int j = 1; j < order; j++)
        residues[j] = (int)((long long)residues[j - 1] * base % p);

    for (int lag = 0; lag < order; lag++) {
        int matches = 0;
        for (int j = 0; j < order; j++) {
            int left = residues[j];
            int right = residues[(j + lag) % order];
            int left_digit = (int)((long long)base * left / p);
            int right_digit = (int)((long long)base * right / p);
            if (left_digit == right_digit) matches++;
        }
        values[lag] = matches;
    }
    free(residues);
    *length = order;
    return 1;
}

static double complex af_slice_value(const AFModel *model, int multiplier)
{
    int p = model->p;
    int inverse = af_inverse(multiplier, p);
    double complex sum = 0.0;
    for (int k = 0; k < p; k++) {
        int kp = af_normalize(-(int)((long long)inverse * k % p), p);
        sum += model->cross[k * p + kp];
    }
    return sum / p;
}

static double complex af_kernel_transform_entry(const AFModel *model,
                                                 int k, int kp)
{
    int p = model->p;
    double complex sum = 0.0;
    for (int r = 1; r < p; r++) {
        for (int s = 1; s < p; s++) {
            if (model->digit[r] != model->digit[s]) continue;
            double angle = -2.0 * M_PI * (k * r + kp * s) / (double)p;
            sum += cos(angle) + I * sin(angle);
        }
    }
    return sum;
}

static double complex af_kernel_inversion_entry(const AFModel *model,
                                                 int r, int s)
{
    int p = model->p;
    double complex sum = 0.0;
    for (int k = 0; k < p; k++) {
        for (int kp = 0; kp < p; kp++) {
            double angle = 2.0 * M_PI * (k * r + kp * s) / (double)p;
            sum += model->cross[k * p + kp]
                 * (cos(angle) + I * sin(angle));
        }
    }
    return sum / ((double)p * p);
}

static double complex af_individual_orbit_value(const AFModel *model,
                                                int coset, int lag)
{
    int p = model->p;
    int order = model->order;
    int multiplier = af_mod_pow(model->base, lag, p);
    int *residues = malloc((size_t)order * sizeof(*residues));
    double complex *subgroup_sum = calloc((size_t)p, sizeof(*subgroup_sum));
    if (!residues || !subgroup_sum) {
        free(residues);
        free(subgroup_sum);
        return NAN + I * NAN;
    }
    residues[0] = af_normalize(coset, p);
    for (int j = 1; j < order; j++)
        residues[j] = (int)((long long)residues[j - 1] * model->base % p);
    for (int frequency = 0; frequency < p; frequency++) {
        for (int j = 0; j < order; j++) {
            double angle = 2.0 * M_PI * frequency * residues[j] / (double)p;
            subgroup_sum[frequency] += cos(angle) + I * sin(angle);
        }
    }
    double complex total = 0.0;
    for (int k = 0; k < p; k++) {
        for (int kp = 0; kp < p; kp++) {
            int frequency = (k + (int)((long long)multiplier * kp % p)) % p;
            total += model->cross[k * p + kp] * subgroup_sum[frequency];
        }
    }
    free(residues);
    free(subgroup_sum);
    return total / ((double)p * p);
}

static void af_cross_diagnostics(const AFModel *model,
                                 double *imaginary_error,
                                 double *symmetry_error,
                                 double *reflection_error,
                                 double *vanishing_error)
{
    int p = model->p;
    double imag = 0.0, sym = 0.0, reflect = 0.0;
    double complex total = 0.0;
    for (int k = 0; k < p; k++) {
        int nk = (p - k) % p;
        for (int kp = 0; kp < p; kp++) {
            int nkp = (p - kp) % p;
            double complex value = model->cross[k * p + kp];
            double di = fabs(cimag(value));
            double ds = cabs(value - model->cross[kp * p + k]);
            double dr = cabs(value - model->cross[nk * p + nkp]);
            if (di > imag) imag = di;
            if (ds > sym) sym = ds;
            if (dr > reflect) reflect = dr;
            total += value;
        }
    }
    *imaginary_error = imag;
    *symmetry_error = sym;
    *reflection_error = reflect;
    *vanishing_error = cabs(total);
}

static int af_coset_representatives(const AFModel *model, int *representatives)
{
    int p = model->p;
    int *seen = calloc((size_t)p, sizeof(*seen));
    if (!seen) return 0;
    int count = 0;
    for (int c = 1; c < p; c++) {
        if (seen[c]) continue;
        representatives[count++] = c;
        int r = c;
        for (int j = 0; j < model->order; j++) {
            seen[r] = 1;
            r = (int)((long long)r * model->base % p);
        }
    }
    free(seen);
    return count;
}

int autocorrelation_inspect(int p, int base)
{
    if (!af_valid(p, base, 1)) return 1;
    AFModel model;
    if (!af_build(p, base, &model)) {
        fprintf(stderr, "unable to allocate the autocorrelation model\n");
        return 1;
    }
    int *aggregate = calloc((size_t)model.order, sizeof(*aggregate));
    int *reference = calloc((size_t)model.order, sizeof(*reference));
    int length = 0;
    if (!aggregate || !reference ||
        !autocorrelation_aggregate_values(p, base, aggregate, model.order, &length) ||
        !autocorrelation_orbit_values(p, base, 1, reference, model.order, &length)) {
        free(aggregate); free(reference); af_free(&model);
        fprintf(stderr, "unable to allocate the autocorrelation values\n");
        return 1;
    }

    printf("Same-bin cross-spectrum and multiplicative autocorrelation\n");
    printf("p = %d, base = %d\n", p, base);
    printf("multiplicative order L = %d, orbits = %d\n", model.order, model.cosets);
    printf("primitive-root domain: %s\n\n", model.cosets == 1 ? "yes" : "no");

    printf("Occupied digit bins\n");
    for (int bin = 0; bin < model.occupied; bin++) {
        int digit = model.bin_label[bin];
        int first = -1, last = -1;
        for (int r = 1; r < p; r++) {
            if (model.digit[r] != digit) continue;
            if (first < 0) first = r;
            last = r;
        }
        printf("  digit %d: %d..%d, size %d\n", digit, first, last,
               model.bin_size[bin]);
    }

    double imag, sym, reflect, vanish;
    af_cross_diagnostics(&model, &imag, &sym, &reflect, &vanish);
    double tolerance = AF_TOL * p * p;
    printf("\nCross-spectrum diagnostics (numerical finite Fourier checks)\n");
    printf("  maximum imaginary part %.3g  %s\n", imag,
           imag <= tolerance ? "PASS" : "FAIL");
    printf("  symmetry error %.3g  %s\n", sym,
           sym <= tolerance ? "PASS" : "FAIL");
    printf("  complement-reflection error %.3g  %s\n", reflect,
           reflect <= tolerance ? "PASS" : "FAIL");
    printf("  total-sum magnitude %.3g  %s\n\n", vanish,
           vanish <= tolerance ? "PASS" : "FAIL");

    if (model.cosets == 1)
        printf("The reference repetend visits every nonzero residue.\n");
    else
        printf("The Fourier slice is aggregate; the reference word is one orbit.\n");
    printf("%5s %10s %11s %11s %15s\n",
           "lag", "multiplier", "reference", "aggregate", "slice error");
    double max_slice_error = 0.0;
    for (int lag = 0; lag < model.order; lag++) {
        int multiplier = af_mod_pow(base, lag, p);
        double complex slice = af_slice_value(&model, multiplier);
        double error = cabs(slice - aggregate[lag]);
        if (error > max_slice_error) max_slice_error = error;
        printf("%5d %10d %11d %11d %15.3g\n", lag, multiplier,
               reference[lag], aggregate[lag], error);
    }
    int primitive_ok = model.cosets != 1;
    if (model.cosets == 1) {
        primitive_ok = 1;
        for (int lag = 0; lag < model.order; lag++)
            if (reference[lag] != aggregate[lag]) primitive_ok = 0;
    }
    printf("\nline-slice formula maximum numerical error %.3g  %s\n",
           max_slice_error, max_slice_error <= tolerance ? "PASS" : "FAIL");
    printf("primitive-root reference equals aggregate  %s\n",
           model.cosets == 1 ? (primitive_ok ? "PASS" : "FAIL") : "not applicable");
    printf("Result  %s\n",
           imag <= tolerance && sym <= tolerance && reflect <= tolerance &&
           vanish <= tolerance && max_slice_error <= tolerance && primitive_ok
               ? "PASS" : "FAIL");

    int ok = imag <= tolerance && sym <= tolerance && reflect <= tolerance &&
             vanish <= tolerance && max_slice_error <= tolerance && primitive_ok;
    free(aggregate);
    free(reference);
    af_free(&model);
    return ok ? 0 : 1;
}

int autocorrelation_slice(int p, int multiplier, int base)
{
    if (!af_valid(p, base, 1)) return 1;
    int a = af_normalize(multiplier, p);
    if (a == 0) {
        fprintf(stderr, "multiplier must be nonzero modulo p\n");
        return 1;
    }
    AFModel model;
    if (!af_build(p, base, &model)) return 1;
    int direct = 0, inverse_direct = 0;
    int inverse = af_inverse(a, p);
    autocorrelation_collision_count(p, base, a, &direct);
    autocorrelation_collision_count(p, base, inverse, &inverse_direct);
    double complex slice = af_slice_value(&model, a);
    double error = cabs(slice - direct);
    double tolerance = AF_TOL * p * p;

    printf("Multiplicative same-bin slice\n");
    printf("p = %d, base = %d, a = %d, inverse = %d\n\n",
           p, base, a, inverse);
    printf("direct C(a) = %d\n", direct);
    printf("direct C(a^-1) = %d  %s\n", inverse_direct,
           direct == inverse_direct ? "PASS" : "FAIL");
    printf("Fourier line sum / p = %.12f %+.3gi\n",
           creal(slice), cimag(slice));
    printf("slice error = %.3g  %s\n", error,
           error <= tolerance ? "PASS" : "FAIL");
    printf("Result  %s\n",
           direct == inverse_direct && error <= tolerance ? "PASS" : "FAIL");
    af_free(&model);
    return direct == inverse_direct && error <= tolerance ? 0 : 1;
}

int autocorrelation_orbit(int p, int coset, int base)
{
    if (!af_valid(p, base, 1)) return 1;
    int c = af_normalize(coset, p);
    if (c == 0) {
        fprintf(stderr, "coset representative must be nonzero modulo p\n");
        return 1;
    }
    AFModel model;
    if (!af_build(p, base, &model)) return 1;
    int *values = calloc((size_t)model.order, sizeof(*values));
    int length = 0;
    if (!values || !autocorrelation_orbit_values(p, base, c, values,
                                                  model.order, &length)) {
        free(values); af_free(&model); return 1;
    }

    printf("Individual multiplicative-orbit autocorrelation\n");
    printf("p = %d, base = %d, representative = %d\n", p, base, c);
    printf("order L = %d, total orbits = %d\n\n", model.order, model.cosets);
    printf("residues:");
    int residue = c;
    for (int j = 0; j < model.order; j++) {
        printf(" %d", residue);
        residue = (int)((long long)residue * base % p);
    }
    printf("\ndigits:  ");
    residue = c;
    for (int j = 0; j < model.order; j++) {
        printf(" %d", model.digit[residue]);
        residue = (int)((long long)residue * base % p);
    }
    printf("\n\n%5s %12s %18s %13s\n",
           "lag", "direct R_c", "subgroup formula", "error");
    double max_error = 0.0;
    for (int lag = 0; lag < model.order; lag++) {
        double complex formula = af_individual_orbit_value(&model, c, lag);
        double error = cabs(formula - values[lag]);
        if (!isfinite(creal(formula)) || !isfinite(cimag(formula)))
            error = INFINITY;
        if (error > max_error) max_error = error;
        printf("%5d %12d %15.10f %+.1gi %13.3g\n", lag, values[lag],
               creal(formula), cimag(formula), error);
    }
    double tolerance = AF_TOL * p * p;
    printf("\nindividual-orbit formula maximum numerical error %.3g  %s\n",
           max_error, max_error <= tolerance ? "PASS" : "FAIL");
    if (model.cosets > 1)
        printf("This orbit is not the aggregate line slice; use inspect to compare them.\n");
    printf("Result  %s\n", max_error <= tolerance ? "PASS" : "FAIL");
    free(values);
    af_free(&model);
    return max_error <= tolerance ? 0 : 1;
}

int autocorrelation_harmonics(int p, int coset, int base)
{
    if (!af_valid(p, base, 1)) return 1;
    int c = af_normalize(coset, p);
    if (c == 0) {
        fprintf(stderr, "coset representative must be nonzero modulo p\n");
        return 1;
    }
    int order = af_order(base, p);
    int *values = calloc((size_t)order, sizeof(*values));
    int length = 0;
    if (!values || !autocorrelation_orbit_values(p, base, c, values,
                                                  order, &length)) {
        free(values); return 1;
    }
    printf("Cyclic same-bin harmonic energies\n");
    printf("p = %d, base = %d, orbit representative = %d, L = %d\n\n",
           p, base, c, order);
    printf("%5s %18s %15s\n", "mode", "eigenvalue", "imaginary part");
    int ok = 1;
    for (int mode = 0; mode < order; mode++) {
        double complex value = 0.0;
        for (int lag = 0; lag < order; lag++) {
            double angle = 2.0 * M_PI * mode * lag / (double)order;
            value += values[lag] * (cos(angle) + I * sin(angle));
        }
        value /= order;
        if (creal(value) < -AF_TOL * order || fabs(cimag(value)) > AF_TOL * order)
            ok = 0;
        printf("%5d %18.12f %15.3g\n", mode, creal(value), cimag(value));
    }
    printf("\nreal and nonnegative harmonic energies  %s\n", ok ? "PASS" : "FAIL");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    free(values);
    return ok ? 0 : 1;
}

static int af_example_prime_seven(void)
{
    AFModel model;
    if (!af_build(7, 10, &model)) return 0;
    int cross_ok = 1;
    for (int k = 0; k < 7; k++) {
        for (int kp = 0; kp < 7; kp++) {
            double expected = (k + kp) % 7 == 0 ? 6.0 : -1.0;
            if (cabs(model.cross[k * 7 + kp] - expected) > 1e-8)
                cross_ok = 0;
        }
    }
    int values[6], length = 0;
    int orbit_ok = autocorrelation_orbit_values(7, 10, 1, values, 6, &length)
                && length == 6 && values[0] == 6;
    for (int lag = 1; lag < 6 && orbit_ok; lag++)
        if (values[lag] != 0) orbit_ok = 0;
    af_free(&model);
    return cross_ok && orbit_ok;
}

static int af_example_prime_forty_one(void)
{
    int expected[] = {40, 0, 6, 6, 0};
    int values[5], length = 0;
    if (!autocorrelation_aggregate_values(41, 10, values, 5, &length) ||
        length != 5)
        return 0;
    for (int lag = 0; lag < 5; lag++)
        if (values[lag] != expected[lag]) return 0;
    return 1;
}

int autocorrelation_examples(void)
{
    int seven = af_example_prime_seven();
    int forty_one = af_example_prime_forty_one();
    printf("Same-bin cross-spectrum exact examples\n\n");
    printf("Decimal prime seven\n");
    printf("  G(k,k') is 6 on k+k'=0 and -1 elsewhere  %s\n",
           seven ? "PASS" : "FAIL");
    printf("  R = 6 0 0 0 0 0 for the repetend 142857  %s\n\n",
           seven ? "PASS" : "FAIL");
    printf("Decimal prime forty-one\n");
    printf("  order 5 with 8 multiplicative orbits\n");
    printf("  aggregate slice values = 40 0 6 6 0  %s\n",
           forty_one ? "PASS" : "FAIL");
    printf("  the aggregate is not mislabeled as one orbit\n");
    printf("\nResult  %s\n", seven && forty_one ? "PASS" : "FAIL");
    return seven && forty_one ? 0 : 1;
}

static int af_check_complement(const AFModel *model)
{
    for (int r = 1; r < model->p; r++)
        if (model->digit[model->p - r] != model->base - 1 - model->digit[r])
            return 0;
    return 1;
}

static int af_check_slices(const AFModel *model)
{
    double tolerance = AF_TOL * model->p * model->p;
    for (int a = 1; a < model->p; a++) {
        int direct = 0, inverse_direct = 0;
        autocorrelation_collision_count(model->p, model->base, a, &direct);
        autocorrelation_collision_count(model->p, model->base,
                                         af_inverse(a, model->p),
                                         &inverse_direct);
        if (direct != inverse_direct ||
            cabs(af_slice_value(model, a) - direct) > tolerance)
            return 0;
    }
    return 1;
}

static int af_check_transform(const AFModel *model)
{
    double tolerance = AF_TOL * model->p * model->p;
    int frequencies[] = {0, 1, 2};
    for (int i = 0; i < 3; i++) {
        int k = frequencies[i] % model->p;
        int kp = frequencies[2 - i] % model->p;
        double complex direct = af_kernel_transform_entry(model, k, kp);
        if (cabs(direct - model->cross[k * model->p + kp]) > tolerance)
            return 0;
    }
    int residues[] = {0, 1, 2};
    for (int i = 0; i < 3; i++) {
        int r = residues[i] % model->p;
        int s = residues[2 - i] % model->p;
        int expected = r != 0 && s != 0 && model->digit[r] == model->digit[s];
        if (cabs(af_kernel_inversion_entry(model, r, s) - expected) > tolerance)
            return 0;
    }
    return 1;
}

static int af_check_aggregation(const AFModel *model)
{
    int *representatives = malloc((size_t)model->cosets * sizeof(*representatives));
    int *aggregate = calloc((size_t)model->order, sizeof(*aggregate));
    int *orbit = calloc((size_t)model->order, sizeof(*orbit));
    if (!representatives || !aggregate || !orbit) {
        free(representatives); free(aggregate); free(orbit); return 0;
    }
    int count = af_coset_representatives(model, representatives);
    int length = 0;
    int ok = count == model->cosets &&
        autocorrelation_aggregate_values(model->p, model->base, aggregate,
                                         model->order, &length);
    int *sum = calloc((size_t)model->order, sizeof(*sum));
    if (!sum) ok = 0;
    for (int index = 0; index < count && ok; index++) {
        if (!autocorrelation_orbit_values(model->p, model->base,
                                          representatives[index], orbit,
                                          model->order, &length)) {
            ok = 0;
            break;
        }
        for (int lag = 0; lag < model->order; lag++) sum[lag] += orbit[lag];
    }
    for (int lag = 0; lag < model->order && ok; lag++)
        if (sum[lag] != aggregate[lag]) ok = 0;
    if (model->cosets == 1 && ok)
        for (int lag = 0; lag < model->order; lag++)
            if (orbit[lag] != aggregate[lag]) ok = 0;
    free(representatives); free(aggregate); free(orbit); free(sum);
    return ok;
}

static int af_check_harmonics(const AFModel *model)
{
    int *representatives = malloc((size_t)model->cosets * sizeof(*representatives));
    int *values = calloc((size_t)model->order, sizeof(*values));
    if (!representatives || !values) {
        free(representatives); free(values); return 0;
    }
    int count = af_coset_representatives(model, representatives);
    int ok = count == model->cosets;
    for (int index = 0; index < count && ok; index++) {
        int length = 0;
        if (!autocorrelation_orbit_values(model->p, model->base,
                                          representatives[index], values,
                                          model->order, &length)) {
            ok = 0;
            break;
        }
        for (int mode = 0; mode < model->order; mode++) {
            double complex energy = 0.0;
            for (int lag = 0; lag < model->order; lag++) {
                double angle = 2.0 * M_PI * mode * lag / model->order;
                energy += values[lag] * (cos(angle) + I * sin(angle));
            }
            energy /= model->order;
            if (creal(energy) < -AF_TOL * model->order ||
                fabs(cimag(energy)) > AF_TOL * model->order)
                ok = 0;
        }
    }
    free(representatives); free(values);
    return ok;
}

static int af_check_individual_fixtures(void)
{
    const int fixtures[][3] = {
        {7, 10, 1}, {13, 10, 1}, {41, 10, 1}, {7, 4, 1}
    };
    for (size_t f = 0; f < sizeof(fixtures) / sizeof(fixtures[0]); f++) {
        AFModel model;
        if (!af_build(fixtures[f][0], fixtures[f][1], &model)) return 0;
        int *values = calloc((size_t)model.order, sizeof(*values));
        int length = 0, ok = values && autocorrelation_orbit_values(
            model.p, model.base, fixtures[f][2], values, model.order, &length);
        for (int lag = 0; lag < model.order && ok; lag++) {
            double complex formula = af_individual_orbit_value(
                &model, fixtures[f][2], lag);
            if (!isfinite(creal(formula)) || !isfinite(cimag(formula)) ||
                cabs(formula - values[lag]) > AF_TOL * model.p * model.p)
                ok = 0;
        }
        free(values);
        af_free(&model);
        if (!ok) return 0;
    }
    return 1;
}

int autocorrelation_formula_verify(void)
{
    int complement_ok = 1, cross_ok = 1, transform_ok = 1;
    int slice_ok = 1, aggregation_ok = 1, harmonic_ok = 1;
    int cases = 0;

    printf("Finite C verification of same-bin cross-spectrum and multiplicative autocorrelation\n");
    printf("Sweep domain: 2 <= base <= 12, prime p <= 43, p does not divide base\n");
    printf("Bin, collision, orbit, and aggregation checks are exact integers.\n");
    printf("Finite Fourier checks use tolerance 1e-8 times p^2.\n\n");

    for (int base = 2; base <= 12; base++) {
        for (int p = 2; p <= 43; p++) {
            if (!af_is_prime(p) || base % p == 0) continue;
            AFModel model;
            if (!af_build(p, base, &model)) return 0;
            cases++;
            if (!af_check_complement(&model)) complement_ok = 0;
            double imag, sym, reflect, vanish;
            af_cross_diagnostics(&model, &imag, &sym, &reflect, &vanish);
            double tolerance = AF_TOL * p * p;
            if (imag > tolerance || sym > tolerance || reflect > tolerance ||
                vanish > tolerance)
                cross_ok = 0;
            if (!af_check_transform(&model)) transform_ok = 0;
            if (!af_check_slices(&model)) slice_ok = 0;
            if (!af_check_aggregation(&model)) aggregation_ok = 0;
            if (!af_check_harmonics(&model)) harmonic_ok = 0;
            af_free(&model);
        }
    }

    int checks = 0, passed = 0;
#define AF_REPORT(label, condition) do { \
    int check_ok = (condition); \
    checks++; \
    if (check_ok) passed++; \
    printf("  %-64s %s\n", label, check_ok ? "PASS" : "FAIL"); \
} while (0)
    AF_REPORT("complement digit and same-bin reflection laws", complement_ok);
    AF_REPORT("real, symmetric, reflection-invariant G with vanishing total", cross_ok);
    AF_REPORT("sampled two-dimensional transform and inversion", transform_ok);
    AF_REPORT("every nonzero multiplier slice and inverse symmetry", slice_ok);
    AF_REPORT("exact aggregation over every multiplicative orbit", aggregation_ok);
    AF_REPORT("real nonnegative harmonic energies on every orbit", harmonic_ok);
    AF_REPORT("individual-orbit subgroup formula on contrasting fixtures",
              af_check_individual_fixtures());
    AF_REPORT("decimal prime-seven and multi-orbit prime-forty-one examples",
              af_example_prime_seven() && af_example_prime_forty_one());
#undef AF_REPORT

    printf("\n%d finite (base, prime) models checked.\n", cases);
    printf("%d/%d verification groups passed.\n", passed, checks);
    printf("The bounded calculations are reproducible evidence.\n");
    printf("The manuscript supplies the universal finite-group proofs.\n");
    return passed == checks;
}

void autocorrelation_formula_help(void)
{
    printf(
        "Same-bin cross-spectrum and multiplicative autocorrelation\n\n"
        "Commands\n"
        "  nfield autocorrelation inspect <p> [--base <b>]\n"
        "  nfield autocorrelation slice <p> <a> [--base <b>]\n"
        "  nfield autocorrelation orbit <p> <c> [--base <b>]\n"
        "  nfield autocorrelation harmonics <p> [--coset <c>] [--base <b>]\n"
        "  nfield autocorrelation examples\n"
        "  nfield autocorrelation verify\n"
        "  nfield verify autocorrelation\n"
        "  nfield help autocorrelation\n\n"
        "The same-bin kernel K is transformed in both residue coordinates to\n"
        "the cross-spectrum G.  The slice command compares the exact collision\n"
        "count C(a) with the numerical Fourier line k'=-a^-1 k.\n\n"
        "The inspect command distinguishes the reference repetend orbit from\n"
        "the aggregate over all multiplicative orbits.  They coincide only in\n"
        "the primitive-root case.  The orbit command independently checks the\n"
        "subgroup exponential-sum formula for one chosen orbit.\n\n"
        "The harmonics command diagonalizes the normalized circulant readout\n"
        "and checks that its finite energies are real and nonnegative.\n\n"
        "Digit bins, collision counts, orbit words, and aggregation use exact\n"
        "integer arithmetic.  Complex Fourier transforms are numerical\n"
        "cross-checks with explicit tolerances.  Finite sweeps are evidence,\n"
        "not replacements for the manuscript's universal proofs.\n"
    );
}
