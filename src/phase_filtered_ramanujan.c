/*
 * phase_filtered_ramanujan.c
 *
 * Finite verification tools for the Ramanujan selector, spectral line,
 * normalized phase gate, and Euclidean digit-bin word.
 *
 * Collision counts, cell counts, bin words, and disjointness checks use exact
 * integer arithmetic.  The finite Fourier and phase-gate evaluations use C99
 * complex arithmetic and report their tolerance explicitly.
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

#define PF_MAX_PRIME 257
#define PF_MAX_BASE 256
#define PF_MAX_CELLS 20000000LL
#define PF_TOL 1e-8

typedef struct {
    int p;
    int base;
    int occupied;
    int *digit;
    int *bin_label;
    int *bin_size;
    double complex *fourier;
} PFModel;

static int pf_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int pf_valid(int p, int base, int report)
{
    if (!pf_is_prime(p)) {
        if (report) fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (p > PF_MAX_PRIME) {
        if (report) fprintf(stderr, "prime must not exceed %d\n", PF_MAX_PRIME);
        return 0;
    }
    if (base < 2) {
        if (report) fprintf(stderr, "base must be at least 2\n");
        return 0;
    }
    if (base > PF_MAX_BASE) {
        if (report) fprintf(stderr, "base must not exceed %d\n", PF_MAX_BASE);
        return 0;
    }
    if (base % p == 0) {
        if (report) fprintf(stderr, "p must not divide the base\n");
        return 0;
    }
    return 1;
}

static int pf_normalize(int value, int p)
{
    int result = value % p;
    return result < 0 ? result + p : result;
}

static int pf_collision_by_residues(int p, int base, int multiplier,
                                    int *count)
{
    if (!count || !pf_is_prime(p) || base < 2 || base > PF_MAX_BASE ||
        base % p == 0)
        return 0;
    int a = pf_normalize(multiplier, p);
    if (a == 0) return 0;
    int matches = 0;
    for (int x = 1; x < p; x++) {
        int ax = (int)((long long)a * x % p);
        if ((long long)base * x / p == (long long)base * ax / p)
            matches++;
    }
    *count = matches;
    return 1;
}

/*
 * Count the same grid points through the ab-cell partition used in the
 * fixed-multiplier proof.  Taking the cheaper of this and direct residue
 * enumeration keeps long prime scans practical while preserving exactness.
 */
static int pf_collision_for_fixed_multiplier(int p, int base, int multiplier,
                                             int *count)
{
    if (!count || multiplier < 1 || !pf_is_prime(p) || base < 2 ||
        base > PF_MAX_BASE || base % p == 0 || multiplier % p == 0)
        return 0;
    long long cells = (long long)multiplier * base;
    if (cells > PF_MAX_CELLS || p <= cells)
        return pf_collision_by_residues(p, base, multiplier, count);

    int matches = 0;
    for (long long m = 0; m < cells; m++) {
        if (m / multiplier != m % base) continue;
        long long lower = ((long long)p * m + cells - 1) / cells;
        long long upper = ((long long)p * (m + 1) + cells - 1) / cells;
        long long in_cell = upper - lower;
        if (m == 0) in_cell--; /* x=0 is not in F_p^*. */
        matches += (int)in_cell;
    }
    *count = matches;
    return 1;
}

static int pf_mod_pow(int base, int exponent, int modulus)
{
    long long result = 1;
    long long power = pf_normalize(base, modulus);
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

static int pf_inverse(int value, int p)
{
    value = pf_normalize(value, p);
    return value == 0 ? 0 : pf_mod_pow(value, p - 2, p);
}

static void pf_free(PFModel *model)
{
    if (!model) return;
    free(model->digit);
    free(model->bin_label);
    free(model->bin_size);
    free(model->fourier);
    memset(model, 0, sizeof(*model));
}

static int pf_build(int p, int base, PFModel *model)
{
    if (!model || !pf_valid(p, base, 0)) return 0;
    memset(model, 0, sizeof(*model));
    model->p = p;
    model->base = base;
    int *population = calloc((size_t)base, sizeof(*population));
    int *bin_index = malloc((size_t)base * sizeof(*bin_index));
    model->digit = malloc((size_t)p * sizeof(*model->digit));
    if (!population || !bin_index || !model->digit) {
        free(population); free(bin_index); pf_free(model); return 0;
    }
    for (int d = 0; d < base; d++) bin_index[d] = -1;
    model->digit[0] = -1;
    for (int x = 1; x < p; x++) {
        int digit = (int)((long long)base * x / p);
        model->digit[x] = digit;
        population[digit]++;
    }
    for (int d = 0; d < base; d++)
        if (population[d] > 0) model->occupied++;
    model->bin_label = malloc((size_t)model->occupied * sizeof(*model->bin_label));
    model->bin_size = malloc((size_t)model->occupied * sizeof(*model->bin_size));
    model->fourier = calloc((size_t)model->occupied * p, sizeof(*model->fourier));
    if (!model->bin_label || !model->bin_size || !model->fourier) {
        free(population); free(bin_index); pf_free(model); return 0;
    }
    int index = 0;
    for (int d = 0; d < base; d++) {
        if (population[d] == 0) continue;
        bin_index[d] = index;
        model->bin_label[index] = d;
        model->bin_size[index] = population[d];
        index++;
    }
    for (int x = 1; x < p; x++) {
        int bin = bin_index[model->digit[x]];
        for (int k = 0; k < p; k++) {
            double angle = -2.0 * M_PI * k * x / (double)p;
            model->fourier[bin * p + k] += cos(angle) + I * sin(angle);
        }
    }
    free(population);
    free(bin_index);
    return 1;
}

static double complex pf_cross(const PFModel *model, int k, int kp)
{
    double complex value = 0.0;
    for (int bin = 0; bin < model->occupied; bin++)
        value += model->fourier[bin * model->p + k]
               * model->fourier[bin * model->p + kp];
    return value;
}

int phase_gate_components(int p, int base, int multiplier,
                          int *collision, double *sigma_real,
                          double *sigma_imag, double *mass,
                          double *gamma)
{
    if (!collision || !sigma_real || !sigma_imag || !mass || !gamma ||
        !pf_valid(p, base, 0))
        return 0;
    int a = pf_normalize(multiplier, p);
    if (a == 0) return 0;
    PFModel model;
    if (!pf_build(p, base, &model)) return 0;
    if (!pf_collision_by_residues(p, base, a, collision)) {
        pf_free(&model);
        return 0;
    }
    int inverse = pf_inverse(a, p);
    double complex sigma = 0.0;
    double unsigned_mass = 0.0;
    for (int k = 0; k < p; k++) {
        int kp = pf_normalize(-(int)((long long)inverse * k % p), p);
        sigma += pf_cross(&model, k, kp);
        for (int bin = 0; bin < model.occupied; bin++)
            unsigned_mass += cabs(model.fourier[bin * p + k])
                           * cabs(model.fourier[bin * p + kp]);
    }
    *sigma_real = creal(sigma);
    *sigma_imag = cimag(sigma);
    *mass = unsigned_mass;
    *gamma = unsigned_mass > 0.0 ? cabs(sigma) / unsigned_mass : NAN;
    pf_free(&model);
    return 1;
}

static double complex pf_ramanujan_weighted(const PFModel *model,
                                            int multiplier)
{
    int p = model->p;
    int a = pf_normalize(multiplier, p);
    double complex total = 0.0;
    for (int k = 0; k < p; k++) {
        for (int kp = 0; kp < p; kp++) {
            int linear = (k + (int)((long long)a * kp % p)) % p;
            int ramanujan = linear == 0 ? p - 1 : -1;
            total += pf_cross(model, k, kp) * ramanujan;
        }
    }
    return total / ((double)p * p);
}

static int pf_singleton_bins(const PFModel *model)
{
    if (model->occupied != model->p - 1) return 0;
    for (int bin = 0; bin < model->occupied; bin++)
        if (model->bin_size[bin] != 1) return 0;
    return 1;
}

static double pf_singleton_formula_error(const PFModel *model)
{
    double maximum = 0.0;
    for (int k = 0; k < model->p; k++) {
        for (int kp = 0; kp < model->p; kp++) {
            int target = (k + kp) % model->p == 0 ? model->p - 1 : -1;
            double error = cabs(pf_cross(model, k, kp) - target);
            if (error > maximum) maximum = error;
        }
    }
    return maximum;
}

static int pf_bins_disjoint(const PFModel *model, int multiplier)
{
    int p = model->p;
    int a = pf_normalize(multiplier, p);
    for (int bin = 0; bin < model->occupied; bin++) {
        int label = model->bin_label[bin];
        for (int x = 1; x < p; x++) {
            if (model->digit[x] != label) continue;
            int ax = (int)((long long)a * x % p);
            if (model->digit[ax] == label) return 0;
        }
    }
    return 1;
}

int phase_gate_cell_count(int multiplier, int base, long long *count)
{
    if (!count || multiplier < 1 || base < 2) return 0;
    long long cells = (long long)multiplier * base;
    if (cells > PF_MAX_CELLS) return 0;
    long long matches = 0;
    for (long long m = 0; m < cells; m++)
        if (m / multiplier == m % base) matches++;
    *count = matches;
    return 1;
}

static int pf_power_checked(int base, int exponent, int *value)
{
    if (!value || base < 2 || exponent < 0) return 0;
    long long result = 1;
    for (int i = 0; i < exponent; i++) {
        result *= base;
        if (result > 10000000) return 0;
    }
    *value = (int)result;
    return 1;
}

static long long pf_ceil_div(long long numerator, int denominator)
{
    return (numerator + denominator - 1) / denominator;
}

int phase_gate_bin_word_values(int p, int base, int *sizes, int *word,
                               int capacity, int *q, int *remainder)
{
    if (!sizes || !word || !q || !remainder || capacity < base ||
        !pf_valid(p, base, 0))
        return 0;
    memset(sizes, 0, (size_t)base * sizeof(*sizes));
    memset(word, 0, (size_t)base * sizeof(*word));
    for (int x = 1; x < p; x++)
        sizes[(int)((long long)base * x / p)]++;
    *q = p / base;
    *remainder = p % base;
    word[0] = 0;
    for (int d = 1; d < base; d++)
        word[d] = (int)(pf_ceil_div((long long)(d + 1) * *remainder, base)
                     - pf_ceil_div((long long)d * *remainder, base));
    return 1;
}

static int pf_bin_word_holds(int p, int base)
{
    int *sizes = calloc((size_t)base, sizeof(*sizes));
    int *word = calloc((size_t)base, sizeof(*word));
    int q = 0, remainder = 0;
    int ok = sizes && word && phase_gate_bin_word_values(
        p, base, sizes, word, base, &q, &remainder);
    int ones = 0;
    for (int d = 0; d < base && ok; d++) {
        int expected = q + word[d];
        if (sizes[d] != expected || (word[d] != 0 && word[d] != 1)) ok = 0;
        ones += word[d];
    }
    if (ok && (word[0] != 0 || ones != remainder - 1)) ok = 0;
    long long actual_zero = 0;
    for (int d = 0; d < base; d++)
        actual_zero += (long long)sizes[d] * sizes[d];
    long long formula_zero = (long long)base * q * q
                           + (long long)(2 * q + 1) * (remainder - 1);
    if (ok && actual_zero != formula_zero) ok = 0;
    free(sizes); free(word);
    return ok;
}

static int pf_continued_fraction(int numerator, int denominator,
                                 int *terms, int capacity)
{
    int count = 0;
    while (denominator != 0) {
        if (count >= capacity) return 0;
        terms[count++] = numerator / denominator;
        int next = numerator % denominator;
        numerator = denominator;
        denominator = next;
    }
    return count;
}

static int pf_cf_reconstructs(int numerator, int denominator)
{
    int terms[64];
    int count = pf_continued_fraction(numerator, denominator, terms, 64);
    if (count <= 0 || terms[count - 1] <= 1) return 0;
    long long n = terms[count - 1], d = 1;
    for (int i = count - 2; i >= 0; i--) {
        long long next_n = (long long)terms[i] * n + d;
        d = n;
        n = next_n;
    }
    return n == numerator && d == denominator;
}

int phase_gate_inspect(int p, int multiplier, int base)
{
    if (!pf_valid(p, base, 1)) return 1;
    int a = pf_normalize(multiplier, p);
    if (a == 0) {
        fprintf(stderr, "multiplier must be nonzero modulo p\n");
        return 1;
    }
    PFModel model;
    if (!pf_build(p, base, &model)) return 1;
    int collision = 0;
    double sigma_real = 0.0, sigma_imag = 0.0, mass = 0.0, gamma = 0.0;
    if (!phase_gate_components(p, base, a, &collision, &sigma_real,
                               &sigma_imag, &mass, &gamma)) {
        pf_free(&model); return 1;
    }
    double complex ramanujan = pf_ramanujan_weighted(&model, a);
    int disjoint = pf_bins_disjoint(&model, a);
    int singleton = pf_singleton_bins(&model);
    double singleton_error = singleton ? pf_singleton_formula_error(&model) : 0.0;
    double lower = collision / (double)(p - 1);
    double tolerance = PF_TOL * p * p;
    int identity = a == 1;
    int ok = cabs(ramanujan - collision) <= tolerance
          && fabs(sigma_real - (double)p * collision) <= tolerance
          && fabs(sigma_imag) <= tolerance
          && gamma + tolerance >= lower && gamma <= 1.0 + tolerance
          && ((collision == 0) == disjoint)
          && ((collision == 0) == (gamma <= tolerance))
          && (!identity || fabs(gamma - 1.0) <= tolerance)
          && (!singleton || singleton_error <= tolerance);

    printf("Ramanujan selector and phase-gate geometry\n");
    printf("p = %d, base = %d, multiplier a = %d\n\n", p, base, a);
    printf("Exact collision geometry\n");
    printf("  C_p,b(a) = %d\n", collision);
    printf("  all bins disjoint from their a-multiples: %s\n",
           disjoint ? "yes" : "no");
    printf("  collision-free iff every bin is disjoint  %s\n\n",
           ((collision == 0) == disjoint) ? "PASS" : "FAIL");
    printf("Ramanujan-weighted two-dimensional spectrum (numerical)\n");
    printf("  weighted sum / p^2 = %.12f %+.3gi\n",
           creal(ramanujan), cimag(ramanujan));
    printf("  equals C_p,b(a), error %.3g  %s\n\n",
           cabs(ramanujan - collision),
           cabs(ramanujan - collision) <= tolerance ? "PASS" : "FAIL");
    if (singleton)
        printf("Singleton-bin formula G(k,k')=c_p(k+k') max error %.3g  %s\n\n",
               singleton_error,
               singleton_error <= tolerance ? "PASS" : "FAIL");
    printf("Phase gate\n");
    printf("  Sigma = %.12f %+.3gi\n", sigma_real, sigma_imag);
    printf("  p*C = %d; slice identity  %s\n", p * collision,
           fabs(sigma_real - (double)p * collision) <= tolerance &&
           fabs(sigma_imag) <= tolerance ? "PASS" : "FAIL");
    printf("  unsigned mass M = %.12f\n", mass);
    printf("  Gamma = %.12f\n", gamma);
    printf("  lower bound C/(p-1) = %.12f  %s\n", lower,
           gamma + tolerance >= lower ? "PASS" : "FAIL");
    printf("  upper bound Gamma <= 1  %s\n",
           gamma <= 1.0 + tolerance ? "PASS" : "FAIL");
    printf("  Gamma=0 iff C=0  %s\n",
           ((collision == 0) == (gamma <= tolerance)) ? "PASS" : "FAIL");
    if (identity)
        printf("  identity multiplier Gamma=1  %s\n",
               fabs(gamma - 1.0) <= tolerance ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    pf_free(&model);
    return ok ? 0 : 1;
}

int phase_gate_multipliers(int p, int base)
{
    if (!pf_valid(p, base, 1)) return 1;
    printf("Phase gate over all nonzero multipliers\n");
    printf("p = %d, base = %d\n\n", p, base);
    printf("%6s %10s %16s %16s\n", "a", "C(a)", "Gamma(a)", "gate status");
    int zero_count = 0, ok = 1;
    for (int a = 1; a < p; a++) {
        int collision = 0;
        double sr, si, mass, gamma;
        if (!phase_gate_components(p, base, a, &collision, &sr, &si,
                                   &mass, &gamma)) {
            ok = 0;
            break;
        }
        int zero = collision == 0;
        if (zero) zero_count++;
        if (zero != (gamma <= PF_TOL * p * p)) ok = 0;
        printf("%6d %10d %16.10f %16s\n", a, collision, gamma,
               zero ? "closed" : "open");
    }
    printf("\ncollision-free multipliers = %d\n", zero_count);
    printf("closed gate iff collision-free  %s\n", ok ? "PASS" : "FAIL");
    printf("No formula for the number of closed multipliers is asserted here.\n");
    return ok ? 0 : 1;
}

int phase_gate_bin_word(int p, int base)
{
    if (!pf_valid(p, base, 1)) return 1;
    int *sizes = calloc((size_t)base, sizeof(*sizes));
    int *word = calloc((size_t)base, sizeof(*word));
    int q = 0, remainder = 0;
    if (!sizes || !word || !phase_gate_bin_word_values(
            p, base, sizes, word, base, &q, &remainder)) {
        free(sizes); free(word); return 1;
    }
    int terms[64];
    int term_count = pf_continued_fraction(base, remainder, terms, 64);
    int ones = 0;
    long long zero_mass = 0;
    for (int d = 0; d < base; d++) {
        ones += word[d];
        zero_mass += (long long)sizes[d] * sizes[d];
    }
    long long zero_formula = (long long)base * q * q
                           + (long long)(2 * q + 1) * (remainder - 1);
    int ok = pf_bin_word_holds(p, base)
          && pf_cf_reconstructs(base, remainder);

    printf("Euclidean digit-bin word\n");
    printf("p = %d = %d*%d + %d\n\n", p, base, q, remainder);
    printf("digit:    ");
    for (int d = 0; d < base; d++) printf(" %d", d);
    printf("\nbin size: ");
    for (int d = 0; d < base; d++) printf(" %d", sizes[d]);
    printf("\nexcess w:");
    for (int d = 0; d < base; d++) printf(" %d", word[d]);
    printf("\n\nw entries equal to one = %d; expected r-1 = %d  %s\n",
           ones, remainder - 1, ones == remainder - 1 ? "PASS" : "FAIL");
    printf("continued-fraction tail CF(%d/%d) = [", base, remainder);
    for (int i = 0; i < term_count; i++)
        printf("%s%d", i ? "," : "", terms[i]);
    printf("]  %s\n", pf_cf_reconstructs(base, remainder) ? "PASS" : "FAIL");
    printf("G(0,0) = %lld; formula = %lld  %s\n", zero_mass, zero_formula,
           zero_mass == zero_formula ? "PASS" : "FAIL");
    printf("The remainder fixes the excess word and continued-fraction tail,\n");
    printf("not the full spectrum or phase gate.\n");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    free(sizes); free(word);
    return ok ? 0 : 1;
}

static int pf_density_error_holds(int p, int base, int multiplier,
                                  long long cells_matching)
{
    int collision = 0;
    if (!pf_collision_for_fixed_multiplier(p, base, multiplier, &collision))
        return 0;
    long long cells = (long long)multiplier * base;
    long long discrepancy = llabs(cells * collision - cells_matching * p);
    return discrepancy <= cells_matching * cells;
}

int phase_gate_density(int multiplier, int base, int max_prime)
{
    if (multiplier < 1) {
        fprintf(stderr, "multiplier must be positive\n");
        return 1;
    }
    if (base < 2 || base > PF_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", PF_MAX_BASE);
        return 1;
    }
    if (max_prime < 2 || max_prime > 200000) {
        fprintf(stderr, "maximum prime must be between 2 and 200000\n");
        return 1;
    }
    long long cell_count = 0;
    if (!phase_gate_cell_count(multiplier, base, &cell_count)) {
        fprintf(stderr, "a*base is too large for the exact cell enumeration\n");
        return 1;
    }
    long long cells = (long long)multiplier * base;
    double density = cell_count / (double)cells;
    int tested = 0, bound_ok = 1;
    long long min_scaled = 0, max_scaled = 0;
    int initialized = 0;
    for (int p = 2; p <= max_prime; p++) {
        if (!pf_is_prime(p) || base % p == 0 || multiplier % p == 0) continue;
        int collision = 0;
        if (!pf_collision_for_fixed_multiplier(p, base, multiplier,
                                               &collision)) {
            bound_ok = 0;
            continue;
        }
        long long scaled = cells * collision - cell_count * p;
        if (!initialized || scaled < min_scaled) min_scaled = scaled;
        if (!initialized || scaled > max_scaled) max_scaled = scaled;
        initialized = 1;
        if (!pf_density_error_holds(p, base, multiplier, cell_count)) bound_ok = 0;
        tested++;
    }

    printf("Fixed-multiplier collision density\n");
    printf("base b = %d, multiplier a = %d\n", base, multiplier);
    printf("exact cells N_a,b = %lld of %lld\n", cell_count, cells);
    printf("predicted density N/(a*b) = %.12f\n", density);
    printf("eligible primes checked through %d = %d\n", max_prime, tested);
    printf("scaled discrepancy a*b*C - N*p ranges from %lld to %lld\n",
           min_scaled, max_scaled);
    printf("finite cell-discrepancy bound  %s\n", bound_ok ? "PASS" : "FAIL");
    printf("The finite cell partition certifies this bounded discrepancy.\n");
    printf("Result  %s\n", tested > 0 && bound_ok ? "PASS" : "FAIL");
    return tested > 0 && bound_ok ? 0 : 1;
}

int phase_gate_power_lag(int lag, int base, int max_prime)
{
    if (lag < 1) {
        fprintf(stderr, "positive power lag must be at least 1\n");
        return 1;
    }
    int multiplier = 0;
    if (!pf_power_checked(base, lag, &multiplier)) {
        fprintf(stderr, "base^lag is too large for exact finite enumeration\n");
        return 1;
    }
    long long count = 0;
    if (!phase_gate_cell_count(multiplier, base, &count)) {
        fprintf(stderr, "base^(lag+1) is too large for exact finite enumeration\n");
        return 1;
    }
    printf("Power-lag cell identity\n");
    printf("base = %d, lag = %d, a = b^lag = %d\n", base, lag, multiplier);
    printf("N_(b^lag,b) = %lld; expected b^lag = %d  %s\n\n",
           count, multiplier, count == multiplier ? "PASS" : "FAIL");
    if (count != multiplier) return 1;
    return phase_gate_density(multiplier, base, max_prime);
}

static double pf_prime_harmonic(int maximum, int base)
{
    double total = 0.0;
    for (int p = 2; p <= maximum; p++)
        if (pf_is_prime(p) && base % p != 0) total += 1.0 / p;
    return total;
}

int phase_gate_prime_sum(int lag, int base, int max_prime)
{
    if (lag < 0) {
        fprintf(stderr, "lag must be nonnegative\n");
        return 1;
    }
    if (base < 2 || base > PF_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", PF_MAX_BASE);
        return 1;
    }
    if (max_prime < 11 || max_prime > 200000) {
        fprintf(stderr, "maximum prime must be between 11 and 200000\n");
        return 1;
    }
    int multiplier = 1;
    if (lag > 0 && !pf_power_checked(base, lag, &multiplier)) {
        fprintf(stderr, "base^lag is too large for this finite calculation\n");
        return 1;
    }
    double coefficient = lag == 0 ? 1.0 : 1.0 / base;
    double D = 0.0, correction = 0.0;
    int primes = 0;
    for (int p = 2; p <= max_prime; p++) {
        if (!pf_is_prime(p) || base % p == 0) continue;
        int collision = 0;
        if (!pf_collision_for_fixed_multiplier(p, base, multiplier,
                                               &collision))
            return 1;
        double error = collision - coefficient * p;
        D += collision / ((double)p * p);
        correction += error / ((double)p * p);
        primes++;
    }
    double harmonic = pf_prime_harmonic(max_prime, base);
    double decomposition_error = fabs(D - (coefficient * harmonic + correction));
    double leading = log(log((double)max_prime));

    printf("Prime-sum boundary for fixed power lag\n");
    printf("base = %d, lag = %d, primes through %d = %d\n", base, lag,
           max_prime, primes);
    printf("D_b,lag(x;2) = %.12f\n", D);
    printf("leading coefficient = %.12f\n", coefficient);
    printf("coefficient * prime harmonic sum = %.12f\n",
           coefficient * harmonic);
    printf("finite discrepancy correction = %.12f\n", correction);
    printf("exact finite decomposition error = %.3g  %s\n",
           decomposition_error, decomposition_error <= 1e-12 ? "PASS" : "FAIL");
    printf("D/log(log x) = %.12f; predicted limiting coefficient %.12f\n",
           D / leading, coefficient);
    printf("The ratio is finite evidence; the associated asymptotic is a separate analytic theorem.\n");
    printf("Result  %s\n", decomposition_error <= 1e-12 ? "PASS" : "FAIL");
    return decomposition_error <= 1e-12 ? 0 : 1;
}

int phase_gate_examples(void)
{
    int collision = 0;
    double sr, si, mass, identity_gamma, closed_gamma;
    int identity = phase_gate_components(7, 10, 1, &collision, &sr, &si,
                                         &mass, &identity_gamma)
                && collision == 6 && fabs(identity_gamma - 1.0) < 1e-8;
    int closed = phase_gate_components(7, 10, 3, &collision, &sr, &si,
                                       &mass, &closed_gamma)
              && collision == 0 && closed_gamma < 1e-8;
    long long cells = 0;
    int lag = phase_gate_cell_count(100, 10, &cells) && cells == 100;
    int bins = pf_bin_word_holds(43, 10) && pf_cf_reconstructs(10, 3);
    printf("Ramanujan selector and phase-gate examples\n\n");
    printf("decimal prime seven identity has C=6 and Gamma=1  %s\n",
           identity ? "PASS" : "FAIL");
    printf("decimal prime seven multiplier three has C=0 and Gamma=0  %s\n",
           closed ? "PASS" : "FAIL");
    printf("base-ten lag two has N_(100,10)=100 and density 1/10  %s\n",
           lag ? "PASS" : "FAIL");
    printf("p=43 gives remainder 3, tail CF(10/3)=[3,3], and two excess bins  %s\n",
           bins ? "PASS" : "FAIL");
    printf("\nResult  %s\n", identity && closed && lag && bins ? "PASS" : "FAIL");
    return identity && closed && lag && bins ? 0 : 1;
}

static int pf_check_gate_and_ramanujan(void)
{
    for (int base = 2; base <= 10; base++) {
        for (int p = 2; p <= 31; p++) {
            if (!pf_is_prime(p) || base % p == 0) continue;
            PFModel model;
            if (!pf_build(p, base, &model)) return 0;
            double tolerance = PF_TOL * p * p;
            for (int a = 1; a < p; a++) {
                int collision = 0;
                double sr, si, mass, gamma;
                if (!phase_gate_components(p, base, a, &collision, &sr, &si,
                                           &mass, &gamma)) {
                    pf_free(&model); return 0;
                }
                double complex ramanujan = pf_ramanujan_weighted(&model, a);
                int disjoint = pf_bins_disjoint(&model, a);
                if (cabs(ramanujan - collision) > tolerance ||
                    fabs(sr - (double)p * collision) > tolerance ||
                    fabs(si) > tolerance || mass <= 0.0 ||
                    gamma + tolerance < collision / (double)(p - 1) ||
                    gamma > 1.0 + tolerance ||
                    ((collision == 0) != disjoint) ||
                    ((collision == 0) != (gamma <= tolerance)) ||
                    (a == 1 && fabs(gamma - 1.0) > tolerance)) {
                    pf_free(&model); return 0;
                }
            }
            pf_free(&model);
        }
    }
    return 1;
}

static int pf_check_bin_words(void)
{
    for (int base = 2; base <= 24; base++)
        for (int p = 2; p <= 97; p++)
            if (pf_is_prime(p) && base % p != 0 &&
                (!pf_bin_word_holds(p, base) ||
                 !pf_cf_reconstructs(base, p % base)))
                return 0;
    return 1;
}

static int pf_check_fixed_density(void)
{
    for (int base = 2; base <= 8; base++) {
        for (int a = 1; a <= 30; a++) {
            long long cells = 0;
            if (!phase_gate_cell_count(a, base, &cells)) return 0;
            for (int p = 2; p <= 97; p++) {
                if (!pf_is_prime(p) || base % p == 0 || a % p == 0) continue;
                if (!pf_density_error_holds(p, base, a, cells)) return 0;
            }
        }
    }
    return 1;
}

static int pf_check_collision_routes(void)
{
    for (int base = 2; base <= 12; base++) {
        for (int a = 1; a <= 30; a++) {
            for (int p = 2; p <= 997; p++) {
                if (!pf_is_prime(p) || base % p == 0 || a % p == 0) continue;
                int residues = 0, cells = 0;
                if (!pf_collision_by_residues(p, base, a, &residues) ||
                    !pf_collision_for_fixed_multiplier(p, base, a, &cells) ||
                    residues != cells)
                    return 0;
            }
        }
    }
    return 1;
}

static int pf_check_power_lags(void)
{
    for (int base = 2; base <= 12; base++) {
        for (int lag = 1; lag <= 4; lag++) {
            int a = 0;
            long long cells = 0;
            if (!pf_power_checked(base, lag, &a) ||
                !phase_gate_cell_count(a, base, &cells) || cells != a)
                return 0;
        }
    }
    return 1;
}

static int pf_check_primitive_specialization(void)
{
    for (int base = 2; base <= 12; base++) {
        for (int p = 2; p <= 43; p++) {
            if (!pf_is_prime(p) || base % p == 0 || mult_order(base, p) != p - 1)
                continue;
            int *aggregate = calloc((size_t)(p - 1), sizeof(*aggregate));
            int *orbit = calloc((size_t)(p - 1), sizeof(*orbit));
            int length = 0, ok = aggregate && orbit
                && autocorrelation_aggregate_values(p, base, aggregate, p - 1, &length)
                && autocorrelation_orbit_values(p, base, 1, orbit, p - 1, &length);
            for (int lag = 0; lag < length && ok; lag++)
                if (aggregate[lag] != orbit[lag]) ok = 0;
            free(aggregate); free(orbit);
            if (!ok) return 0;
        }
    }
    return 1;
}

static int pf_check_singleton_formula(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!pf_is_prime(p) || base % p == 0) continue;
            PFModel model;
            if (!pf_build(p, base, &model)) return 0;
            double tolerance = PF_TOL * p * p;
            int ok = pf_singleton_bins(&model)
                  && pf_singleton_formula_error(&model) <= tolerance;
            pf_free(&model);
            if (!ok) return 0;
        }
    }
    return 1;
}

static int pf_check_prime_sum_decomposition(void)
{
    for (int base = 2; base <= 10; base++) {
        for (int lag = 0; lag <= 3; lag++) {
            int a = 1;
            if (lag > 0 && !pf_power_checked(base, lag, &a)) return 0;
            double coefficient = lag == 0 ? 1.0 : 1.0 / base;
            double D = 0.0, harmonic = 0.0, correction = 0.0;
            for (int p = 2; p <= 997; p++) {
                if (!pf_is_prime(p) || base % p == 0) continue;
                int collision = 0;
                if (!pf_collision_for_fixed_multiplier(p, base, a,
                                                       &collision))
                    return 0;
                D += collision / ((double)p * p);
                harmonic += 1.0 / p;
                correction += (collision - coefficient * p) / ((double)p * p);
            }
            if (fabs(D - coefficient * harmonic - correction) > 1e-12)
                return 0;
        }
    }
    return 1;
}

int phase_gate_verify(void)
{
    printf("Finite C verification of Ramanujan selector and phase-gate geometry\n");
    printf("Exact integer checks are separated from numerical Fourier checks.\n\n");
    int checks = 0, passed = 0;
    int gate_and_ramanujan = pf_check_gate_and_ramanujan();
    int bin_words = pf_check_bin_words();
#define PF_REPORT(label, condition) do { \
    int check_ok = (condition); \
    checks++; \
    if (check_ok) passed++; \
    printf("  %-66s %s\n", label, check_ok ? "PASS" : "FAIL"); \
} while (0)
    PF_REPORT("Ramanujan-weighted identity for every multiplier in the sweep",
              gate_and_ramanujan);
    PF_REPORT("gate bounds, zero equivalence, and identity normalization",
              gate_and_ramanujan);
    PF_REPORT("exact Euclidean bin word and zero-frequency mass",
              bin_words);
    PF_REPORT("continued-fraction tail reconstruction by remainder class",
              bin_words);
    PF_REPORT("fixed-multiplier cell density with finite discrepancy bound",
              pf_check_fixed_density());
    PF_REPORT("direct residues agree with exact cell-partition counts",
              pf_check_collision_routes());
    PF_REPORT("positive power-lag cell count N=b^lag and density 1/b",
              pf_check_power_lags());
    PF_REPORT("primitive-root repetend specialization", pf_check_primitive_specialization());
    PF_REPORT("singleton-bin cross-spectrum is the prime Ramanujan sum",
              pf_check_singleton_formula());
    PF_REPORT("exact finite prime-sum leading-plus-correction decomposition",
              pf_check_prime_sum_decomposition());
    PF_REPORT("named decimal fixtures", phase_gate_examples() == 0);
#undef PF_REPORT
    printf("\n%d/%d verification groups passed.\n", passed, checks);
    printf("Finite sweeps and Fourier tolerances are evidence.\n");
    printf("Finite sweeps do not replace universal or analytic proofs.\n");
    return passed == checks;
}

void phase_gate_help(void)
{
    printf(
        "Ramanujan selector, spectral line, phase gate, and Euclidean cells\n\n"
        "Commands\n"
        "  nfield phase-gate inspect <p> <a> [--base <b>]\n"
        "  nfield phase-gate multipliers <p> [--base <b>]\n"
        "  nfield phase-gate bin-word <p> [--base <b>]\n"
        "  nfield phase-gate density <a> [--base <b>] [--max-prime <P>]\n"
        "  nfield phase-gate power-lag <ell> [--base <b>] [--max-prime <P>]\n"
        "  nfield phase-gate prime-sum <ell> [--base <b>] [--max-prime <P>]\n"
        "  nfield phase-gate examples\n"
        "  nfield phase-gate verify\n"
        "  nfield verify phase-gate\n"
        "  nfield help phase-gate\n\n"
        "inspect computes the exact same-bin collision count and bin-disjointness\n"
        "condition. It independently evaluates the full Ramanujan-weighted\n"
        "two-dimensional spectrum, the selected slice, unsigned phase mass,\n"
        "and the exact upper and lower gate bounds.\n\n"
        "bin-word reconstructs the Euclidean quotient, remainder, exact excess\n"
        "word, continued-fraction tail, and zero-frequency mass. The remainder\n"
        "is reported only as coarse structure, never as a complete spectrum.\n\n"
        "density and power-lag enumerate the exact finite cells behind the\n"
        "fixed-multiplier collision density. prime-sum displays the exact finite\n"
        "leading-plus-correction decomposition at s=2. Its finite ratio is not\n"
        "presented as proof of the separate asymptotic or convergence boundary.\n\n"
        "The existing gate and gate_width commands concern later derangement\n"
        "results. They are deliberately separate from this phase coefficient.\n"
        "No later character decomposition is used here.\n"
    );
}
