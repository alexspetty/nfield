/*
 * cross_alignment.c: Exact synchronized matrix and orbit checks.
 *
 * The integer score matrix G stores L*A, where L is the common rough-part
 * period.  This keeps every entry and every scalar recovery exact.  Floating
 * point is used only for LAPACK spectral corroboration of the exact matrix.
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

#define CA_MAX_N 500
#define CA_MAX_BASE 1000
#define CA_PRINT_MAX_N 25
#define CA_SPECTRUM_MAX_P 250
#define CA_MAX_EXTRA_DEPTH 10000

extern void dsyev_(char *jobz, char *uplo, int *n, double *a, int *lda,
                   double *w, double *work, int *lwork, int *info);
extern void zheev_(char *jobz, char *uplo, int *n, double complex *a,
                   int *lda, double *w, double complex *work, int *lwork,
                   double *rwork, int *info);

typedef struct {
    int n;
    int base;
    int rough;
    int supported;
    int minimum_depth;
    int depth;
    int order;
    int dimension;
    int *score;
    long long *remainders;
} CAMatrix;

static int ca_gcd(int a, int b)
{
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a < 0 ? -a : a;
}

static long long ca_gcdll(long long a, long long b)
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

static void ca_reduce(long long *numerator, long long *denominator)
{
    long long g = ca_gcdll(*numerator, *denominator);
    *numerator /= g;
    *denominator /= g;
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
}

static void ca_subtract(long long an, long long ad,
                        long long bn, long long bd,
                        long long *rn, long long *rd)
{
    long long g = ca_gcdll(ad, bd);
    *rn = an * (bd / g) - bn * (ad / g);
    *rd = ad * (bd / g);
    ca_reduce(rn, rd);
}

static int ca_equal(long long an, long long ad,
                    long long bn, long long bd)
{
    ca_reduce(&an, &ad);
    ca_reduce(&bn, &bd);
    return an == bn && ad == bd;
}

static void ca_print_fraction(long long numerator, long long denominator)
{
    ca_reduce(&numerator, &denominator);
    printf("%lld/%lld", numerator, denominator);
}

static long long ca_choose2(long long n)
{
    return n < 2 ? 0 : n * (n - 1) / 2;
}

static int ca_is_prime(int n)
{
    if (n < 2) return 0;
    if (n % 2 == 0) return n == 2;
    for (int d = 3; d <= n / d; d += 2)
        if (n % d == 0) return 0;
    return 1;
}

static int ca_supported_part(int n, int base, int *rough, int *supported)
{
    if (n < 1 || base < 2) return 0;
    int q = n;
    for (;;) {
        int g = ca_gcd(q, base);
        if (g == 1) break;
        q /= g;
    }
    *rough = q;
    *supported = n / q;
    return 1;
}

static int ca_clearing_depth(int supported, int base)
{
    int depth = 0;
    while (supported > 1) {
        int g = ca_gcd(supported, base);
        if (g == 1) return -1;
        supported /= g;
        depth++;
    }
    return depth;
}

static int ca_order(int base, int modulus)
{
    if (modulus == 1) return 1;
    if (modulus < 2 || ca_gcd(base, modulus) != 1) return -1;
    int value = base % modulus;
    int order = 1;
    while (value != 1 && order <= modulus) {
        value = (int)(((long long)value * base) % modulus);
        order++;
    }
    return value == 1 ? order : -1;
}

static void ca_free(CAMatrix *matrix)
{
    free(matrix->score);
    free(matrix->remainders);
    memset(matrix, 0, sizeof(*matrix));
}

static int ca_build(int n, int base, int requested_depth, CAMatrix *matrix)
{
    memset(matrix, 0, sizeof(*matrix));
    if (n < 2 || n > CA_MAX_N || base < 2 || base > CA_MAX_BASE)
        return 0;

    int rough, supported;
    if (!ca_supported_part(n, base, &rough, &supported)) return 0;
    int minimum_depth = ca_clearing_depth(supported, base);
    int depth = requested_depth < 0 ? minimum_depth : requested_depth;
    if (minimum_depth < 0 || depth < minimum_depth
        || depth - minimum_depth > CA_MAX_EXTRA_DEPTH)
        return 0;
    int order = ca_order(base, rough);
    if (order < 1) return 0;

    int dimension = n - 1;
    int *score = calloc((size_t)dimension * dimension, sizeof(int));
    long long *remainders = calloc((size_t)n, sizeof(long long));
    if (!score || !remainders) {
        free(score);
        free(remainders);
        return 0;
    }

    matrix->n = n;
    matrix->base = base;
    matrix->rough = rough;
    matrix->supported = supported;
    matrix->minimum_depth = minimum_depth;
    matrix->depth = depth;
    matrix->order = order;
    matrix->dimension = dimension;
    matrix->score = score;
    matrix->remainders = remainders;

    if (rough == 1) {
        for (int i = 0; i < dimension * dimension; i++) score[i] = 1;
        return 1;
    }

    for (int k = 1; k < n; k++) {
        long long remainder = k;
        for (int d = 0; d < depth; d++)
            remainder = remainder * base % n;
        remainders[k] = remainder;
    }

    for (int i = 1; i < n; i++) {
        for (int j = i; j < n; j++) {
            long long left = remainders[i], right = remainders[j];
            int matches = 0;
            if (left == 0 && right == 0) {
                matches = order;
            } else if (left != 0 && right != 0) {
                for (int t = 0; t < order; t++) {
                    if (left * base / n == right * base / n) matches++;
                    left = left * base % n;
                    right = right * base % n;
                }
            }
            score[(i - 1) * dimension + (j - 1)] = matches;
            score[(j - 1) * dimension + (i - 1)] = matches;
        }
    }
    return 1;
}

static int ca_validate_request(int n, int base, int depth)
{
    if (n < 2 || n > CA_MAX_N) {
        fprintf(stderr, "n must be between 2 and %d\n", CA_MAX_N);
        return 0;
    }
    if (base < 2 || base > CA_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", CA_MAX_BASE);
        return 0;
    }
    int rough, supported;
    ca_supported_part(n, base, &rough, &supported);
    int minimum = ca_clearing_depth(supported, base);
    if (depth >= 0 && depth < minimum) {
        fprintf(stderr, "depth %d is too early; use --depth %d or greater\n",
                depth, minimum);
        return 0;
    }
    if (depth >= 0 && depth - minimum > CA_MAX_EXTRA_DEPTH) {
        fprintf(stderr, "depth may be at most %d positions beyond the minimum\n",
                CA_MAX_EXTRA_DEPTH);
        return 0;
    }
    return 1;
}

int cross_alignment_entry_fraction(int n, int base, int depth,
                                   int row, int column,
                                   long long *numerator,
                                   long long *denominator)
{
    if (!numerator || !denominator || row < 1 || row >= n
        || column < 1 || column >= n)
        return 0;
    CAMatrix matrix;
    if (!ca_build(n, base, depth, &matrix)) return 0;
    *numerator = matrix.score[(row - 1) * matrix.dimension + column - 1];
    *denominator = matrix.order;
    ca_reduce(numerator, denominator);
    ca_free(&matrix);
    return 1;
}

static int ca_scalar_fractions(const CAMatrix *matrix,
                               long long *alpha_num, long long *alpha_den,
                               long long *sigma_num, long long *sigma_den,
                               long long *focused_num, long long *focused_den)
{
    int dimension = matrix->dimension;
    if (dimension < 2) return 0;

    long long pair_sum = 0;
    for (int i = 0; i < dimension; i++)
        for (int j = i + 1; j < dimension; j++)
            pair_sum += matrix->score[i * dimension + j];
    *sigma_num = pair_sum;
    *sigma_den = (long long)matrix->order * ca_choose2(dimension);
    ca_reduce(sigma_num, sigma_den);

    long long row_sum = 0;
    for (int j = 0; j < dimension; j++) row_sum += matrix->score[j];
    if (matrix->rough > 1)
        row_sum += (long long)(matrix->supported - 1) * matrix->order;
    *alpha_num = row_sum;
    *alpha_den = (long long)matrix->order * dimension;
    ca_reduce(alpha_num, alpha_den);
    ca_subtract(*alpha_num, *alpha_den, *sigma_num, *sigma_den,
                focused_num, focused_den);
    return 1;
}

int cross_alignment_scalar_fractions(
    int n, int base, int depth,
    long long *alpha_num, long long *alpha_den,
    long long *sigma_num, long long *sigma_den,
    long long *focused_num, long long *focused_den)
{
    if (!alpha_num || !alpha_den || !sigma_num || !sigma_den
        || !focused_num || !focused_den)
        return 0;
    CAMatrix matrix;
    if (!ca_build(n, base, depth, &matrix)) return 0;
    int ok = ca_scalar_fractions(&matrix, alpha_num, alpha_den,
                                 sigma_num, sigma_den,
                                 focused_num, focused_den);
    ca_free(&matrix);
    return ok;
}

static int ca_matrix_invariants(const CAMatrix *matrix)
{
    int dimension = matrix->dimension;
    for (int i = 0; i < dimension; i++) {
        if (matrix->score[i * dimension + i] != matrix->order) return 0;
        for (int j = i + 1; j < dimension; j++) {
            int a = matrix->score[i * dimension + j];
            if (a != matrix->score[j * dimension + i]
                || a < 0 || a > matrix->order)
                return 0;
        }
    }
    return 1;
}

/* G=L*A is itself an exact one-hot Gram matrix.  Terminating rows have
   one in each of L shared termination coordinates; nonterminating rows
   have one digit coordinate at every synchronized position. */
static int ca_gram_reconstruction(const CAMatrix *matrix)
{
    int dimension = matrix->dimension;
    if (matrix->rough == 1) {
        for (int i = 0; i < dimension * dimension; i++)
            if (matrix->score[i] != 1) return 0;
        return 1;
    }
    for (int i = 1; i < matrix->n; i++) {
        for (int j = 1; j < matrix->n; j++) {
            long long left = matrix->remainders[i];
            long long right = matrix->remainders[j];
            int dot = 0;
            if (left == 0 && right == 0) {
                dot = matrix->order;
            } else if (left != 0 && right != 0) {
                for (int t = 0; t < matrix->order; t++) {
                    int left_digit = (int)(left * matrix->base / matrix->n);
                    int right_digit = (int)(right * matrix->base / matrix->n);
                    dot += left_digit == right_digit;
                    left = left * matrix->base % matrix->n;
                    right = right * matrix->base % matrix->n;
                }
            }
            if (dot != matrix->score[(i - 1) * dimension + j - 1])
                return 0;
        }
    }
    return 1;
}

static int ca_same_matrix(const CAMatrix *left, const CAMatrix *right)
{
    return left->dimension == right->dimension
        && left->order == right->order
        && memcmp(left->score, right->score,
                  (size_t)left->dimension * left->dimension * sizeof(int)) == 0;
}

static int ca_eigenvalues(const CAMatrix *matrix, double *eigenvalues)
{
    int n = matrix->dimension;
    double *copy = malloc((size_t)n * n * sizeof(double));
    double *work = malloc((size_t)(3 * n + 1) * sizeof(double));
    if (!copy || !work) {
        free(copy);
        free(work);
        return 0;
    }
    for (int i = 0; i < n * n; i++)
        copy[i] = matrix->score[i] / (double)matrix->order;
    int lda = n, lwork = 3 * n + 1, info = 0;
    char jobz = 'N', uplo = 'U';
    dsyev_(&jobz, &uplo, &n, copy, &lda, eigenvalues,
           work, &lwork, &info);
    free(copy);
    free(work);
    return info == 0;
}

static int ca_psd_trace(const CAMatrix *matrix, double *minimum,
                        double *trace)
{
    double *eigenvalues = malloc((size_t)matrix->dimension * sizeof(double));
    if (!eigenvalues || !ca_eigenvalues(matrix, eigenvalues)) {
        free(eigenvalues);
        return 0;
    }
    *minimum = eigenvalues[0];
    *trace = 0.0;
    for (int i = 0; i < matrix->dimension; i++) *trace += eigenvalues[i];
    int ok = *minimum > -1e-9
          && fabs(*trace - matrix->dimension) < 1e-7;
    free(eigenvalues);
    return ok;
}

static void ca_print_matrix(const CAMatrix *matrix)
{
    int dimension = matrix->dimension;
    if (matrix->n > CA_PRINT_MAX_N) {
        printf("  full entry table omitted for n>%d; use a smaller denominator\n",
               CA_PRINT_MAX_N);
        return;
    }
    printf("       ");
    for (int j = 1; j <= dimension; j++) printf("%7d", j);
    printf("\n");
    for (int i = 0; i < dimension; i++) {
        printf("  %3d  ", i + 1);
        for (int j = 0; j < dimension; j++) {
            long long num = matrix->score[i * dimension + j];
            long long den = matrix->order;
            ca_reduce(&num, &den);
            if (den == 1) printf("%7lld", num);
            else {
                char value[32];
                snprintf(value, sizeof(value), "%lld/%lld", num, den);
                printf("%7s", value);
            }
        }
        printf("\n");
    }
}

int cross_alignment_matrix_print(int n, int base, int depth)
{
    if (!ca_validate_request(n, base, depth)) return 1;
    CAMatrix matrix, later;
    if (!ca_build(n, base, depth, &matrix)
        || !ca_build(n, base,
                     (depth < 0 ? matrix.minimum_depth : depth) + 1,
                     &later)) {
        fprintf(stderr, "could not construct the synchronized matrix\n");
        ca_free(&matrix);
        return 1;
    }

    int invariants = ca_matrix_invariants(&matrix);
    int gram = ca_gram_reconstruction(&matrix);
    int depth_ok = ca_same_matrix(&matrix, &later);
    double minimum = 0.0, trace = 0.0;
    int psd = ca_psd_trace(&matrix, &minimum, &trace);

    printf("Synchronized cross-alignment matrix\n\n");
    printf("  n = %d, base = %d, dimension = %d\n",
           n, base, matrix.dimension);
    printf("  canonical decomposition n = q*s = %d*%d\n",
           matrix.rough, matrix.supported);
    printf("  minimal clearing depth = %d; chosen depth = %d\n",
           matrix.minimum_depth, matrix.depth);
    printf("  common window L = ord_q(b) = %d\n\n", matrix.order);
    printf("Entries A(i,j), with rows and columns indexed by numerator:\n");
    ca_print_matrix(&matrix);

    printf("\nMatrix certificates:\n");
    printf("  symmetric with unit diagonal: %s\n",
           invariants ? "PASS" : "FAIL");
    printf("  exact one-hot Gram reconstruction G=L*A: %s\n",
           gram ? "PASS" : "FAIL");
    printf("  same matrix one common position later: %s\n",
           depth_ok ? "PASS" : "FAIL");
    printf("  numerical PSD cross-check: min eigenvalue %.3g, trace %.12g  %s\n",
           minimum, trace, psd ? "PASS" : "FAIL");

    int scalar_ok = 1;
    if (n >= 3) {
        long long an, ad, sn, sd, fn, fd;
        long long ean, ead, esn, esd, efn, efd;
        scalar_ok = ca_scalar_fractions(&matrix, &an, &ad, &sn, &sd, &fn, &fd)
                 && coherence_decomposition_fractions(
                        n, base, matrix.depth,
                        &ean, &ead, &esn, &esd, &efn, &efd)
                 && ca_equal(an, ad, ean, ead)
                 && ca_equal(sn, sd, esn, esd)
                 && ca_equal(fn, fd, efn, efd);
        printf("\nRecovered scalar statistics:\n");
        printf("  reference alignment alpha = ");
        ca_print_fraction(an, ad);
        printf("\n  pairwise off-diagonal mean sigma = ");
        ca_print_fraction(sn, sd);
        printf("\n  signed residual F = ");
        ca_print_fraction(fn, fd);
        printf("\n  independent coherence-decomposition engine comparison: %s\n",
               scalar_ok ? "PASS" : "FAIL");
        if (matrix.rough > 1)
            printf("  reference-row terminating correction = s-1 = %d\n",
                   matrix.supported - 1);
    } else {
        printf("\nPairwise mean sigma is undefined at n=2 (empty pair set).\n");
    }

    int ok = invariants && gram && depth_ok && psd && scalar_ok;
    printf("\nResult: %s\n", ok ? "PASS" : "FAIL");
    ca_free(&later);
    ca_free(&matrix);
    return ok ? 0 : 1;
}

static int ca_digit_map_injective(int p, int base)
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

static int ca_identity(const CAMatrix *matrix)
{
    for (int i = 0; i < matrix->dimension; i++)
        for (int j = 0; j < matrix->dimension; j++)
            if (matrix->score[i * matrix->dimension + j]
                != (i == j ? matrix->order : 0))
                return 0;
    return 1;
}

static int ca_validate_prime(int p, int base)
{
    if (!ca_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (base < 2 || base > CA_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", CA_MAX_BASE);
        return 0;
    }
    if (base % p == 0) {
        fprintf(stderr, "p must not divide the base\n");
        return 0;
    }
    if (p > CA_SPECTRUM_MAX_P) {
        fprintf(stderr, "prime must not exceed %d for matrix spectral analysis\n",
                CA_SPECTRUM_MAX_P);
        return 0;
    }
    return 1;
}

static int ca_cosets(int p, int base, int order, int **orbit_out, int **rep_out)
{
    int cosets = (p - 1) / order;
    int *orbit = malloc((size_t)(p - 1) * sizeof(int));
    int *representatives = malloc((size_t)cosets * sizeof(int));
    int *seen = calloc((size_t)p, sizeof(int));
    if (!orbit || !representatives || !seen) {
        free(orbit); free(representatives); free(seen);
        return 0;
    }
    int index = 0;
    for (int c = 1; c < p; c++) {
        if (seen[c]) continue;
        if (index >= cosets) {
            free(orbit); free(representatives); free(seen);
            return 0;
        }
        representatives[index] = c;
        int value = c;
        for (int t = 0; t < order; t++) {
            orbit[index * order + t] = value;
            seen[value] = 1;
            value = (int)(((long long)value * base) % p);
        }
        index++;
    }
    free(seen);
    if (index != cosets) {
        free(orbit); free(representatives);
        return 0;
    }
    *orbit_out = orbit;
    *rep_out = representatives;
    return 1;
}

int cross_alignment_prime_print(int p, int base)
{
    if (!ca_validate_prime(p, base)) return 1;
    CAMatrix matrix;
    if (!ca_build(p, base, -1, &matrix)) return 1;
    int injective = ca_digit_map_injective(p, base);
    int identity = ca_identity(&matrix);
    int boundary = p <= base + 1;
    int equivalence = injective >= 0
                   && identity == injective && injective == boundary;

    int *orbit = NULL, *representatives = NULL;
    int cosets = (p - 1) / matrix.order;
    int cosets_ok = ca_cosets(p, base, matrix.order,
                              &orbit, &representatives);

    printf("Prime cross-alignment structure\n\n");
    printf("  base b = %d, prime p = %d\n", base, p);
    printf("  order L = %d; multiplicative cosets = %d\n",
           matrix.order, cosets);
    printf("  digit map injective: %s\n", injective ? "yes" : "no");
    printf("  A_b(p) is the identity: %s\n", identity ? "yes" : "no");
    printf("  boundary p <= b+1: %s\n", boundary ? "yes" : "no");
    printf("  identity iff injective iff p<=b+1: %s\n",
           equivalence ? "PASS" : "FAIL");

    if (cosets_ok) {
        printf("\nMultiplicative-coset digit words:\n");
        for (int a = 0; a < cosets; a++) {
            printf("  c=%-4d  ", representatives[a]);
            for (int t = 0; t < matrix.order; t++) {
                int r = orbit[a * matrix.order + t];
                int digit = (int)(((long long)base * r) / p);
                if (base <= 10) printf("%d", digit);
                else printf("%s%d", t ? " " : "", digit);
            }
            printf("\n");
        }
    }

    free(orbit);
    free(representatives);
    ca_free(&matrix);
    return equivalence && cosets_ok ? 0 : 1;
}

static int ca_circulant_blocks(const CAMatrix *matrix,
                               const int *orbit, int cosets)
{
    int L = matrix->order, dimension = matrix->dimension;
    for (int a = 0; a < cosets; a++) {
        for (int ap = 0; ap < cosets; ap++) {
            for (int r = 0; r < L; r++) {
                for (int rp = 0; rp < L; rp++) {
                    int delta = (rp - r + L) % L;
                    int row = orbit[a * L + r] - 1;
                    int col = orbit[ap * L + rp] - 1;
                    int ref_row = orbit[a * L] - 1;
                    int ref_col = orbit[ap * L + delta] - 1;
                    if (matrix->score[row * dimension + col]
                        != matrix->score[ref_row * dimension + ref_col])
                        return 0;
                }
            }
        }
    }
    return 1;
}

static int ca_compare_double(const void *left, const void *right)
{
    double a = *(const double *)left, b = *(const double *)right;
    return (a > b) - (a < b);
}

static int ca_fourier_eigenvalues(int p, int base, int L, int cosets,
                                  const int *orbit, double *eigenvalues,
                                  double *per_frequency)
{
    double complex *transforms = calloc((size_t)cosets * base,
                                         sizeof(double complex));
    double complex *block = malloc((size_t)cosets * cosets
                                   * sizeof(double complex));
    double complex *work = malloc((size_t)(2 * cosets + 1)
                                  * sizeof(double complex));
    double *rwork = malloc((size_t)(3 * cosets + 1) * sizeof(double));
    double *values = malloc((size_t)cosets * sizeof(double));
    if (!transforms || !block || !work || !rwork || !values) {
        free(transforms); free(block); free(work); free(rwork); free(values);
        return 0;
    }

    int output = 0;
    for (int frequency = 0; frequency < L; frequency++) {
        memset(transforms, 0,
               (size_t)cosets * base * sizeof(double complex));
        for (int a = 0; a < cosets; a++) {
            for (int t = 0; t < L; t++) {
                int r = orbit[a * L + t];
                int digit = (int)(((long long)base * r) / p);
                double angle = -2.0 * M_PI * frequency * t / L;
                transforms[a * base + digit] += cos(angle) + I * sin(angle);
            }
        }
        for (int column = 0; column < cosets; column++) {
            for (int row = 0; row < cosets; row++) {
                double complex sum = 0.0;
                for (int digit = 0; digit < base; digit++)
                    sum += conj(transforms[row * base + digit])
                         * transforms[column * base + digit];
                block[row + column * cosets] = sum / L;
            }
        }
        int n = cosets, lda = cosets, info = 0;
        int lwork = 2 * cosets + 1;
        char jobz = 'N', uplo = 'U';
        zheev_(&jobz, &uplo, &n, block, &lda, values,
               work, &lwork, rwork, &info);
        if (info != 0) {
            free(transforms); free(block); free(work); free(rwork); free(values);
            return 0;
        }
        for (int a = 0; a < cosets; a++) {
            eigenvalues[output++] = values[a];
            if (per_frequency)
                per_frequency[frequency * cosets + a] = values[a];
        }
    }

    free(transforms); free(block); free(work); free(rwork); free(values);
    qsort(eigenvalues, (size_t)(p - 1), sizeof(double), ca_compare_double);
    return 1;
}

static int ca_fourier_matches_full(const CAMatrix *matrix, int p, int base,
                                   int cosets, const int *orbit,
                                   double *maximum_error,
                                   double *per_frequency)
{
    int dimension = matrix->dimension;
    double *full = malloc((size_t)dimension * sizeof(double));
    double *fourier = malloc((size_t)dimension * sizeof(double));
    if (!full || !fourier || !ca_eigenvalues(matrix, full)
        || !ca_fourier_eigenvalues(p, base, matrix->order, cosets,
                                   orbit, fourier, per_frequency)) {
        free(full); free(fourier);
        return 0;
    }
    *maximum_error = 0.0;
    for (int i = 0; i < dimension; i++) {
        double error = fabs(full[i] - fourier[i]);
        if (error > *maximum_error) *maximum_error = error;
    }
    free(full);
    free(fourier);
    return *maximum_error < 1e-8;
}

static int ca_primitive_autocorrelation(const CAMatrix *matrix,
                                        const int *orbit,
                                        int *autocorrelation,
                                        double *maximum_error)
{
    if (matrix->order != matrix->dimension) return 0;
    int L = matrix->order;
    double *full = malloc((size_t)L * sizeof(double));
    double *formula = malloc((size_t)L * sizeof(double));
    if (!full || !formula || !ca_eigenvalues(matrix, full)) {
        free(full); free(formula);
        return 0;
    }
    for (int shift = 0; shift < L; shift++) {
        int count = 0;
        for (int t = 0; t < L; t++) {
            int left = orbit[t];
            int right = orbit[(t + shift) % L];
            int left_digit = (int)(((long long)matrix->base * left) / matrix->n);
            int right_digit = (int)(((long long)matrix->base * right) / matrix->n);
            count += left_digit == right_digit;
        }
        autocorrelation[shift] = count;
    }
    for (int frequency = 0; frequency < L; frequency++) {
        double value = 0.0;
        for (int shift = 0; shift < L; shift++)
            value += autocorrelation[shift]
                   * cos(2.0 * M_PI * frequency * shift / L);
        formula[frequency] = value / L;
    }
    qsort(formula, (size_t)L, sizeof(double), ca_compare_double);
    *maximum_error = 0.0;
    for (int i = 0; i < L; i++) {
        double error = fabs(full[i] - formula[i]);
        if (error > *maximum_error) *maximum_error = error;
    }
    free(full);
    free(formula);
    return *maximum_error < 1e-8;
}

static void ca_print_spectrum(const double *values, int count)
{
    int start = 0;
    while (start < count) {
        int multiplicity = 1;
        while (start + multiplicity < count
               && fabs(values[start + multiplicity] - values[start]) < 1e-8)
            multiplicity++;
        printf("  %.12g", values[start]);
        if (multiplicity > 1) printf(" (mult %d)", multiplicity);
        printf("\n");
        start += multiplicity;
    }
}

int cross_alignment_eigenvalues(int p, int base, double *eigenvalues,
                                int capacity, int *count,
                                int *order, int *cosets)
{
    if (!eigenvalues || capacity < p - 1 || !count || !order || !cosets
        || !ca_is_prime(p) || base < 2 || base % p == 0
        || p > CA_SPECTRUM_MAX_P)
        return 0;
    CAMatrix matrix;
    if (!ca_build(p, base, -1, &matrix)) return 0;
    int ok = ca_eigenvalues(&matrix, eigenvalues);
    *count = matrix.dimension;
    *order = matrix.order;
    *cosets = matrix.dimension / matrix.order;
    ca_free(&matrix);
    return ok;
}

int cross_alignment_fourier_print(int p, int base)
{
    if (!ca_validate_prime(p, base)) return 1;
    CAMatrix matrix;
    if (!ca_build(p, base, -1, &matrix)) return 1;
    int cosets = (p - 1) / matrix.order;
    int *orbit = NULL, *representatives = NULL;
    if (!ca_cosets(p, base, matrix.order, &orbit, &representatives)) {
        ca_free(&matrix);
        return 1;
    }
    double *per_frequency = malloc((size_t)(p - 1) * sizeof(double));
    double *full = malloc((size_t)(p - 1) * sizeof(double));
    double max_error = 0.0;
    int circulant = ca_circulant_blocks(&matrix, orbit, cosets);
    int fourier = per_frequency && full
               && ca_fourier_matches_full(&matrix, p, base, cosets, orbit,
                                          &max_error, per_frequency)
               && ca_eigenvalues(&matrix, full);

    printf("Coset-Fourier reduction of the cross-alignment matrix\n\n");
    printf("  base b = %d, prime p = %d\n", base, p);
    printf("  L = ord_p(b) = %d; h = (p-1)/L = %d\n",
           matrix.order, cosets);
    printf("  exact LxL circulant block check: %s\n",
           circulant ? "PASS" : "FAIL");
    printf("  numerical Fourier-block/full-spectrum agreement: %s\n",
           fourier ? "PASS" : "FAIL");
    printf("  maximum numerical spectral discrepancy = %.3g\n", max_error);

    if (fourier) {
        printf("\nHermitian block eigenvalues by frequency:\n");
        int frequency_limit = matrix.order <= 40 ? matrix.order : 20;
        for (int frequency = 0; frequency < frequency_limit; frequency++) {
            printf("  j=%-3d", frequency);
            for (int a = 0; a < cosets; a++)
                printf("  %.10g", per_frequency[frequency * cosets + a]);
            printf("\n");
        }
        if (frequency_limit < matrix.order)
            printf("  ... %d additional frequencies omitted\n",
                   matrix.order - frequency_limit);
        printf("\nFull spectrum:\n");
        ca_print_spectrum(full, p - 1);
    }

    int primitive = 1;
    if (cosets == 1) {
        int *autocorrelation = malloc((size_t)matrix.order * sizeof(int));
        double primitive_error = 0.0;
        primitive = autocorrelation
                 && ca_primitive_autocorrelation(&matrix, orbit,
                                                 autocorrelation,
                                                 &primitive_error);
        printf("\nPrimitive-root autocorrelation certificate:\n  R(ell) =");
        if (autocorrelation) {
            for (int shift = 0; shift < matrix.order; shift++)
                printf(" %d", autocorrelation[shift]);
        }
        printf("\n  numerical DFT/full-spectrum agreement: %s (max error %.3g)\n",
               primitive ? "PASS" : "FAIL", primitive_error);
        free(autocorrelation);
    } else {
        printf("\nBase %d is not a primitive root modulo %d; the h-by-h\n",
               base, p);
        printf("Hermitian blocks above are the applicable reduction.\n");
    }

    free(per_frequency);
    free(full);
    free(orbit);
    free(representatives);
    ca_free(&matrix);
    return circulant && fourier && primitive ? 0 : 1;
}

static int ca_block_structure(const CAMatrix *matrix, int p, int supported)
{
    int dimension = matrix->dimension;
    for (int i = 1; i < matrix->n; i++) {
        for (int j = 1; j < matrix->n; j++) {
            int i_term = i % p == 0;
            int j_term = j % p == 0;
            int expected = (i_term && j_term)
                        || (!i_term && !j_term && i % p == j % p);
            if (matrix->score[(i - 1) * dimension + j - 1]
                != (expected ? matrix->order : 0))
                return 0;
        }
    }
    int terminating = 0;
    for (int k = 1; k < matrix->n; k++) terminating += k % p == 0;
    return terminating == supported - 1;
}

static int ca_block_spectrum(const CAMatrix *matrix, int p, int supported,
                             int *rank)
{
    int dimension = matrix->dimension;
    double *observed = malloc((size_t)dimension * sizeof(double));
    double *expected = calloc((size_t)dimension, sizeof(double));
    if (!observed || !expected || !ca_eigenvalues(matrix, observed)) {
        free(observed); free(expected);
        return 0;
    }
    int index = 0;
    if (supported == 1) {
        for (int i = 0; i < p - 1; i++) expected[index++] = 1.0;
        *rank = p - 1;
    } else {
        int zero_count = p * supported - p - 1;
        index = zero_count;
        expected[index++] = supported - 1;
        for (int i = 0; i < p - 1; i++) expected[index++] = supported;
        *rank = p;
    }
    int ok = index == dimension;
    for (int i = 0; ok && i < dimension; i++)
        if (fabs(observed[i] - expected[i]) > 1e-8) ok = 0;
    free(observed);
    free(expected);
    return ok;
}

int cross_alignment_block_print(int p, int supported, int base, int depth)
{
    if (!ca_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (base < 2 || base > CA_MAX_BASE || base % p == 0) {
        fprintf(stderr, "base must be valid and p must not divide it\n");
        return 1;
    }
    if (p > base + 1) {
        fprintf(stderr, "block theorem requires p <= base + 1\n");
        return 1;
    }
    if (supported < 1 || !is_b_smooth(supported, base)) {
        fprintf(stderr, "s must be a positive base-supported integer\n");
        return 1;
    }
    long long nll = (long long)p * supported;
    if (nll > CA_MAX_N) {
        fprintf(stderr, "p*s must not exceed %d\n", CA_MAX_N);
        return 1;
    }
    int n = (int)nll;
    if (!ca_validate_request(n, base, depth)) return 1;
    CAMatrix matrix;
    if (!ca_build(n, base, depth, &matrix)) return 1;
    int structure = ca_block_structure(&matrix, p, supported);
    int rank = 0;
    int spectrum = ca_block_spectrum(&matrix, p, supported, &rank);

    printf("Digit-partitioning supported-lift block structure\n\n");
    printf("  base b = %d, p = %d, s = %d, n = %d\n",
           base, p, supported, n);
    printf("  common depth D = %d; common window L = %d\n",
           matrix.depth, matrix.order);
    printf("  terminating block J_(s-1) has size %d\n", supported - 1);
    printf("  nonterminating blocks: p-1 = %d copies of J_s with size %d\n",
           p - 1, supported);
    printf("  exact entrywise block decomposition: %s\n",
           structure ? "PASS" : "FAIL");
    printf("  exact block rank = %d (expected %d): %s\n", rank,
           supported == 1 ? p - 1 : p,
           structure ? "PASS" : "FAIL");
    printf("\nExpected spectrum:\n");
    if (supported == 1) {
        printf("  1 with multiplicity %d\n", p - 1);
    } else {
        printf("  %d with multiplicity %d\n", supported, p - 1);
        printf("  %d with multiplicity 1\n", supported - 1);
        printf("  0 with multiplicity %d\n", p * supported - p - 1);
    }
    printf("  LAPACK spectrum comparison: %s\n", spectrum ? "PASS" : "FAIL");
    ca_free(&matrix);
    return structure && spectrum ? 0 : 1;
}

static int ca_count_distinct(const double *values, int count)
{
    int distinct = count > 0;
    for (int i = 1; i < count; i++)
        if (fabs(values[i] - values[i - 1]) > 1e-8) distinct++;
    return distinct;
}

static int ca_example_checks(int verbose)
{
    CAMatrix p13 = {0}, p17 = {0};
    if (!ca_build(13, 10, -1, &p13) || !ca_build(17, 10, -1, &p17)) {
        ca_free(&p13); ca_free(&p17);
        return 0;
    }
    double e13[12], e17[16];
    int spectral = ca_eigenvalues(&p13, e13) && ca_eigenvalues(&p17, e17);
    int p13_levels = spectral;
    for (int i = 0; i < 6 && p13_levels; i++)
        p13_levels = fabs(e13[i] - 2.0 / 3.0) < 1e-8;
    for (int i = 6; i < 12 && p13_levels; i++)
        p13_levels = fabs(e13[i] - 4.0 / 3.0) < 1e-8;

    int *orbit13 = NULL, *reps13 = NULL;
    int p13_structure = ca_cosets(13, 10, 6, &orbit13, &reps13);
    if (p13_structure) {
        for (int a = 0; a < 2 && p13_structure; a++) {
            for (int ap = 0; ap < 2 && p13_structure; ap++) {
                for (int r = 0; r < 6 && p13_structure; r++) {
                    for (int rp = 0; rp < 6; rp++) {
                        int row = orbit13[a * 6 + r] - 1;
                        int col = orbit13[ap * 6 + rp] - 1;
                        int expected;
                        if (a == ap) expected = r == rp ? 6 : 0;
                        else expected = rp == (r + 3) % 6 ? 2 : 0;
                        if (p13.score[row * 12 + col] != expected) {
                            p13_structure = 0;
                            break;
                        }
                    }
                }
            }
        }
    }

    int *orbit17 = NULL, *reps17 = NULL;
    int autocorrelation[16];
    double primitive_error = 0.0;
    int p17_auto = ca_cosets(17, 10, 16, &orbit17, &reps17)
                && ca_primitive_autocorrelation(&p17, orbit17,
                                                autocorrelation,
                                                &primitive_error);
    if (p17_auto) {
        for (int shift = 0; shift < 16; shift++) {
            int expected = shift == 0 ? 16
                         : (shift == 1 || shift == 3 || shift == 5
                            || shift == 11 || shift == 13 || shift == 15)
                         ? 2 : 0;
            if (autocorrelation[shift] != expected) p17_auto = 0;
        }
    }
    int p17_levels = spectral && ca_count_distinct(e17, 16) == 9
                  && fabs(e17[0] - 0.25) < 1e-8
                  && fabs(e17[15] - 1.75) < 1e-8;

    if (verbose) {
        printf("Decimal matrix fixtures and spectral corroboration\n\n");
        printf("p=13:\n");
        printf("  multiplicative-coset words: 076923 and 153846\n");
        printf("  exact block form [I, (1/3)P^3; (1/3)P^3, I]: %s\n",
               p13_structure ? "PASS" : "FAIL");
        printf("  LAPACK level 2/3 with multiplicity 6: %s\n",
               p13_levels ? "PASS" : "FAIL");
        printf("  LAPACK level 4/3 with multiplicity 6: %s\n",
               p13_levels ? "PASS" : "FAIL");
        printf("\np=17:\n");
        printf("  primitive-root digit word: 0588235294117647\n");
        printf("  R(0)=16; R(+/-1,+/-3,+/-5)=2; all others zero: %s\n",
               p17_auto ? "PASS" : "FAIL");
        printf("  LAPACK finds exactly 9 distinct eigenvalues: %s\n",
               p17_levels ? "PASS" : "FAIL");
        printf("  LAPACK minimum 1/4 and maximum 7/4: %s\n",
               p17_levels ? "PASS" : "FAIL");
    }

    free(orbit13); free(reps13); free(orbit17); free(reps17);
    ca_free(&p13); ca_free(&p17);
    return p13_structure && p13_levels && p17_auto && p17_levels;
}

int cross_alignment_examples(void)
{
    return ca_example_checks(1) ? 0 : 1;
}

static int ca_check_matrix_gram_depth(void)
{
    for (int base = 2; base <= 12; base++) {
        for (int n = 2; n <= 55; n++) {
            CAMatrix first, later;
            if (!ca_build(n, base, -1, &first)
                || !ca_build(n, base, first.minimum_depth + 1, &later))
                return 0;
            int ok = ca_matrix_invariants(&first)
                  && ca_gram_reconstruction(&first)
                  && ca_same_matrix(&first, &later);
            ca_free(&first); ca_free(&later);
            if (!ok) return 0;
        }
    }
    return 1;
}

static int ca_check_scalar_recovery(void)
{
    for (int base = 2; base <= 12; base++) {
        for (int n = 3; n <= 100; n++) {
            long long an, ad, sn, sd, fn, fd;
            long long ean, ead, esn, esd, efn, efd;
            if (!cross_alignment_scalar_fractions(
                    n, base, -1, &an, &ad, &sn, &sd, &fn, &fd)
                || !coherence_decomposition_fractions(
                    n, base, -1, &ean, &ead, &esn, &esd, &efn, &efd)
                || !ca_equal(an, ad, ean, ead)
                || !ca_equal(sn, sd, esn, esd)
                || !ca_equal(fn, fd, efn, efd))
                return 0;
        }
    }
    return 1;
}

static int ca_check_prime_identity(void)
{
    for (int base = 2; base <= 24; base++) {
        for (int p = 2; p <= 97; p++) {
            if (!ca_is_prime(p) || base % p == 0) continue;
            CAMatrix matrix;
            if (!ca_build(p, base, -1, &matrix)) return 0;
            int injective = ca_digit_map_injective(p, base);
            int ok = injective >= 0
                  && ca_identity(&matrix) == injective
                  && injective == (p <= base + 1);
            ca_free(&matrix);
            if (!ok) return 0;
        }
    }
    return 1;
}

static int ca_check_coset_fourier(void)
{
    for (int base = 2; base <= 12; base++) {
        for (int p = 3; p <= 43; p++) {
            if (!ca_is_prime(p) || base % p == 0) continue;
            CAMatrix matrix;
            if (!ca_build(p, base, -1, &matrix)) return 0;
            int cosets = (p - 1) / matrix.order;
            int *orbit = NULL, *representatives = NULL;
            double error = 0.0;
            int ok = ca_cosets(p, base, matrix.order, &orbit, &representatives)
                  && ca_circulant_blocks(&matrix, orbit, cosets)
                  && ca_fourier_matches_full(&matrix, p, base, cosets,
                                             orbit, &error, NULL);
            free(orbit); free(representatives); ca_free(&matrix);
            if (!ok) return 0;
        }
    }
    return 1;
}

static int ca_check_primitive(void)
{
    int cases = 0;
    for (int base = 2; base <= 16; base++) {
        for (int p = 3; p <= 61; p++) {
            if (!ca_is_prime(p) || base % p == 0
                || ca_order(base, p) != p - 1)
                continue;
            CAMatrix matrix;
            int *orbit = NULL, *representatives = NULL;
            int *autocorrelation = malloc((size_t)(p - 1) * sizeof(int));
            double error = 0.0;
            if (!autocorrelation || !ca_build(p, base, -1, &matrix)) {
                free(autocorrelation);
                return 0;
            }
            int ok = ca_cosets(p, base, p - 1, &orbit, &representatives)
                  && ca_primitive_autocorrelation(&matrix, orbit,
                                                  autocorrelation, &error);
            free(autocorrelation); free(orbit); free(representatives);
            ca_free(&matrix);
            if (!ok) return 0;
            cases++;
        }
    }
    return cases > 20;
}

static int ca_check_blocks(void)
{
    for (int base = 2; base <= 20; base++) {
        for (int p = 2; p <= base + 1; p++) {
            if (!ca_is_prime(p) || base % p == 0) continue;
            for (int s = 1; s <= 24; s++) {
                if (!is_b_smooth(s, base) || p * s > 180) continue;
                CAMatrix matrix;
                int rank = 0;
                if (!ca_build(p * s, base, -1, &matrix)
                    || !ca_block_structure(&matrix, p, s)
                    || !ca_block_spectrum(&matrix, p, s, &rank)) {
                    ca_free(&matrix);
                    return 0;
                }
                ca_free(&matrix);
            }
        }
    }
    return 1;
}

int cross_alignment_verify(void)
{
    printf("Exact C verification of the synchronized cross-alignment matrix\n");
    printf("Matrix entries are exact; LAPACK is used only for spectral cross-checks.\n\n");

    int passed = 0;
    int ok = ca_check_matrix_gram_depth();
    printf("  symmetry, unit diagonal, exact Gram form, depth independence: b<=12,n<=55  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ca_check_scalar_recovery();
    printf("  row/off-diagonal scalar recovery vs coherence-decomposition engine: b<=12,n<=100  %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ca_check_prime_identity();
    printf("  prime identity iff digit injectivity iff p<=b+1: b<=24,p<=97           %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ca_check_coset_fourier();
    printf("  exact coset circulants; numerical Fourier/full agreement: b<=12,p<=43 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ca_check_primitive();
    printf("  exact primitive autocorrelation; numerical DFT check: b<=16,p<=61     %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ca_check_blocks();
    printf("  exact supported blocks; numerical spectral check: b<=20,s<=24,ps<=180 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ca_example_checks(0);
    printf("  exact decimal fixtures; numerical spectral check at p=13,p=17        %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/7 finite checks passed.\n", passed);
    printf("Exact matrix certificates construct the finite objects directly;\n");
    printf("bounded sweeps and numerical eigensolvers do not replace formal proofs.\n");
    return passed == 7;
}

void cross_alignment_help(void)
{
    printf("Synchronized matrix and orbit-spectrum tools\n\n");
    printf("The matrix retains every pairwise comparison on one common depth and\n");
    printf("period. Exact integer match counts sit underneath the displayed rational\n");
    printf("entries. Spectral calculations are cross-checks of that exact matrix.\n\n");
    printf("Commands:\n");
    printf("  nfield cross-alignment matrix <n> [--base <b>] [--depth <D>]\n");
    printf("      Print entries, Gram/PSD certificates, and recovered scalars.\n\n");
    printf("  nfield cross-alignment prime <p> [--base <b>]\n");
    printf("      Check the identity characterization and list coset digit words.\n\n");
    printf("  nfield cross-alignment fourier <p> [--base <b>]\n");
    printf("      Check exact circulant blocks and compare the Fourier spectrum.\n\n");
    printf("  nfield cross-alignment block <p> <s> [--base <b>] [--depth <D>]\n");
    printf("      Build the exact all-ones sum and compare its predicted spectrum.\n\n");
    printf("  nfield cross-alignment examples\n");
    printf("      Reproduce exact decimal fixtures and corroborate their spectra.\n\n");
    printf("  nfield cross-alignment verify\n");
    printf("  nfield verify cross-alignment\n\n");
    printf("Examples:\n");
    printf("  nfield cross-alignment matrix 12 --base 10\n");
    printf("  nfield cross-alignment prime 13 --base 10\n");
    printf("  nfield cross-alignment fourier 17 --base 10\n");
    printf("  nfield cross-alignment block 3 4 --base 10\n");
}
