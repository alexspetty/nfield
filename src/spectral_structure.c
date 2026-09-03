/*
 * spectral_structure.c: Finite multiplicative orbit-frequency tools.
 *
 * The synchronized cross-alignment matrix itself is built from exact integer
 * match counts.  Orbit words, occupied bins, cyclic equality counts, and the
 * partition-of-unity checks are exact.  Complex Fourier fibers and their
 * thresholded ranks and eigenvalues are evaluated in double precision with
 * LAPACK at tolerance 1e-8 and are labeled as numerical corroboration.
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

#define SS_MAX_P 241
#define SS_MAX_BASE 1000
#define SS_TOL 1e-8

extern void zheev_(char *jobz, char *uplo, int *n, double complex *a,
                   int *lda, double *w, double complex *work, int *lwork,
                   double *rwork, int *info);

typedef struct {
    int p;
    int base;
    int L;
    int C;
    int nu;
    int *representatives;
    int *orbit;
    int *digits;
    int *score;
    int *fiber_rank;
    double *fiber_eigenvalues;
    double *full_eigenvalues;
} SSModel;

static int ss_gcd(int a, int b)
{
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a < 0 ? -a : a;
}

static long long ss_gcdll(long long a, long long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = b;
        b = a % b;
        a = t;
    }
    return a ? a : 1;
}

static int ss_is_prime(int n)
{
    if (n < 2) return 0;
    if (n % 2 == 0) return n == 2;
    for (int d = 3; d <= n / d; d += 2)
        if (n % d == 0) return 0;
    return 1;
}

static int ss_order(int base, int p)
{
    if (p < 2 || ss_gcd(base, p) != 1) return -1;
    int value = base % p;
    int L = 1;
    while (value != 1 && L <= p) {
        value = (int)(((long long)value * base) % p);
        L++;
    }
    return value == 1 ? L : -1;
}

static int ss_min(int a, int b)
{
    return a < b ? a : b;
}

static int ss_positive_part(int x)
{
    return x > 0 ? x : 0;
}

static int ss_compare_double(const void *left, const void *right)
{
    double a = *(const double *)left;
    double b = *(const double *)right;
    return (a > b) - (a < b);
}

static void ss_free(SSModel *model)
{
    free(model->representatives);
    free(model->orbit);
    free(model->digits);
    free(model->score);
    free(model->fiber_rank);
    free(model->fiber_eigenvalues);
    free(model->full_eigenvalues);
    memset(model, 0, sizeof(*model));
}

static int ss_validate(int p, int base)
{
    if (!ss_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 0;
    }
    if (base < 2 || base > SS_MAX_BASE) {
        fprintf(stderr, "base must be between 2 and %d\n", SS_MAX_BASE);
        return 0;
    }
    if (base % p == 0) {
        fprintf(stderr, "p must not divide the base\n");
        return 0;
    }
    if (p > SS_MAX_P) {
        fprintf(stderr, "prime must not exceed %d for spectral-structure analysis\n",
                SS_MAX_P);
        return 0;
    }
    return 1;
}

static int ss_frequency_vectors(const SSModel *model, int frequency,
                                double complex *vectors)
{
    if (!vectors || frequency < 0 || frequency >= model->L) return 0;
    memset(vectors, 0,
           (size_t)model->C * model->base * sizeof(double complex));
    for (int a = 0; a < model->C; a++) {
        for (int t = 0; t < model->L; t++) {
            int digit = model->digits[a * model->L + t];
            double angle = -2.0 * M_PI * frequency * t / model->L;
            vectors[a * model->base + digit] +=
                cos(angle) + I * sin(angle);
        }
    }
    return 1;
}

static int ss_compute_fibers(SSModel *model)
{
    int C = model->C;
    double complex *vectors = calloc((size_t)C * model->base,
                                     sizeof(double complex));
    double complex *block = malloc((size_t)C * C * sizeof(double complex));
    int lwork = 2 * C + 1;
    double complex *work = malloc((size_t)lwork * sizeof(double complex));
    double *rwork = malloc((size_t)(3 * C + 1) * sizeof(double));
    double *values = malloc((size_t)C * sizeof(double));
    if (!vectors || !block || !work || !rwork || !values) {
        free(vectors); free(block); free(work); free(rwork); free(values);
        return 0;
    }

    for (int j = 0; j < model->L; j++) {
        ss_frequency_vectors(model, j, vectors);
        for (int column = 0; column < C; column++) {
            for (int row = 0; row < C; row++) {
                double complex sum = 0.0;
                for (int digit = 0; digit < model->base; digit++)
                    sum += conj(vectors[row * model->base + digit])
                         * vectors[column * model->base + digit];
                block[row + column * C] = sum / model->L;
            }
        }
        int n = C, lda = C, info = 0;
        char jobz = 'N', uplo = 'U';
        zheev_(&jobz, &uplo, &n, block, &lda, values,
               work, &lwork, rwork, &info);
        if (info != 0) {
            free(vectors); free(block); free(work); free(rwork); free(values);
            return 0;
        }
        int rank = 0;
        for (int a = 0; a < C; a++) {
            model->fiber_eigenvalues[j * C + a] = values[a];
            if (values[a] > SS_TOL) rank++;
        }
        model->fiber_rank[j] = rank;
    }

    free(vectors); free(block); free(work); free(rwork); free(values);
    return 1;
}

static int ss_build(int p, int base, SSModel *model)
{
    memset(model, 0, sizeof(*model));
    if (!ss_is_prime(p) || base < 2 || base > SS_MAX_BASE
        || base % p == 0 || p > SS_MAX_P)
        return 0;

    int L = ss_order(base, p);
    if (L < 1 || (p - 1) % L != 0) return 0;
    int C = (p - 1) / L;
    int *representatives = malloc((size_t)C * sizeof(int));
    int *orbit = malloc((size_t)(p - 1) * sizeof(int));
    int *digits = malloc((size_t)(p - 1) * sizeof(int));
    int *score = calloc((size_t)(p - 1) * (p - 1), sizeof(int));
    int *fiber_rank = calloc((size_t)L, sizeof(int));
    double *fiber_eigenvalues = malloc((size_t)(p - 1) * sizeof(double));
    double *full_eigenvalues = malloc((size_t)(p - 1) * sizeof(double));
    int *seen = calloc((size_t)p, sizeof(int));
    int *occupied = calloc((size_t)base, sizeof(int));
    if (!representatives || !orbit || !digits || !score || !fiber_rank
        || !fiber_eigenvalues || !full_eigenvalues || !seen || !occupied) {
        free(representatives); free(orbit); free(digits); free(score);
        free(fiber_rank); free(fiber_eigenvalues); free(full_eigenvalues);
        free(seen); free(occupied);
        return 0;
    }

    int a = 0;
    for (int c = 1; c < p; c++) {
        if (seen[c]) continue;
        if (a >= C) {
            free(representatives); free(orbit); free(digits); free(score);
            free(fiber_rank); free(fiber_eigenvalues); free(full_eigenvalues);
            free(seen); free(occupied);
            return 0;
        }
        representatives[a] = c;
        int residue = c;
        for (int t = 0; t < L; t++) {
            int digit = (int)(((long long)base * residue) / p);
            orbit[a * L + t] = residue;
            digits[a * L + t] = digit;
            occupied[digit] = 1;
            seen[residue] = 1;
            residue = (int)(((long long)residue * base) % p);
        }
        a++;
    }
    free(seen);
    if (a != C) {
        free(representatives); free(orbit); free(digits); free(score);
        free(fiber_rank); free(fiber_eigenvalues); free(full_eigenvalues);
        free(occupied);
        return 0;
    }

    int nu = 0;
    for (int d = 0; d < base; d++) nu += occupied[d];
    free(occupied);

    for (int r = 1; r < p; r++) {
        for (int s = r; s < p; s++) {
            int rr = r, ss = s, matches = 0;
            for (int t = 0; t < L; t++) {
                matches += ((long long)base * rr) / p
                        == ((long long)base * ss) / p;
                rr = (int)(((long long)rr * base) % p);
                ss = (int)(((long long)ss * base) % p);
            }
            score[(r - 1) * (p - 1) + (s - 1)] = matches;
            score[(s - 1) * (p - 1) + (r - 1)] = matches;
        }
    }

    model->p = p;
    model->base = base;
    model->L = L;
    model->C = C;
    model->nu = nu;
    model->representatives = representatives;
    model->orbit = orbit;
    model->digits = digits;
    model->score = score;
    model->fiber_rank = fiber_rank;
    model->fiber_eigenvalues = fiber_eigenvalues;
    model->full_eigenvalues = full_eigenvalues;

    int count = 0, order = 0, cosets = 0;
    if (!ss_compute_fibers(model)
        || !cross_alignment_eigenvalues(p, base, full_eigenvalues, p - 1,
                                        &count, &order, &cosets)
        || count != p - 1 || order != L || cosets != C) {
        ss_free(model);
        return 0;
    }
    return 1;
}

static int ss_partition_unity(const SSModel *model)
{
    double complex *vectors = calloc((size_t)model->C * model->base,
                                     sizeof(double complex));
    if (!vectors) return 0;
    int ok = 1;
    for (int j = 0; j < model->L && ok; j++) {
        ss_frequency_vectors(model, j, vectors);
        for (int a = 0; a < model->C; a++) {
            double complex sum = 0.0;
            for (int d = 0; d < model->base; d++)
                sum += vectors[a * model->base + d];
            double expected = j == 0 ? model->L : 0.0;
            if (cabs(sum - expected) > SS_TOL) ok = 0;
        }
    }
    free(vectors);
    return ok;
}

static int ss_spectrum_matches_fibers(const SSModel *model, double *max_error)
{
    double *fiber = malloc((size_t)(model->p - 1) * sizeof(double));
    if (!fiber) return 0;
    memcpy(fiber, model->fiber_eigenvalues,
           (size_t)(model->p - 1) * sizeof(double));
    qsort(fiber, (size_t)(model->p - 1), sizeof(double), ss_compare_double);
    *max_error = 0.0;
    for (int i = 0; i < model->p - 1; i++) {
        double error = fabs(fiber[i] - model->full_eigenvalues[i]);
        if (error > *max_error) *max_error = error;
    }
    free(fiber);
    return *max_error < SS_TOL;
}

static int ss_rank_sum(const SSModel *model)
{
    int rank = 0;
    for (int j = 0; j < model->L; j++) rank += model->fiber_rank[j];
    return rank;
}

static int ss_full_rank(const SSModel *model)
{
    int rank = 0;
    for (int i = 0; i < model->p - 1; i++)
        if (model->full_eigenvalues[i] > SS_TOL) rank++;
    return rank;
}

static int ss_rank_bound(const SSModel *model)
{
    return ss_min(model->C, model->nu)
         + (model->L - 1) * ss_min(model->C, model->nu - 1);
}

static int ss_nullity_bound(const SSModel *model)
{
    return ss_positive_part(model->C - model->nu)
         + (model->L - 1)
           * ss_positive_part(model->C - model->nu + 1);
}

static int ss_fiber_bounds(const SSModel *model)
{
    if (model->fiber_rank[0] > ss_min(model->C, model->nu)) return 0;
    for (int j = 1; j < model->L; j++)
        if (model->fiber_rank[j] > ss_min(model->C, model->nu - 1))
            return 0;
    return 1;
}

static long long ss_off_diagonal_square_sum(const SSModel *model)
{
    long long total = 0;
    int n = model->p - 1;
    for (int r = 0; r < n; r++)
        for (int s = 0; s < n; s++)
            if (r != s) {
                long long value = model->score[r * n + s];
                total += value * value;
            }
    return total;
}

static double ss_eigenvalue_excess(const SSModel *model)
{
    double total = 0.0;
    for (int i = 0; i < model->p - 1; i++) {
        double centered = model->full_eigenvalues[i] - 1.0;
        total += centered * centered;
    }
    return total;
}

static int ss_words_distinct(const SSModel *model, int a)
{
    for (int i = 0; i < model->L; i++)
        for (int j = i + 1; j < model->L; j++)
            if (model->digits[a * model->L + i]
                == model->digits[a * model->L + j])
                return 0;
    return 1;
}

static void ss_cross_equality(const SSModel *model, int *Q)
{
    for (int shift = 0; shift < model->L; shift++) {
        int count = 0;
        for (int t = 0; t < model->L; t++)
            count += model->digits[t]
                  == model->digits[model->L + (t + shift) % model->L];
        Q[shift] = count;
    }
}

static int ss_support_size(const int *values, int count, int *mass,
                           int *location)
{
    int support = 0;
    *mass = 0;
    *location = -1;
    for (int i = 0; i < count; i++) {
        if (values[i] > 0) {
            support++;
            *mass = values[i];
            *location = i;
        }
    }
    return support;
}

static int ss_distinct_levels(const SSModel *model, int *multiplicities,
                              double *levels, int capacity)
{
    int distinct = 0;
    for (int i = 0; i < model->p - 1;) {
        int multiplicity = 1;
        while (i + multiplicity < model->p - 1
               && fabs(model->full_eigenvalues[i + multiplicity]
                       - model->full_eigenvalues[i]) < SS_TOL)
            multiplicity++;
        if (distinct < capacity) {
            levels[distinct] = model->full_eigenvalues[i];
            multiplicities[distinct] = multiplicity;
        }
        distinct++;
        i += multiplicity;
    }
    return distinct;
}

static int ss_two_coset_branches_ok(const SSModel *model, double *max_error)
{
    if (model->C != 2) return 0;
    double complex *vectors = calloc((size_t)2 * model->base,
                                     sizeof(double complex));
    if (!vectors) return 0;
    *max_error = 0.0;
    for (int j = 0; j < model->L; j++) {
        ss_frequency_vectors(model, j, vectors);
        double q1 = 0.0, q2 = 0.0;
        double complex z = 0.0;
        for (int d = 0; d < model->base; d++) {
            double complex x1 = vectors[d];
            double complex x2 = vectors[model->base + d];
            q1 += creal(conj(x1) * x1);
            q2 += creal(conj(x2) * x2);
            z += conj(x1) * x2;
        }
        double discriminant = sqrt((q1 - q2) * (q1 - q2)
                                   + 4.0 * cabs(z) * cabs(z));
        double expected[2] = {
            (q1 + q2 - discriminant) / (2.0 * model->L),
            (q1 + q2 + discriminant) / (2.0 * model->L)
        };
        for (int branch = 0; branch < 2; branch++) {
            double error = fabs(expected[branch]
                              - model->fiber_eigenvalues[j * 2 + branch]);
            if (error > *max_error) *max_error = error;
        }
    }
    free(vectors);
    return *max_error < SS_TOL;
}

static int ss_two_level_observed(const SSModel *model)
{
    int multiplicities[4] = {0};
    double levels[4] = {0.0};
    int distinct = ss_distinct_levels(model, multiplicities, levels, 4);
    return distinct == 2
        && multiplicities[0] == model->L
        && multiplicities[1] == model->L
        && fabs(levels[0] + levels[1] - 2.0) < SS_TOL;
}

static void ss_print_word(const SSModel *model, int a)
{
    printf("  c=%-4d  ", model->representatives[a]);
    for (int t = 0; t < model->L; t++) {
        int digit = model->digits[a * model->L + t];
        if (model->base <= 10) printf("%d", digit);
        else printf("%s%d", t ? " " : "", digit);
    }
    printf("\n");
}

static void ss_print_fraction(long long numerator, long long denominator)
{
    long long divisor = ss_gcdll(numerator, denominator);
    printf("%lld/%lld", numerator / divisor, denominator / divisor);
}

int spectral_structure_metrics(int p, int base, int *order, int *cosets,
                               int *occupied, int *rank, int *rank_bound,
                               int *nullity, int *nullity_bound)
{
    if (!order || !cosets || !occupied || !rank || !rank_bound
        || !nullity || !nullity_bound)
        return 0;
    SSModel model;
    if (!ss_build(p, base, &model)) return 0;
    *order = model.L;
    *cosets = model.C;
    *occupied = model.nu;
    *rank = ss_full_rank(&model);
    *rank_bound = ss_rank_bound(&model);
    *nullity = p - 1 - *rank;
    *nullity_bound = ss_nullity_bound(&model);
    ss_free(&model);
    return 1;
}

int spectral_structure_cross_equality(int p, int base, int *values,
                                      int capacity, int *count)
{
    if (!values || !count) return 0;
    SSModel model;
    if (!ss_build(p, base, &model)) return 0;
    if (model.C != 2 || capacity < model.L) {
        ss_free(&model);
        return 0;
    }
    ss_cross_equality(&model, values);
    *count = model.L;
    ss_free(&model);
    return 1;
}

int spectral_structure_inspect(int p, int base)
{
    if (!ss_validate(p, base)) return 1;
    SSModel model;
    if (!ss_build(p, base, &model)) return 1;

    double max_error = 0.0;
    int partition = ss_partition_unity(&model);
    int spectral = ss_spectrum_matches_fibers(&model, &max_error);
    int rank = ss_full_rank(&model);
    int rank_sum = ss_rank_sum(&model);
    int rank_bound = ss_rank_bound(&model);
    int nullity = p - 1 - rank;
    int nullity_bound = ss_nullity_bound(&model);
    int occupied = model.nu == ss_min(base, p - 1);
    int fiber_bounds = ss_fiber_bounds(&model);
    long long offdiag = ss_off_diagonal_square_sum(&model);
    long long excess_denominator = (long long)model.L * model.L;
    double eigen_excess = ss_eigenvalue_excess(&model);
    double score_excess = (double)offdiag / excess_denominator;
    int excess = fabs(eigen_excess - score_excess) < SS_TOL;
    int identity_boundary = (offdiag == 0) == (p <= base + 1);
    int all_full_rank = 1;
    for (int j = 0; j < model.L; j++)
        if (model.fiber_rank[j] != model.C) all_full_rank = 0;
    int positive_definite = model.full_eigenvalues[0] > SS_TOL;

    printf("Multiplicative orbit-frequency structure\n\n");
    printf("  base b = %d; prime p = %d\n", base, p);
    printf("  orbit length L = %d; cosets C = %d\n", model.L, model.C);
    printf("  occupied digit bins nu = %d; min(b,p-1) = %d  %s\n",
           model.nu, ss_min(base, p - 1), occupied ? "PASS" : "FAIL");
    printf("  digit indicators partition unity at every orbit position: %s\n",
           partition ? "PASS" : "FAIL");

    printf("\nMultiplicative-coset digit words:\n");
    int word_limit = model.C <= 20 ? model.C : 20;
    for (int a = 0; a < word_limit; a++) ss_print_word(&model, a);
    if (word_limit < model.C)
        printf("  ... %d additional cosets omitted\n", model.C - word_limit);

    printf("\nFrequency-fiber ranks (numerical, tolerance 1e-8):\n  ");
    int frequency_limit = model.L <= 40 ? model.L : 40;
    for (int j = 0; j < frequency_limit; j++)
        printf("j=%d:%d%s", j, model.fiber_rank[j],
               j + 1 == frequency_limit ? "" : "  ");
    if (frequency_limit < model.L) printf("  ...");
    printf("\n");
    printf("  numerical rank(A) = %d; sum_j rank(Y_j) = %d  %s\n",
           rank, rank_sum, rank == rank_sum ? "PASS" : "FAIL");
    printf("  exact rank bound = %d; numerical rank <= bound: %s\n",
           rank_bound, rank <= rank_bound && fiber_bounds ? "PASS" : "FAIL");
    printf("  numerical nullity(A) = %d; exact forced lower bound = %d  %s\n",
           nullity, nullity_bound,
           nullity >= nullity_bound ? "PASS" : "FAIL");
    if (model.C >= model.nu) {
        int forced = model.L * (model.C - model.nu + 1) - 1;
        printf("  exact C>=nu forced-kernel bound: nullity >= %d  %s\n",
               forced, nullity >= forced ? "PASS" : "FAIL");
    }
    printf("  numerical positive-definite/full-column-rank agreement: %s\n",
           positive_definite == all_full_rank ? "PASS" : "FAIL");
    printf("  numerical Fourier/full-matrix spectrum agreement: %s",
           spectral ? "PASS" : "FAIL");
    printf(" (max numerical error %.3g)\n", max_error);

    printf("\nSpectral excess certificate:\n  exact off-diagonal square sum = ");
    ss_print_fraction(offdiag, excess_denominator);
    printf("; numerical eigenvalue sum = %.12g  %s\n", eigen_excess,
           excess ? "PASS" : "FAIL");
    printf("  exact zero boundary p<=b+1: %s\n",
           identity_boundary ? "PASS" : "FAIL");

    int ok = occupied && partition && spectral && rank == rank_sum
          && rank <= rank_bound && fiber_bounds
          && nullity >= nullity_bound && excess && identity_boundary
          && positive_definite == all_full_rank;
    printf("\nResult: %s\n", ok ? "PASS" : "FAIL");
    printf("Exact words, counts, and bounds define the finite object. Numerical\n");
    printf("ranks and spectra above use LAPACK at tolerance 1e-8.\n");
    ss_free(&model);
    return ok ? 0 : 1;
}

int spectral_structure_two_coset(int p, int base)
{
    if (!ss_validate(p, base)) return 1;
    SSModel model;
    if (!ss_build(p, base, &model)) return 1;
    if (model.C != 2) {
        fprintf(stderr, "two-coset analysis requires (p-1)/ord_p(b) = 2; got %d\n",
                model.C);
        ss_free(&model);
        return 1;
    }

    int *Q = calloc((size_t)model.L, sizeof(int));
    double complex *vectors = calloc((size_t)2 * model.base,
                                     sizeof(double complex));
    if (!Q || !vectors) {
        free(Q); free(vectors); ss_free(&model);
        return 1;
    }
    ss_cross_equality(&model, Q);
    int mass = 0, location = -1;
    int support = ss_support_size(Q, model.L, &mass, &location);
    int distinct_words = ss_words_distinct(&model, 0)
                      && ss_words_distinct(&model, 1);
    int criterion = support == 1 && mass > 0;
    int observed = ss_two_level_observed(&model);
    double branch_error = 0.0;
    int branches = ss_two_coset_branches_ok(&model, &branch_error);
    int rigidity = !distinct_words || observed == criterion;

    printf("Exact two-coset spectral branches\n\n");
    printf("  base b = %d; prime p = %d; L = %d; C = 2\n", base, p, model.L);
    printf("\nOrbit words:\n");
    ss_print_word(&model, 0);
    ss_print_word(&model, 1);
    printf("  both words have internally distinct digits: %s\n",
           distinct_words ? "yes" : "no");

    printf("\nPer-frequency branches (numerical, tolerance 1e-8):\n");
    for (int j = 0; j < model.L; j++) {
        ss_frequency_vectors(&model, j, vectors);
        double q1 = 0.0, q2 = 0.0;
        double complex z = 0.0;
        for (int d = 0; d < model.base; d++) {
            double complex x1 = vectors[d];
            double complex x2 = vectors[model.base + d];
            q1 += creal(conj(x1) * x1);
            q2 += creal(conj(x2) * x2);
            z += conj(x1) * x2;
        }
        printf("  j=%-3d q1=%-9.5g q2=%-9.5g |z|=%-9.5g  lambda-=%-11.8g lambda+=%-11.8g\n",
               j, q1, q2, cabs(z),
               model.fiber_eigenvalues[2 * j],
               model.fiber_eigenvalues[2 * j + 1]);
    }
    printf("  numerical closed-branch/fiber agreement: %s",
           branches ? "PASS" : "FAIL");
    printf(" (max error %.3g)\n", branch_error);

    printf("\nCyclic cross-equality count Q =");
    for (int shift = 0; shift < model.L; shift++) printf(" %d", Q[shift]);
    printf("\n  nonzero support size = %d", support);
    if (support == 1) printf("; Q = %d*delta_%d", mass, location);
    printf("\n  observed exactly two global levels: %s\n",
           observed ? "yes" : "no");
    if (distinct_words) {
        printf("  two levels iff Q is nonzero at exactly one shift: %s\n",
               rigidity ? "PASS" : "FAIL");
        if (criterion) {
            printf("  exact levels: ");
            ss_print_fraction(model.L - mass, model.L);
            printf(" and ");
            ss_print_fraction(model.L + mass, model.L);
            printf(", each with multiplicity %d\n", model.L);
        }
    } else {
        printf("  rigidity theorem status: not applicable (a word repeats a digit)\n");
    }

    int multiplicities[64] = {0};
    double levels[64] = {0.0};
    int distinct = ss_distinct_levels(&model, multiplicities, levels, 64);
    printf("  numerical global spectrum (tolerance 1e-8): %d level%s\n", distinct,
           distinct == 1 ? "" : "s");
    int level_limit = distinct < 64 ? distinct : 64;
    for (int i = 0; i < level_limit; i++)
        printf("    %.12g (mult %d)\n", levels[i], multiplicities[i]);

    int ok = branches && rigidity;
    printf("\nResult: %s\n", ok ? "PASS" : "FAIL");
    free(Q); free(vectors); ss_free(&model);
    return ok ? 0 : 1;
}

int spectral_structure_character_energy(int p, int base)
{
    if (!ss_validate(p, base)) return 1;
    SSModel model;
    if (!ss_build(p, base, &model)) return 1;
    if (model.C != 1) {
        fprintf(stderr, "character-energy analysis requires a primitive-root base; got %d cosets\n",
                model.C);
        ss_free(&model);
        return 1;
    }

    double complex *vectors = calloc((size_t)model.base,
                                     sizeof(double complex));
    if (!vectors) {
        ss_free(&model);
        return 1;
    }
    double lambda0 = model.fiber_eigenvalues[0];
    int bounded = 1;
    printf("Finite multiplicative character-energy table\n\n");
    printf("  base b = %d is a primitive root modulo p = %d\n", base, p);
    printf("  L = p-1 = %d; occupied bins nu = %d\n\n", model.L, model.nu);
    printf("  %4s %18s %18s\n", "j", "sum_d |X_d(j)|^2", "lambda_j = energy/L");
    for (int j = 0; j < model.L; j++) {
        ss_frequency_vectors(&model, j, vectors);
        double energy = 0.0;
        for (int d = 0; d < model.base; d++)
            energy += creal(conj(vectors[d]) * vectors[d]);
        double lambda = energy / model.L;
        if (lambda > lambda0 + SS_TOL) bounded = 0;
        printf("  %4d %18.10g %18.10g\n", j, energy, lambda);
    }
    printf("\n  0 <= lambda_j <= lambda_0: %s\n", bounded ? "PASS" : "FAIL");
    printf("  These finite multiplicative character-sum energies are distinct from Dirichlet L-values.\n");
    printf("  Numerical Fourier evaluation uses tolerance 1e-8.\n");
    printf("\nResult: %s\n", bounded ? "PASS" : "FAIL");
    free(vectors); ss_free(&model);
    return bounded ? 0 : 1;
}

static int ss_level_fixture(const SSModel *model, const double *expected,
                            const int *multiplicities, int expected_count)
{
    double levels[16] = {0.0};
    int observed_multiplicities[16] = {0};
    int count = ss_distinct_levels(model, observed_multiplicities, levels, 16);
    if (count != expected_count) return 0;
    for (int i = 0; i < count; i++)
        if (fabs(levels[i] - expected[i]) > SS_TOL
            || observed_multiplicities[i] != multiplicities[i])
            return 0;
    return 1;
}

int spectral_structure_examples(void)
{
    SSModel b2p7, b10p13, b4p7;
    int ok1 = ss_build(7, 2, &b2p7);
    int ok2 = ss_build(13, 10, &b10p13);
    int ok3 = ss_build(7, 4, &b4p7);
    if (!ok1 || !ok2 || !ok3) {
        if (ok1) ss_free(&b2p7);
        if (ok2) ss_free(&b10p13);
        if (ok3) ss_free(&b4p7);
        return 1;
    }

    int sharp = b2p7.L == 3 && b2p7.C == 2 && b2p7.nu == 2
             && ss_full_rank(&b2p7) == 4
             && 6 - ss_full_rank(&b2p7) == 2
             && ss_rank_bound(&b2p7) == 4;

    int Q13[6] = {0};
    int Q4[3] = {0};
    ss_cross_equality(&b10p13, Q13);
    ss_cross_equality(&b4p7, Q4);
    int q13 = Q13[0] == 0 && Q13[1] == 0 && Q13[2] == 0
           && Q13[3] == 2 && Q13[4] == 0 && Q13[5] == 0;
    int q4 = Q4[0] == 1 && Q4[1] == 1 && Q4[2] == 0;
    double levels13[] = {2.0 / 3.0, 4.0 / 3.0};
    int multiplicities13[] = {6, 6};
    double levels4[] = {1.0 / 3.0, 2.0 / 3.0, 4.0 / 3.0, 5.0 / 3.0};
    int multiplicities4[] = {1, 2, 2, 1};
    int spectrum13 = ss_level_fixture(&b10p13, levels13, multiplicities13, 2);
    int spectrum4 = ss_level_fixture(&b4p7, levels4, multiplicities4, 4);

    printf("Orbit-frequency exact examples and numerical spectral contrasts\n\n");
    printf("  base 2, p=7: L=3, C=2, nu=2\n");
    printf("    orbit words 001 and 011: %s\n",
           b2p7.digits[0] == 0 && b2p7.digits[1] == 0
           && b2p7.digits[2] == 1 && b2p7.digits[3] == 0
           && b2p7.digits[4] == 1 && b2p7.digits[5] == 1 ? "PASS" : "FAIL");
    printf("    rank=4, nullity=2, and rank bound attained: %s\n",
           sharp ? "PASS" : "FAIL");
    printf("\n  base 10, p=13:\n");
    printf("    Q = 2*delta_3: %s\n", q13 ? "PASS" : "FAIL");
    printf("    levels 2/3 and 4/3, each multiplicity 6: %s\n",
           spectrum13 ? "PASS" : "FAIL");
    printf("\n  base 4, p=7 counterexample:\n");
    printf("    two cosets but Q=(1,1,0): %s\n", q4 ? "PASS" : "FAIL");
    printf("    four levels 1/3, 2/3, 4/3, 5/3: %s\n",
           spectrum4 ? "PASS" : "FAIL");
    printf("    two cosets alone do not force two levels: %s\n",
           q4 && spectrum4 ? "PASS" : "FAIL");

    int words = b2p7.digits[0] == 0 && b2p7.digits[1] == 0
             && b2p7.digits[2] == 1 && b2p7.digits[3] == 0
             && b2p7.digits[4] == 1 && b2p7.digits[5] == 1;
    int ok = words && sharp && q13 && spectrum13 && q4 && spectrum4;
    printf("\nResult: %s\n", ok ? "PASS" : "FAIL");
    ss_free(&b2p7); ss_free(&b10p13); ss_free(&b4p7);
    return ok ? 0 : 1;
}

static int ss_check_occupied(void)
{
    int cases = 0;
    for (int base = 2; base <= 20; base++) {
        for (int p = 2; p <= 97; p++) {
            if (!ss_is_prime(p) || base % p == 0) continue;
            int *seen = calloc((size_t)base, sizeof(int));
            if (!seen) return 0;
            for (int r = 1; r < p; r++)
                seen[(int)(((long long)base * r) / p)] = 1;
            int occupied = 0;
            for (int d = 0; d < base; d++) occupied += seen[d];
            free(seen);
            if (occupied != ss_min(base, p - 1)) return 0;
            cases++;
        }
    }
    return cases > 400;
}

static int ss_check_rank_law(void)
{
    int cases = 0;
    for (int base = 2; base <= 10; base++) {
        for (int p = 2; p <= 43; p++) {
            if (!ss_is_prime(p) || base % p == 0) continue;
            SSModel model;
            double error = 0.0;
            if (!ss_build(p, base, &model)) return 0;
            int rank = ss_full_rank(&model);
            int ok = ss_partition_unity(&model)
                  && ss_spectrum_matches_fibers(&model, &error)
                  && rank == ss_rank_sum(&model)
                  && ss_fiber_bounds(&model)
                  && rank <= ss_rank_bound(&model)
                  && p - 1 - rank >= ss_nullity_bound(&model);
            ss_free(&model);
            if (!ok) return 0;
            cases++;
        }
    }
    return cases > 100;
}

static int ss_check_base_two_sharpness(void)
{
    int order, cosets, occupied, rank, bound, nullity, nullity_bound;
    return spectral_structure_metrics(7, 2, &order, &cosets, &occupied,
                                      &rank, &bound, &nullity, &nullity_bound)
        && order == 3 && cosets == 2 && occupied == 2
        && rank == 4 && bound == 4 && nullity == 2 && nullity_bound == 2;
}

static int ss_check_excess(void)
{
    int cases = 0;
    for (int base = 2; base <= 12; base++) {
        for (int p = 2; p <= 43; p++) {
            if (!ss_is_prime(p) || base % p == 0) continue;
            SSModel model;
            if (!ss_build(p, base, &model)) return 0;
            double exact = (double)ss_off_diagonal_square_sum(&model)
                         / ((double)model.L * model.L);
            int ok = fabs(ss_eigenvalue_excess(&model) - exact) < SS_TOL
                  && ((ss_off_diagonal_square_sum(&model) == 0)
                      == (p <= base + 1));
            ss_free(&model);
            if (!ok) return 0;
            cases++;
        }
    }
    return cases > 100;
}

static int ss_check_two_coset_branches(void)
{
    int cases = 0;
    for (int base = 2; base <= 20; base++) {
        for (int p = 3; p <= 97; p++) {
            if (!ss_is_prime(p) || base % p == 0
                || (p - 1) / ss_order(base, p) != 2)
                continue;
            SSModel model;
            double error = 0.0;
            if (!ss_build(p, base, &model)) return 0;
            int ok = ss_two_coset_branches_ok(&model, &error);
            ss_free(&model);
            if (!ok) return 0;
            cases++;
        }
    }
    return cases > 40;
}

static int ss_check_two_level_rigidity(void)
{
    int cases = 0, saw_p13 = 0, saw_counterexample = 0;
    for (int base = 2; base <= 20; base++) {
        for (int p = 3; p <= 97; p++) {
            if (!ss_is_prime(p) || base % p == 0
                || (p - 1) / ss_order(base, p) != 2)
                continue;
            SSModel model;
            if (!ss_build(p, base, &model)) return 0;
            if (ss_words_distinct(&model, 0) && ss_words_distinct(&model, 1)) {
                int Q[SS_MAX_P] = {0};
                ss_cross_equality(&model, Q);
                int mass = 0, location = -1;
                int support = ss_support_size(Q, model.L, &mass, &location);
                int criterion = support == 1 && mass > 0;
                int observed = ss_two_level_observed(&model);
                if (criterion != observed) { ss_free(&model); return 0; }
                if (base == 10 && p == 13 && criterion) saw_p13 = 1;
                if (base == 4 && p == 7 && !criterion && !observed)
                    saw_counterexample = 1;
                cases++;
            }
            ss_free(&model);
        }
    }
    return cases > 20 && saw_p13 && saw_counterexample;
}

static int ss_check_primitive_energy(void)
{
    int cases = 0;
    for (int base = 2; base <= 16; base++) {
        for (int p = 3; p <= 61; p++) {
            if (!ss_is_prime(p) || base % p == 0
                || ss_order(base, p) != p - 1)
                continue;
            SSModel model;
            if (!ss_build(p, base, &model)) return 0;
            double lambda0 = model.fiber_eigenvalues[0];
            int ok = 1;
            for (int j = 0; j < model.L; j++)
                if (model.fiber_eigenvalues[j] < -SS_TOL
                    || model.fiber_eigenvalues[j] > lambda0 + SS_TOL)
                    ok = 0;
            ss_free(&model);
            if (!ok) return 0;
            cases++;
        }
    }
    return cases > 20;
}

int spectral_structure_verify(void)
{
    printf("Finite verification of multiplicative orbit-frequency structure\n");
    printf("Exact words and counts are separated from numerical LAPACK checks at tolerance 1e-8.\n\n");

    int passed = 0;
    int ok = ss_check_occupied();
    printf("  occupied digit count nu=min(b,p-1): b<=20,p<=97                    %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ss_check_rank_law();
    printf("  exact partition/rank bounds plus numerical fiber decomposition: b<=10,p<=43 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ss_check_base_two_sharpness();
    printf("  exact bound and numerical rank/nullity at base 2, p=7: 4 and 2    %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ss_check_excess();
    printf("  exact off-diagonal energy/numerical spectral excess: b<=12,p<=43 %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ss_check_two_coset_branches();
    printf("  numerical two-coset Hermitian branch agreement: b<=20,p<=97      %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ss_check_two_level_rigidity();
    printf("  two-level iff single-shift Q, including p=13 and counterexample    %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;
    ok = ss_check_primitive_energy();
    printf("  primitive-root finite character energies and lambda_0 bound       %s\n",
           ok ? "PASS" : "FAIL");
    passed += ok;

    printf("\n%d/7 finite checks passed.\n", passed);
    printf("The bounded sweeps exercise the same objects carried by the exact Lean identities.\n");
    return passed == 7;
}

void spectral_structure_help(void)
{
    printf("Multiplicative orbit-frequency structure\n\n");
    printf("This coordinate diagonalizes the synchronized cross-alignment matrix.\n");
    printf("It is distinct from the additive digit-bin spectrum in 'nfield spectral'.\n\n");
    printf("Commands:\n");
    printf("  nfield spectral-structure inspect <p> [--base <b>]\n");
    printf("      Show orbit words, occupied bins, fiber ranks, kernel bounds,\n");
    printf("      positive-definiteness status, and the spectral-excess identity.\n\n");
    printf("  nfield spectral-structure two-coset <p> [--base <b>]\n");
    printf("      Show both closed spectral branches and the exact cyclic count Q.\n\n");
    printf("  nfield spectral-structure character <p> [--base <b>]\n");
    printf("      Show primitive-root finite character-sum energies, distinct from\n");
    printf("      Dirichlet L-values.\n\n");
    printf("  nfield spectral-structure examples\n");
    printf("      Reproduce sharpness at (b,p)=(2,7), the p=13 two-level collapse,\n");
    printf("      and the base-4 p=7 two-coset/four-level counterexample.\n\n");
    printf("  nfield spectral-structure verify\n");
    printf("  nfield verify spectral-structure\n\n");
    printf("Exact integer counts define each finite matrix. Numerical Fourier ranks\n");
    printf("and spectra use LAPACK at tolerance 1e-8 and are labeled in the output.\n");
}
