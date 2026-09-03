/* Finite collision-label quotient and squared normalized Laplacian. */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "nfield.h"

#define FSQ_MAX_PRIMES 300
#define FSQ_MAX_LABELS 300
#define FSQ_JACOBI_TOL 1.0e-13
#define FSQ_CHECK_TOL 5.0e-10

typedef struct {
    int base;
    const int *expected_labels;
    int expected_count;
} FsqDeclaredCase;

typedef struct {
    int prime_count;
    int unit_table_classes;
    int unit_table_failures;
    int nonbase_prime_checks;
    int base_prime_checks;
    int arithmetic_failures;
    int label_count;
    int missing_labels;
    int bulk_multiplicity;
    int quotient_failures;
    int heat_failures;
    int full_operator_failures;
    int inverse_failures;
    int perron_failures;
    double maximum_compression_error;
    double maximum_constant_action_error;
    double maximum_bulk_action_error;
    double maximum_inverse_error;
    double maximum_quotient_factor_error;
    double maximum_perron_error;
    int labels[FSQ_MAX_LABELS];
    int populations[FSQ_MAX_LABELS];
    double quotient_eigenvalues[FSQ_MAX_LABELS];
    double hamiltonian_eigenvalues[FSQ_MAX_LABELS];
} FsqSummary;

static const int fsq_base_seven_labels[] =
    {-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5};
static const int fsq_base_ten_labels[] =
    {-9, -7, -4, -3, -2, -1, 0, 1, 2, 3, 6, 8};
static const int fsq_base_twelve_labels[] =
    {-11, -7, -5, -3, -2, -1, 0, 1, 2, 4, 6, 10};

static int fsq_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0) return 0;
    return 1;
}

static void fsq_generate_primes(int *primes, int count)
{
    int found = 0;
    for (int candidate = 2; found < count; candidate++)
        if (fsq_is_prime(candidate)) primes[found++] = candidate;
}

static void fsq_sort_ints(int *values, int count)
{
    for (int index = 1; index < count; index++) {
        int value = values[index];
        int position = index;
        while (position > 0 && values[position - 1] > value) {
            values[position] = values[position - 1];
            position--;
        }
        values[position] = value;
    }
}

static int fsq_unique_ints(int *values, int count)
{
    int write = 0;
    fsq_sort_ints(values, count);
    for (int read = 0; read < count; read++)
        if (write == 0 || values[read] != values[write - 1])
            values[write++] = values[read];
    return write;
}

static int fsq_label_index(const int *labels, int count, int label)
{
    for (int index = 0; index < count; index++)
        if (labels[index] == label) return index;
    return -1;
}

static void fsq_sort_doubles(double *values, int count)
{
    for (int index = 1; index < count; index++) {
        double value = values[index];
        int position = index;
        while (position > 0 && values[position - 1] > value) {
            values[position] = values[position - 1];
            position--;
        }
        values[position] = value;
    }
}

static int fsq_jacobi(const double *input, int dimension, double *eigenvalues)
{
    size_t entries = (size_t)dimension * (size_t)dimension;
    double *matrix = malloc(entries * sizeof(*matrix));
    if (!matrix) return 0;
    memcpy(matrix, input, entries * sizeof(*matrix));
    int maximum_iterations = 100 * dimension * dimension;
    int converged = 0;
    for (int iteration = 0; iteration < maximum_iterations; iteration++) {
        double largest = 0.0;
        int pivot_row = 0;
        int pivot_column = 0;
        for (int row = 0; row < dimension; row++) {
            for (int column = row + 1; column < dimension; column++) {
                double magnitude = fabs(
                    matrix[(size_t)row * (size_t)dimension +
                           (size_t)column]);
                if (magnitude > largest) {
                    largest = magnitude;
                    pivot_row = row;
                    pivot_column = column;
                }
            }
        }
        if (largest < FSQ_JACOBI_TOL) {
            converged = 1;
            break;
        }
        size_t pp = (size_t)pivot_row * (size_t)dimension +
                    (size_t)pivot_row;
        size_t qq = (size_t)pivot_column * (size_t)dimension +
                    (size_t)pivot_column;
        size_t pq = (size_t)pivot_row * (size_t)dimension +
                    (size_t)pivot_column;
        double diagonal_p = matrix[pp];
        double diagonal_q = matrix[qq];
        double off_diagonal = matrix[pq];
        double theta = (diagonal_q - diagonal_p) / (2.0 * off_diagonal);
        double tangent = theta >= 0.0
            ? 1.0 / (theta + sqrt(1.0 + theta * theta))
            : -1.0 / (-theta + sqrt(1.0 + theta * theta));
        double cosine = 1.0 / sqrt(1.0 + tangent * tangent);
        double sine = tangent * cosine;
        for (int index = 0; index < dimension; index++) {
            if (index == pivot_row || index == pivot_column) continue;
            size_t ip = (size_t)index * (size_t)dimension +
                        (size_t)pivot_row;
            size_t iq = (size_t)index * (size_t)dimension +
                        (size_t)pivot_column;
            double old_p = matrix[ip];
            double old_q = matrix[iq];
            double new_p = cosine * old_p - sine * old_q;
            double new_q = sine * old_p + cosine * old_q;
            matrix[ip] = new_p;
            matrix[(size_t)pivot_row * (size_t)dimension +
                   (size_t)index] = new_p;
            matrix[iq] = new_q;
            matrix[(size_t)pivot_column * (size_t)dimension +
                   (size_t)index] = new_q;
        }
        matrix[pp] = diagonal_p - tangent * off_diagonal;
        matrix[qq] = diagonal_q + tangent * off_diagonal;
        matrix[pq] = 0.0;
        matrix[(size_t)pivot_column * (size_t)dimension +
               (size_t)pivot_row] = 0.0;
    }
    for (int index = 0; index < dimension; index++)
        eigenvalues[index] =
            matrix[(size_t)index * (size_t)dimension + (size_t)index];
    fsq_sort_doubles(eigenvalues, dimension);
    free(matrix);
    return converged;
}

static int fsq_expected_match(const FsqDeclaredCase *declared,
                              const FsqSummary *summary)
{
    if (!declared) return 1;
    if (summary->label_count != declared->expected_count) return 0;
    for (int index = 0; index < declared->expected_count; index++)
        if (summary->labels[index] != declared->expected_labels[index])
            return 0;
    return 1;
}

static int fsq_build(int base, int lag, int prime_count, double tau,
                     const FsqDeclaredCase *declared, FsqSummary *summary)
{
    int modulus = 0;
    if (!summary || base < 2 || prime_count < 2 ||
        prime_count > FSQ_MAX_PRIMES || tau <= 0.0 ||
        !collision_table_modulus(base, lag, &modulus))
        return 0;
    *summary = (FsqSummary){0};
    summary->prime_count = prime_count;
    int *primes = malloc((size_t)prime_count * sizeof(*primes));
    int *prime_labels = malloc((size_t)prime_count * sizeof(*prime_labels));
    int *blocks = malloc((size_t)prime_count * sizeof(*blocks));
    if (!primes || !prime_labels || !blocks) {
        free(primes);
        free(prime_labels);
        free(blocks);
        return 0;
    }
    fsq_generate_primes(primes, prime_count);
    for (int residue = 1; residue < modulus; residue++) {
        if (collision_table_gcd(residue, modulus) != 1) continue;
        int value = 0;
        int direct = 0;
        int collision = 0;
        int multiplier = 0;
        summary->unit_table_classes++;
        if (!collision_table_value(base, lag, residue, &value) ||
            !collision_table_direct_deviation(
                modulus + residue, base, lag,
                &collision, &direct, &multiplier) ||
            direct != value)
            summary->unit_table_failures++;
    }

    for (int index = 0; index < prime_count; index++) {
        int direct = 0;
        int table = 0;
        int uses_table = 0;
        if (!all_prime_collision_label_value(
                primes[index], base, lag, &direct, &table, &uses_table)) {
            summary->arithmetic_failures++;
            direct = 0;
        } else if (uses_table) {
            summary->nonbase_prime_checks++;
            if (direct != table) summary->arithmetic_failures++;
        } else {
            summary->base_prime_checks++;
            if (direct != 0) summary->arithmetic_failures++;
        }
        prime_labels[index] = direct;
        summary->labels[index] = direct;
    }
    summary->label_count = fsq_unique_ints(summary->labels, prime_count);
    if (summary->label_count > FSQ_MAX_LABELS) {
        free(primes);
        free(prime_labels);
        free(blocks);
        return 0;
    }
    for (int index = 0; index < prime_count; index++) {
        blocks[index] = fsq_label_index(
            summary->labels, summary->label_count, prime_labels[index]);
        if (blocks[index] < 0) summary->arithmetic_failures++;
        else summary->populations[blocks[index]]++;
    }
    for (int index = 0; index < summary->label_count; index++)
        if (summary->populations[index] == 0) summary->missing_labels++;
    if (!fsq_expected_match(declared, summary))
        summary->arithmetic_failures++;
    summary->arithmetic_failures += summary->unit_table_failures;
    summary->bulk_multiplicity = prime_count - summary->label_count;

    int q = summary->label_count;
    double *degrees = calloc((size_t)q, sizeof(*degrees));
    double *distance = calloc((size_t)q * (size_t)q, sizeof(*distance));
    double *precision = calloc((size_t)q * (size_t)q, sizeof(*precision));
    double *quotient = calloc((size_t)q * (size_t)q, sizeof(*quotient));
    double *quotient_h = calloc((size_t)q * (size_t)q, sizeof(*quotient_h));
    double *full_a = calloc(
        (size_t)prime_count * (size_t)prime_count, sizeof(*full_a));
    double *full_h = calloc(
        (size_t)prime_count * (size_t)prime_count, sizeof(*full_h));
    double *compressed = calloc((size_t)q * (size_t)q, sizeof(*compressed));
    if (!degrees || !distance || !precision || !quotient || !quotient_h ||
        !full_a || !full_h || !compressed) {
        free(primes); free(prime_labels); free(blocks);
        free(degrees); free(distance); free(precision); free(quotient);
        free(quotient_h); free(full_a); free(full_h); free(compressed);
        return 0;
    }
    for (int row = 0; row < q; row++) {
        for (int column = 0; column < q; column++) {
            size_t entry = (size_t)row * (size_t)q + (size_t)column;
            distance[entry] = exp(-fabs((double)(summary->labels[row] -
                                                  summary->labels[column])) /
                                  tau);
            degrees[row] += (double)summary->populations[column] *
                distance[entry];
        }
    }
    for (int row = 0; row < q; row++) {
        for (int column = 0; column < q; column++) {
            size_t entry = (size_t)row * (size_t)q + (size_t)column;
            quotient[entry] =
                sqrt((double)summary->populations[row] *
                     (double)summary->populations[column]) *
                distance[entry] /
                sqrt(degrees[row] * degrees[column]);
            double scale_row = sqrt(
                (double)summary->populations[row] / degrees[row]);
            double scale_column = sqrt(
                (double)summary->populations[column] / degrees[column]);
            double factor_error = fabs(
                quotient[entry] -
                scale_row * distance[entry] * scale_column);
            if (factor_error > summary->maximum_quotient_factor_error)
                summary->maximum_quotient_factor_error = factor_error;
        }
    }
    if (q == 1) {
        precision[0] = 1.0;
    } else {
        precision[0] = 1.0;
        for (int index = 0; index < q - 1; index++) {
            double ratio = distance[(size_t)index * (size_t)q +
                                    (size_t)(index + 1)];
            double denominator = 1.0 - ratio * ratio;
            if (!(ratio > 0.0 && ratio < 1.0) || denominator <= 0.0) {
                summary->inverse_failures++;
                continue;
            }
            precision[(size_t)index * (size_t)q + (size_t)index] +=
                ratio * ratio / denominator;
            precision[(size_t)(index + 1) * (size_t)q +
                      (size_t)(index + 1)] += 1.0 / denominator;
            precision[(size_t)index * (size_t)q +
                      (size_t)(index + 1)] = -ratio / denominator;
            precision[(size_t)(index + 1) * (size_t)q +
                      (size_t)index] = -ratio / denominator;
            if (precision[(size_t)index * (size_t)q +
                          (size_t)(index + 1)] == 0.0)
                summary->inverse_failures++;
        }
    }
    for (int row = 0; row < q; row++) {
        for (int column = 0; column < q; column++) {
            double product = 0.0;
            for (int middle = 0; middle < q; middle++)
                product += precision[(size_t)row * (size_t)q +
                                     (size_t)middle] *
                           distance[(size_t)middle * (size_t)q +
                                    (size_t)column];
            double expected = row == column ? 1.0 : 0.0;
            double error = fabs(product - expected);
            if (error > summary->maximum_inverse_error)
                summary->maximum_inverse_error = error;
        }
    }
    if (summary->maximum_inverse_error > FSQ_CHECK_TOL ||
        summary->maximum_quotient_factor_error > FSQ_CHECK_TOL)
        summary->inverse_failures++;
    for (int row = 0; row < q; row++) {
        double left = 0.0;
        for (int column = 0; column < q; column++)
            left += quotient[(size_t)row * (size_t)q + (size_t)column] *
                sqrt((double)summary->populations[column] * degrees[column]);
        double right = sqrt((double)summary->populations[row] * degrees[row]);
        double error = fabs(left - right);
        if (error > summary->maximum_perron_error)
            summary->maximum_perron_error = error;
    }
    if (summary->maximum_perron_error > FSQ_CHECK_TOL)
        summary->perron_failures++;
    for (int row = 0; row < q; row++) {
        for (int column = 0; column < q; column++) {
            double value = 0.0;
            for (int middle = 0; middle < q; middle++) {
                double left = (row == middle ? 1.0 : 0.0) -
                    quotient[(size_t)row * (size_t)q + (size_t)middle];
                double right = (middle == column ? 1.0 : 0.0) -
                    quotient[(size_t)middle * (size_t)q + (size_t)column];
                value += left * right;
            }
            quotient_h[(size_t)row * (size_t)q + (size_t)column] = value;
        }
    }
    if (!fsq_jacobi(quotient, q, summary->quotient_eigenvalues) ||
        !fsq_jacobi(quotient_h, q, summary->hamiltonian_eigenvalues))
        summary->quotient_failures++;
    double transformed[FSQ_MAX_LABELS];
    for (int index = 0; index < q; index++) {
        double mu = summary->quotient_eigenvalues[index];
        transformed[index] = (1.0 - mu) * (1.0 - mu);
        if (!(mu > 0.0 && mu <= 1.0 + FSQ_CHECK_TOL))
            summary->quotient_failures++;
        if (index > 0 &&
            mu - summary->quotient_eigenvalues[index - 1] <=
                FSQ_CHECK_TOL)
            summary->quotient_failures++;
        double mode = summary->hamiltonian_eigenvalues[index];
        if (!(mode >= -FSQ_CHECK_TOL && mode < 1.0 - FSQ_CHECK_TOL))
            summary->quotient_failures++;
        if (index > 0 &&
            mode - summary->hamiltonian_eigenvalues[index - 1] <=
                FSQ_CHECK_TOL)
            summary->quotient_failures++;
    }
    fsq_sort_doubles(transformed, q);
    for (int index = 0; index < q; index++)
        if (fabs(transformed[index] -
                 summary->hamiltonian_eigenvalues[index]) >
            FSQ_CHECK_TOL)
            summary->quotient_failures++;
    if (fabs(summary->quotient_eigenvalues[q - 1] - 1.0) >
            FSQ_CHECK_TOL ||
        fabs(summary->hamiltonian_eigenvalues[0]) > FSQ_CHECK_TOL)
        summary->quotient_failures++;

    for (int row = 0; row < prime_count; row++) {
        for (int column = 0; column < prime_count; column++) {
            int row_block = blocks[row];
            int column_block = blocks[column];
            full_a[(size_t)row * (size_t)prime_count + (size_t)column] =
                distance[(size_t)row_block * (size_t)q +
                         (size_t)column_block] /
                sqrt(degrees[row_block] * degrees[column_block]);
        }
    }
    for (int row = 0; row < prime_count; row++) {
        for (int column = 0; column < prime_count; column++) {
            double square = 0.0;
            for (int middle = 0; middle < prime_count; middle++)
                square += full_a[(size_t)row * (size_t)prime_count +
                                 (size_t)middle] *
                          full_a[(size_t)middle * (size_t)prime_count +
                                 (size_t)column];
            full_h[(size_t)row * (size_t)prime_count + (size_t)column] =
                (row == column ? 1.0 : 0.0) -
                2.0 * full_a[(size_t)row * (size_t)prime_count +
                             (size_t)column] + square;
        }
    }
    for (int row = 0; row < prime_count; row++) {
        for (int column = 0; column < prime_count; column++) {
            int row_block = blocks[row];
            int column_block = blocks[column];
            compressed[(size_t)row_block * (size_t)q +
                       (size_t)column_block] +=
                full_a[(size_t)row * (size_t)prime_count +
                       (size_t)column] /
                sqrt((double)summary->populations[row_block] *
                     (double)summary->populations[column_block]);
        }
    }
    for (int row = 0; row < q; row++) {
        for (int column = 0; column < q; column++) {
            double error = fabs(
                compressed[(size_t)row * (size_t)q + (size_t)column] -
                quotient[(size_t)row * (size_t)q + (size_t)column]);
            if (error > summary->maximum_compression_error)
                summary->maximum_compression_error = error;
        }
    }
    for (int column = 0; column < q; column++) {
        for (int row = 0; row < prime_count; row++) {
            int row_block = blocks[row];
            double left = 0.0;
            for (int index = 0; index < prime_count; index++)
                if (blocks[index] == column)
                    left += full_h[(size_t)row * (size_t)prime_count +
                                   (size_t)index] /
                            sqrt((double)summary->populations[column]);
            double right = quotient_h[
                (size_t)row_block * (size_t)q + (size_t)column] /
                sqrt((double)summary->populations[row_block]);
            double error = fabs(left - right);
            if (error > summary->maximum_constant_action_error)
                summary->maximum_constant_action_error = error;
        }
    }
    for (int block = 0; block < q; block++) {
        int representative = -1;
        for (int index = 0; index < prime_count; index++) {
            if (blocks[index] != block) continue;
            if (representative < 0) {
                representative = index;
                continue;
            }
            for (int row = 0; row < prime_count; row++) {
                double left = full_h[
                    (size_t)row * (size_t)prime_count + (size_t)index] -
                    full_h[(size_t)row * (size_t)prime_count +
                           (size_t)representative];
                double right = (row == index ? 1.0 : 0.0) -
                               (row == representative ? 1.0 : 0.0);
                double error = fabs(left - right);
                if (error > summary->maximum_bulk_action_error)
                    summary->maximum_bulk_action_error = error;
            }
        }
    }
    if (summary->maximum_compression_error > FSQ_CHECK_TOL ||
        summary->maximum_constant_action_error > FSQ_CHECK_TOL ||
        summary->maximum_bulk_action_error > FSQ_CHECK_TOL)
        summary->full_operator_failures++;
    static const double heat_times[] = {0.0, 0.25, 1.0, 2.0, 5.0};
    for (size_t time_index = 0;
         time_index < sizeof(heat_times) / sizeof(heat_times[0]);
         time_index++) {
        double time = heat_times[time_index];
        double heat = (double)summary->bulk_multiplicity * exp(-time);
        for (int index = 0; index < q; index++)
            heat += exp(-time * summary->hamiltonian_eigenvalues[index]);
        double baseline = 1.0 + (double)(prime_count - 1) * exp(-time);
        double difference = heat - baseline;
        double upper = (double)(q - 1) * (1.0 - exp(-time));
        if (difference < -FSQ_CHECK_TOL ||
            difference > upper + FSQ_CHECK_TOL)
            summary->heat_failures++;
    }

    free(primes); free(prime_labels); free(blocks);
    free(degrees); free(distance); free(precision); free(quotient);
    free(quotient_h); free(full_a); free(full_h); free(compressed);
    return 1;
}

static void fsq_print_labels(const FsqSummary *summary)
{
    printf("  labels = {");
    for (int index = 0; index < summary->label_count; index++)
        printf("%s%d", index == 0 ? "" : ",", summary->labels[index]);
    printf("}\n  populations = {");
    for (int index = 0; index < summary->label_count; index++)
        printf("%s%d:%d", index == 0 ? "" : ",",
               summary->labels[index], summary->populations[index]);
    printf("}\n");
}

static void fsq_print_eigenvalues(const FsqSummary *summary)
{
    printf("  quotient mu = {");
    for (int index = 0; index < summary->label_count; index++)
        printf("%s%.12g", index == 0 ? "" : ",",
               summary->quotient_eigenvalues[index]);
    printf("}\n  quotient H modes = {");
    for (int index = 0; index < summary->label_count; index++)
        printf("%s%.12g", index == 0 ? "" : ",",
               summary->hamiltonian_eigenvalues[index]);
    printf("}\n");
}

static int fsq_summary_passes(const FsqSummary *summary)
{
    return summary->arithmetic_failures == 0 &&
           summary->missing_labels == 0 &&
           summary->quotient_failures == 0 &&
           summary->heat_failures == 0 &&
           summary->full_operator_failures == 0 &&
           summary->inverse_failures == 0 &&
           summary->perron_failures == 0;
}

int finite_spectral_quotient_metrics(
        int base, int lag, int prime_count, double tau,
        int *label_count, int *bulk_multiplicity,
        double *maximum_action_error)
{
    if (!label_count || !bulk_multiplicity || !maximum_action_error)
        return 0;
    FsqSummary summary;
    if (!fsq_build(base, lag, prime_count, tau, NULL, &summary)) return 0;
    *label_count = summary.label_count;
    *bulk_multiplicity = summary.bulk_multiplicity;
    *maximum_action_error = summary.maximum_compression_error;
    if (summary.maximum_constant_action_error > *maximum_action_error)
        *maximum_action_error = summary.maximum_constant_action_error;
    if (summary.maximum_bulk_action_error > *maximum_action_error)
        *maximum_action_error = summary.maximum_bulk_action_error;
    return fsq_summary_passes(&summary);
}

int finite_spectral_quotient_inspect(int base, int lag,
                                     int prime_count, double tau)
{
    FsqSummary summary;
    if (!fsq_build(base, lag, prime_count, tau, NULL, &summary)) {
        fprintf(stderr,
                "require base>=2, lag>=1, 2<=prime-count<=300, tau>0, and modulus<=2000000\n");
        return 1;
    }
    int ok = fsq_summary_passes(&summary);
    printf("Finite spectral quotient\n\n");
    printf("  base=%d lag=%d first-prime-count=%d tau=%.6g\n",
           base, lag, prime_count, tau);
    printf("  observed label states q=%d; exact bulk multiplicity N-q=%d\n",
           summary.label_count, summary.bulk_multiplicity);
    fsq_print_labels(&summary);
    fsq_print_eigenvalues(&summary);
    printf("  all direct prime labels agree with the finite cases  %s\n",
           summary.arithmetic_failures == 0 ? "PASS" : "FAIL");
    printf("  quotient modes are simple, distinct, and in [0,1)   %s\n",
           summary.quotient_failures == 0 ? "PASS" : "FAIL");
    printf("  tridiagonal distance-kernel inverse error %.3e      %s\n",
           summary.maximum_inverse_error,
           summary.inverse_failures == 0 ? "PASS" : "FAIL");
    printf("  normalized Perron eigenvector error %.3e            %s\n",
           summary.maximum_perron_error,
           summary.perron_failures == 0 ? "PASS" : "FAIL");
    printf("  full block compression error %.3e                  %s\n",
           summary.maximum_compression_error,
           summary.full_operator_failures == 0 ? "PASS" : "FAIL");
    printf("  N-q bulk action numerical error %.3e                %s\n",
           summary.maximum_bulk_action_error,
           summary.full_operator_failures == 0 ? "PASS" : "FAIL");
    printf("  heat-trace bounds at five nonnegative times         %s\n",
           summary.heat_failures == 0 ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int fsq_declared_audit(int report)
{
    static const FsqDeclaredCase cases[] = {
        {7, fsq_base_seven_labels, 12},
        {10, fsq_base_ten_labels, 12},
        {12, fsq_base_twelve_labels, 12}
    };
    int failures = 0;
    int unit_classes = 0;
    int prime_checks = 0;
    int base_prime_checks = 0;
    double maximum_error = 0.0;
    for (size_t index = 0; index < sizeof(cases) / sizeof(cases[0]);
         index++) {
        FsqSummary summary;
        if (!fsq_build(cases[index].base, 1, 300, 1.0,
                       &cases[index], &summary)) {
            failures++;
            continue;
        }
        int ok = fsq_summary_passes(&summary) &&
                 summary.label_count == 12 &&
                 summary.missing_labels == 0 &&
                 summary.bulk_multiplicity == 288;
        if (!ok) failures++;
        unit_classes += summary.unit_table_classes;
        prime_checks += summary.nonbase_prime_checks;
        base_prime_checks += summary.base_prime_checks;
        if (summary.maximum_compression_error > maximum_error)
            maximum_error = summary.maximum_compression_error;
        if (summary.maximum_constant_action_error > maximum_error)
            maximum_error = summary.maximum_constant_action_error;
        if (summary.maximum_bulk_action_error > maximum_error)
            maximum_error = summary.maximum_bulk_action_error;
        if (summary.maximum_inverse_error > maximum_error)
            maximum_error = summary.maximum_inverse_error;
        if (summary.maximum_quotient_factor_error > maximum_error)
            maximum_error = summary.maximum_quotient_factor_error;
        if (summary.maximum_perron_error > maximum_error)
            maximum_error = summary.maximum_perron_error;
        if (report) {
            printf("\nbase %d\n", cases[index].base);
            fsq_print_labels(&summary);
            printf("  q=%d; bulk multiplicity=%d; arithmetic=%s; spectrum=%s\n",
                   summary.label_count, summary.bulk_multiplicity,
                   summary.arithmetic_failures == 0 ? "PASS" : "FAIL",
                   summary.quotient_failures == 0 ? "PASS" : "FAIL");
        }
    }
    if (report) {
        printf("\nDeclared quotient-spectrum ledger\n");
        printf("  unit classes=%d; nonbase prime checks=%d; base-prime checks=%d\n",
               unit_classes, prime_checks, base_prime_checks);
        printf("  maximum numerical certificate error %.3e\n", maximum_error);
        printf("  three 300-prime systems with q=12 and bulk=288  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    return failures;
}

int finite_spectral_quotient_declared(void)
{
    printf("Finite spectral quotient\n");
    printf("Declared base-seven, base-ten, and base-twelve systems\n");
    return fsq_declared_audit(1) == 0 ? 0 : 1;
}

int finite_spectral_quotient_verify(void)
{
    int failures = fsq_declared_audit(0);
    int ok = failures == 0;
    printf("Finite spectral-quotient verification\n\n");
    printf("  exact displayed label sets for bases 7, 10, and 12  %s\n",
           ok ? "PASS" : "FAIL");
    printf("  all 130 unit table classes and 900 direct prime labels  %s\n",
           ok ? "PASS" : "FAIL");
    printf("  all labels occur; q=12 and exact bulk multiplicity=288  %s\n",
           ok ? "PASS" : "FAIL");
    printf("  full block action agrees with the quotient numerically  %s\n",
           ok ? "PASS" : "FAIL");
    printf("  tridiagonal distance-kernel inverse and Q=RER identity  %s\n",
           ok ? "PASS" : "FAIL");
    printf("  explicit Perron eigenvector has eigenvalue one          %s\n",
           ok ? "PASS" : "FAIL");
    printf("  simple positive quotient and distinct H modes below one %s\n",
           ok ? "PASS" : "FAIL");
    printf("  heat-trace identity bounds at five times per system     %s\n",
           ok ? "PASS" : "FAIL");
    printf("\n8/8 verification groups %s.\n",
           ok ? "passed" : "did not pass");
    printf("Exact boundary  labels, populations, block dimensions, and N-q are\n");
    printf("integer facts. Exponential kernels and eigenvalues are numerical checks.\n");
    printf("Numerical boundary  tau=1 and tolerance %.1e for the declared systems.\n",
           FSQ_CHECK_TOL);
    printf("Theorem boundary  quotient simplicity and heat bounds are proved separately.\n");
    return ok;
}

void finite_spectral_quotient_help(void)
{
    printf(
        "Finite spectral quotient\n\n"
        "Commands\n"
        "  nfield finite-spectral-quotient inspect <base> [--lag <ell>]\n"
        "      [--prime-count <N>] [--tau <positive-scale>]\n"
        "      Build one prime-label quotient and compare its full block action.\n"
        "  nfield finite-spectral-quotient declared\n"
        "      Reproduce the three 300-prime, twelve-label systems.\n"
        "  nfield finite-spectral-quotient verify\n"
        "  nfield verify finite-spectral-quotient\n\n"
        "Scope\n"
        "  proved             exact q-state quotient, N-q eigenvalue-one bulk,\n"
        "                     simple modes below one, heat trace, and fixed complexity.\n"
        "  exact computation collision labels, block populations, quotient dimension,\n"
        "                     and bulk multiplicity for all declared systems.\n"
        "  numerical check   distance-kernel inverse, Q=RER, Perron vector, full\n"
        "                     block action, Jacobi modes, and heat bounds at tau=1\n"
        "                     with tolerance 5e-10.\n"
    );
}
