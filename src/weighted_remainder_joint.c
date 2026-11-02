/* Exact finite-list CRT and empirical/cutoff moments for collision resets. */
#include "weighted_remainder_joint.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned joint_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned r = a % b; a = b; b = r; }
    return a;
}

static int valid_shifts(unsigned dimension, const unsigned *shifts, unsigned maximum)
{
    if (dimension > WEIGHTED_REMAINDER_JOINT_MAX || (dimension && !shifts)) return 0;
    for (unsigned i = 0; i < dimension; ++i) if (shifts[i] > maximum) return 0;
    return 1;
}

int weighted_remainder_joint_crt_q(mpq_t probability, mpz_t residue, mpz_t period,
                                    unsigned dimension, const unsigned *periods,
                                    const unsigned *shifts)
{
    if (!valid_shifts(dimension, shifts, WEIGHTED_REMAINDER_EXACT_MAX) ||
        (dimension && !periods) || residue == period ||
        residue == mpq_numref(probability) || residue == mpq_denref(probability) ||
        period == mpq_numref(probability) || period == mpq_denref(probability)) return 0;
    for (unsigned i = 0; i < dimension; ++i)
        if (periods[i] < 2 || periods[i] > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    int compatible = 1;
    mpz_t full, current, address, divisor, quotient, modulus, inverse, step;
    mpz_inits(full, current, address, divisor, quotient, modulus, inverse, step, NULL);
    mpz_set_ui(full, 1);
    mpz_set_ui(current, 1);
    for (unsigned i = 0; i < dimension; ++i) {
        mpz_lcm_ui(full, full, periods[i]);
        for (unsigned j = 0; j < i; ++j) {
            unsigned g = joint_gcd(periods[i], periods[j]);
            if (shifts[i] % g != shifts[j] % g) compatible = 0;
        }
    }
    if (compatible) for (unsigned i = 0; i < dimension; ++i) {
        unsigned k = periods[i];
        unsigned g = (unsigned)mpz_gcd_ui(divisor, current, k);
        unsigned m = k / g;
        if (m == 1) continue;
        unsigned target = (k - shifts[i] % k) % k;
        long difference = (long)target - (long)mpz_fdiv_ui(address, k);
        mpz_divexact_ui(quotient, current, g);
        mpz_set_ui(modulus, m);
        /* current/g and k/g are coprime by construction. */
        if (!mpz_invert(inverse, quotient, modulus)) {
            mpz_clears(full, current, address, divisor, quotient, modulus, inverse, step, NULL);
            return 0;
        }
        mpz_set_si(step, difference / (long)g);
        mpz_mul(step, step, inverse);
        mpz_mod(step, step, modulus);
        mpz_addmul(address, current, step);
        mpz_mul_ui(current, current, m);
    }
    mpq_t result;
    mpq_init(result);
    if (compatible) {
        mpq_set_ui(result, 1, 1);
        mpz_set(mpq_denref(result), full);
    }
    mpq_set(probability, result);
    mpz_set(residue, address);
    mpz_set(period, full);
    mpq_clear(result);
    mpz_clears(full, current, address, divisor, quotient, modulus, inverse, step, NULL);
    return 1;
}

int weighted_remainder_forcing_q(mpq_t out, unsigned n)
{
    if (!n || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t sum, term, factor;
    mpq_inits(sum, term, factor, NULL);
    for (unsigned k = 2; k <= n; ++k) if (n % k == 0) {
        weighted_remainder_weight_q(term, k);
        mpq_set_ui(factor, k, 1);
        mpq_mul(term, term, factor);
        mpq_add(sum, sum, term);
    }
    mpq_set(out, sum);
    mpq_clears(sum, term, factor, NULL);
    return 1;
}

int weighted_remainder_empirical_moment_q(mpq_t out, unsigned length, unsigned kind,
                                         unsigned dimension, const unsigned *shifts,
                                         const unsigned *powers)
{
    if (!length || length > WEIGHTED_REMAINDER_EXACT_MAX || kind > 1 ||
        !valid_shifts(dimension, shifts, WEIGHTED_REMAINDER_EXACT_MAX-length) ||
        (dimension && !powers)) return 0;
    unsigned degree = 0;
    for (unsigned i = 0; i < dimension; ++i) {
        if (powers[i] > WEIGHTED_REMAINDER_MOMENT_DEGREE_MAX-degree) return 0;
        degree += powers[i];
    }
    mpq_t sum, product, value, factor;
    mpq_inits(sum, product, value, factor, NULL);
    for (unsigned n = 1; n <= length; ++n) {
        mpq_set_ui(product, 1, 1);
        for (unsigned i = 0; i < dimension; ++i) {
            if (kind) weighted_remainder_reset_q(value, n+shifts[i]);
            else weighted_remainder_forcing_q(value, n+shifts[i]);
            mpz_pow_ui(mpq_numref(value), mpq_numref(value), powers[i]);
            mpz_pow_ui(mpq_denref(value), mpq_denref(value), powers[i]);
            mpq_mul(product, product, value);
        }
        mpq_add(sum, sum, product);
    }
    mpq_set_ui(factor, length, 1);
    mpq_div(out, sum, factor);
    mpq_clears(sum, product, value, factor, NULL);
    return 1;
}

typedef struct {
    unsigned dimension, cutoff;
    const unsigned *shifts;
    unsigned periods[WEIGHTED_REMAINDER_JOINT_MAX];
    mpq_t coefficients[WEIGHTED_REMAINDER_EXACT_MAX+1];
    mpq_t total;
} JointMoment;

static int joint_moment_terms(JointMoment *job, unsigned index, const mpq_t product)
{
    mpq_t value;
    mpq_init(value);
    if (index == job->dimension) {
        mpz_t residue, period;
        mpz_inits(residue, period, NULL);
        int ok = weighted_remainder_joint_crt_q(value, residue, period,
            job->dimension, job->periods, job->shifts);
        if (ok) {
            mpq_mul(value, value, product);
            mpq_add(job->total, job->total, value);
        }
        mpz_clears(residue, period, NULL);
        mpq_clear(value);
        return ok;
    }
    for (unsigned k = 2; k <= job->cutoff; ++k) {
        job->periods[index] = k;
        mpq_mul(value, product, job->coefficients[k]);
        if (!joint_moment_terms(job, index+1, value)) { mpq_clear(value); return 0; }
    }
    mpq_clear(value);
    return 1;
}

int weighted_remainder_cutoff_joint_moment_q(mpq_t out, unsigned cutoff,
                                            unsigned dimension, const unsigned *shifts)
{
    if (cutoff < 2 || cutoff > WEIGHTED_REMAINDER_EXACT_MAX ||
        !valid_shifts(dimension, shifts, WEIGHTED_REMAINDER_EXACT_MAX)) return 0;
    unsigned tuples = 1;
    for (unsigned i = 0; i < dimension; ++i) {
        if (tuples > WEIGHTED_REMAINDER_JOINT_TUPLE_MAX/(cutoff-1)) return 0;
        tuples *= cutoff-1;
    }
    JointMoment job = {.dimension=dimension, .cutoff=cutoff, .shifts=shifts};
    mpq_t product, factor;
    mpq_inits(job.total, product, factor, NULL);
    mpq_set_ui(product, 1, 1);
    for (unsigned k = 2; k <= cutoff; ++k) {
        mpq_init(job.coefficients[k]);
        weighted_remainder_weight_q(job.coefficients[k], k);
        mpq_set_ui(factor, k, 1);
        mpq_mul(job.coefficients[k], job.coefficients[k], factor);
    }
    int ok = joint_moment_terms(&job, 0, product);
    if (ok) mpq_set(out, job.total);
    for (unsigned k = 2; k <= cutoff; ++k) mpq_clear(job.coefficients[k]);
    mpq_clears(job.total, product, factor, NULL);
    return ok;
}

int weighted_remainder_block_q(mpq_t out, unsigned start, unsigned length)
{
    if (length > WEIGHTED_REMAINDER_EXACT_MAX ||
        start > WEIGHTED_REMAINDER_EXACT_MAX-length) return 0;
    mpq_t total, value;
    mpq_inits(total, value, NULL);
    for (unsigned j = 1; j <= length; ++j) {
        weighted_remainder_reset_q(value, start+j);
        mpq_add(total, total, value);
    }
    mpq_set(out, total);
    mpq_clears(total, value, NULL);
    return 1;
}

static int parse_joint_uint(const char *text, unsigned *out)
{
    if (!text || !*text) return 0;
    for (const char *p = text; *p; ++p) if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    unsigned long value = strtoul(text, &end, 10);
    if (errno || *end || value > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    *out = (unsigned)value;
    return 1;
}

static int parse_joint_pair(const char *text, unsigned *first, unsigned *second)
{
    const char *colon = strchr(text, ':');
    if (!colon || colon == text || colon-text >= 16) return 0;
    char left[16];
    memcpy(left, text, (size_t)(colon-text));
    left[colon-text] = '\0';
    return parse_joint_uint(left, first) && parse_joint_uint(colon+1, second);
}

int weighted_remainder_joint_command(int argc, char **argv)
{
    unsigned first = 0, second = 0, dimension = 0;
    unsigned left[WEIGHTED_REMAINDER_JOINT_MAX], right[WEIGHTED_REMAINDER_JOINT_MAX];
    int ok = 0;
    mpq_t value;
    mpq_init(value);
    if (argc >= 3 && strcmp(argv[2], "crt") == 0 && argc <= 3+WEIGHTED_REMAINDER_JOINT_MAX) {
        dimension = (unsigned)(argc-3);
        ok = 1;
        for (unsigned i = 0; i < dimension; ++i)
            if (!parse_joint_pair(argv[3+i], &left[i], &right[i])) ok = 0;
        mpz_t residue, period;
        mpz_inits(residue, period, NULL);
        if (ok) ok = weighted_remainder_joint_crt_q(value, residue, period, dimension, left, right);
        if (ok) gmp_printf("dimension=%u\ncompatible=%d\nperiod=%Zd\nresidue=%Zd\nhaar_probability=%Qd\n",
                           dimension, mpq_sgn(value) != 0, period, residue, value);
        mpz_clears(residue, period, NULL);
    } else if (argc >= 5 && strcmp(argv[2], "moment") == 0 &&
               argc <= 5+WEIGHTED_REMAINDER_JOINT_MAX && parse_joint_uint(argv[3], &first) &&
               (strcmp(argv[4], "f") == 0 || strcmp(argv[4], "g") == 0)) {
        dimension = (unsigned)(argc-5);
        ok = 1;
        for (unsigned i = 0; i < dimension; ++i)
            if (!parse_joint_pair(argv[5+i], &left[i], &right[i])) ok = 0;
        if (ok) ok = weighted_remainder_empirical_moment_q(value, first, strcmp(argv[4], "g") == 0,
                                                          dimension, left, right);
        if (ok) gmp_printf("length=%u\nkind=%s\ndimension=%u\nfinite_moment=%Qd\n", first, argv[4], dimension, value);
    } else if (argc >= 4 && strcmp(argv[2], "haar-moment") == 0 &&
               argc <= 4+WEIGHTED_REMAINDER_JOINT_MAX && parse_joint_uint(argv[3], &first)) {
        dimension = (unsigned)(argc-4);
        ok = 1;
        for (unsigned i = 0; i < dimension; ++i) if (!parse_joint_uint(argv[4+i], &left[i])) ok = 0;
        if (ok) ok = weighted_remainder_cutoff_joint_moment_q(value, first, dimension, left);
        if (ok) gmp_printf("cutoff=%u\ndimension=%u\nfinite_haar_reset_moment=%Qd\n", first, dimension, value);
    } else if (argc == 5 && strcmp(argv[2], "block") == 0 && parse_joint_uint(argv[3], &first) &&
               parse_joint_uint(argv[4], &second)) {
        ok = weighted_remainder_block_q(value, first, second);
        if (ok) gmp_printf("start=%u\nlength=%u\ndeficit_difference=%Qd\n", first, second, value);
    } else if (argc == 4 && strcmp(argv[2], "forcing") == 0 && parse_joint_uint(argv[3], &first)) {
        ok = weighted_remainder_forcing_q(value, first);
        if (ok) gmp_printf("resolution=%u\nfull_reset_forcing=%Qd\n", first, value);
    }
    if (!ok) fprintf(stderr, "Invalid joint query or resource bound exceeded; see weighted-remainder-state help.\n");
    mpq_clear(value);
    return ok ? 0 : 1;
}
