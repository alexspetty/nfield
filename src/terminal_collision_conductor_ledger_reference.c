/* Independent fixed-case regression for the terminal conductor ledger. */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int p;
    int n;
    int ok;
    int failure;
    int64_t modulus;
    int64_t formal_boundary;
    int64_t unit_norm;
    int64_t moment;
    int64_t character_count;
    int64_t mean;
} prime_case_result;

static int64_t gcd_i64(int64_t a, int64_t b)
{
    while (b != 0) {
        int64_t r = a % b;
        a = b;
        b = r;
    }
    return a < 0 ? -a : a;
}

static int64_t pow_i64(int64_t base, int exponent)
{
    int64_t value = 1;
    for (int i = 0; i < exponent; ++i) {
        value *= base;
    }
    return value;
}

static int64_t phi_i64(int64_t n)
{
    int64_t result = n;
    int64_t remaining = n;
    for (int64_t p = 2; p * p <= remaining; ++p) {
        if (remaining % p != 0) {
            continue;
        }
        while (remaining % p == 0) {
            remaining /= p;
        }
        result -= result / p;
    }
    if (remaining > 1) {
        result -= result / remaining;
    }
    return result;
}

static int mobius_i64(int64_t n)
{
    int factors = 0;
    int64_t remaining = n;
    for (int64_t p = 2; p * p <= remaining; ++p) {
        if (remaining % p != 0) {
            continue;
        }
        remaining /= p;
        ++factors;
        if (remaining % p == 0) {
            return 0;
        }
        while (remaining % p == 0) {
            remaining /= p;
        }
    }
    if (remaining > 1) {
        ++factors;
    }
    return (factors % 2 == 0) ? 1 : -1;
}

static int64_t *terminal_unit_boundary(int base, int depth, int64_t *modulus_out)
{
    const int64_t modulus = pow_i64(base, depth);
    const int64_t middle_count = pow_i64(base, depth - 2);
    const int64_t leading_place = pow_i64(base, depth - 1);
    int64_t *boundary = calloc((size_t)modulus, sizeof(*boundary));

    if (boundary == NULL) {
        return NULL;
    }

    for (int a = 0; a < base; ++a) {
        for (int64_t y = 0; y < middle_count; ++y) {
            const int64_t left = (int64_t)a * leading_place
                               + (int64_t)base * y + a;
            const int64_t right = (left + 1) % modulus;
            boundary[left] -= 1;
            boundary[right] += 1;
        }
    }

    for (int64_t x = 0; x < modulus; ++x) {
        if (gcd_i64(x, modulus) != 1) {
            boundary[x] = 0;
        }
    }

    *modulus_out = modulus;
    return boundary;
}

static int pushdown_invariants(const int64_t *boundary, int64_t modulus,
                               int64_t divisor, int64_t *diagonal,
                               int64_t *antipodal)
{
    int64_t *pushdown = calloc((size_t)divisor, sizeof(*pushdown));
    if (pushdown == NULL) {
        return 0;
    }

    for (int64_t x = 0; x < modulus; ++x) {
        if (gcd_i64(x, modulus) == 1) {
            pushdown[x % divisor] += boundary[x];
        }
    }

    int64_t d_value = 0;
    int64_t a_value = 0;
    for (int64_t r = 0; r < divisor; ++r) {
        if (gcd_i64(r, divisor) != 1) {
            continue;
        }
        const int64_t opposite = (divisor - r) % divisor;
        d_value += pushdown[r] * pushdown[r];
        a_value += pushdown[r] * pushdown[opposite];
    }

    free(pushdown);
    *diagonal = d_value;
    *antipodal = a_value;
    return 1;
}

static int64_t pushdown_value(const int64_t *boundary, int64_t modulus,
                              int64_t divisor, int64_t residue)
{
    int64_t value = 0;
    for (int64_t x = 0; x < modulus; ++x) {
        if (gcd_i64(x, modulus) == 1 && x % divisor == residue) {
            value += boundary[x];
        }
    }
    return value;
}

static int conductor_ledger_moment(const int64_t *boundary, int64_t modulus,
                                   int64_t *moment_out)
{
    int64_t twice_moment = 0;
    for (int64_t d = 1; d <= modulus; ++d) {
        if (modulus % d != 0) {
            continue;
        }
        const int coefficient = mobius_i64(modulus / d);
        if (coefficient == 0) {
            continue;
        }
        int64_t diagonal = 0;
        int64_t antipodal = 0;
        if (!pushdown_invariants(boundary, modulus, d,
                                 &diagonal, &antipodal)) {
            return 0;
        }
        twice_moment += (int64_t)coefficient * phi_i64(d)
                      * (diagonal - antipodal);
    }
    if (twice_moment % 2 != 0) {
        return 0;
    }
    *moment_out = twice_moment / 2;
    return 1;
}

static int primitive_odd_character_count(int64_t modulus, int64_t *count_out)
{
    int64_t twice_count = 0;
    for (int64_t d = 1; d <= modulus; ++d) {
        if (modulus % d != 0) {
            continue;
        }
        const int coefficient = mobius_i64(modulus / d);
        const int fixed_by_negation = (2 % d == 0);
        twice_count += (int64_t)coefficient * phi_i64(d)
                     * (1 - fixed_by_negation);
    }
    if (twice_count < 0 || twice_count % 2 != 0) {
        return 0;
    }
    *count_out = twice_count / 2;
    return 1;
}

static prime_case_result check_prime_case(int p, int n)
{
    prime_case_result result = {0};
    result.p = p;
    result.n = n;
    result.ok = 0;

    int64_t modulus = 0;
    int64_t *boundary = terminal_unit_boundary(p, n, &modulus);
    if (boundary == NULL) {
        result.failure = 1;
        return result;
    }

    result.modulus = modulus;
    result.formal_boundary = 2 * pow_i64(p, n - 1);
    for (int64_t x = 0; x < modulus; ++x) {
        result.unit_norm += boundary[x] * boundary[x];
    }
    const int64_t expected_norm = 2 * pow_i64(p, n - 2) * (p - 1);
    if (result.unit_norm != expected_norm) {
        result.failure = 2;
        free(boundary);
        return result;
    }

    const int64_t lower = pow_i64(p, n - 1);
    for (int64_t r = 0; r < lower; ++r) {
        if (gcd_i64(r, lower) != 1) {
            continue;
        }
        int64_t balance = 0;
        for (int64_t x = r; x < modulus; x += lower) {
            balance += boundary[x];
        }
        if (balance != 0) {
            result.failure = 3;
            free(boundary);
            return result;
        }
    }

    for (int64_t x = 0; x < modulus; ++x) {
        if (gcd_i64(x, modulus) != 1) {
            continue;
        }
        const int64_t opposite = (modulus - x) % modulus;
        if (boundary[opposite] != -boundary[x]) {
            result.failure = 4;
            free(boundary);
            return result;
        }
    }

    if (!conductor_ledger_moment(boundary, modulus, &result.moment)) {
        result.failure = 5;
        free(boundary);
        return result;
    }
    if (result.moment != phi_i64(modulus) * result.unit_norm) {
        result.failure = 6;
        free(boundary);
        return result;
    }

    if (!primitive_odd_character_count(modulus, &result.character_count)
        || result.character_count
           != (phi_i64(modulus) - phi_i64(lower)) / 2) {
        result.failure = 7;
        free(boundary);
        return result;
    }
    if (result.character_count <= 0
        || result.moment % result.character_count != 0) {
        result.failure = 8;
        free(boundary);
        return result;
    }
    result.mean = result.moment / result.character_count;
    if (result.mean != 2 * result.formal_boundary) {
        result.failure = 9;
        free(boundary);
        return result;
    }

    result.ok = 1;
    free(boundary);
    return result;
}

static int check_base_fifteen(void)
{
    int64_t modulus = 0;
    int64_t *boundary = terminal_unit_boundary(15, 2, &modulus);
    if (boundary == NULL || modulus != 225) {
        free(boundary);
        return 0;
    }

    const int64_t divisors[] = {15, 45, 75, 225};
    const int64_t expected_difference[] = {0, 32, 32, 32};
    for (size_t i = 0; i < sizeof(divisors) / sizeof(divisors[0]); ++i) {
        int64_t diagonal = 0;
        int64_t antipodal = 0;
        if (!pushdown_invariants(boundary, modulus, divisors[i],
                                 &diagonal, &antipodal)
            || diagonal - antipodal != expected_difference[i]) {
            free(boundary);
            return 0;
        }
    }

    int64_t moment = 0;
    int64_t character_count = 0;
    const int ok = pushdown_value(boundary, modulus, 9, 4) == 1
                && pushdown_value(boundary, modulus, 45, 1) == 1
                && pushdown_value(boundary, modulus, 75, 1) == 1
                && conductor_ledger_moment(boundary, modulus, &moment)
                && primitive_odd_character_count(modulus, &character_count)
                && moment == 896
                && character_count == 32
                && moment % character_count == 0
                && moment / character_count == 28;

    free(boundary);
    return ok;
}

int nfield_terminal_collision_conductor_ledger_run(int report)
{
    const int primes[] = {3, 5, 7, 11};
    prime_case_result results[8];

#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (int index = 0; index < 8; ++index) {
        const int prime_index = index / 2;
        const int depth = 2 + index % 2;
        results[index] = check_prime_case(primes[prime_index], depth);
    }

    for (int index = 0; index < 8; ++index) {
        const prime_case_result *result = &results[index];
        if (!result->ok) {
            fprintf(stderr, "FAIL p=%d N=%d check=%d\n",
                    result->p, result->n, result->failure);
            return 1;
        }
        if (report) {
            printf("PASS p=%d N=%d m=%" PRId64
                   " formal=%" PRId64 " U=%" PRId64
                   " moment=%" PRId64 " characters=%" PRId64
                   " mean=%" PRId64 "\n",
                   result->p, result->n, result->modulus,
                   result->formal_boundary, result->unit_norm,
                   result->moment, result->character_count, result->mean);
        }
    }

    if (!check_base_fifteen()) {
        fputs("FAIL base=15 N=2 conductor ledger\n", stderr);
        return 1;
    }
    if (report) {
        puts("PASS base=15 N=2 m=225 conductors=(15,45,75,225) "
             "differences=(0,32,32,32) moment=896 characters=32 mean=28");
    }
    return 0;
}

#ifndef NFIELD_CLI_EMBEDDED
int main(void)
{
    return nfield_terminal_collision_conductor_ledger_run(1);
}
#endif
