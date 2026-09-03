/* Exact nonpositive centered weights on reflected prime pairs modulo b^2.
 * Command: reflected-prime-pair-sign.
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "finite_character_core.h"
#include "nfield.h"

enum {
    REFLECTED_PAIR_MAX_EVEN = 100000,
    REFLECTED_PAIR_BASE_COUNT = 6
};

static const int reflected_pair_bases[REFLECTED_PAIR_BASE_COUNT] = {
    3, 5, 7, 10, 11, 13
};

static const int reflected_pair_fixtures[REFLECTED_PAIR_BASE_COUNT][3] = {
    {5555,8452088,8452088}, {2000,2535490,2535490},
    {1020,1207848,1207848}, {1000,1268016,1268016},
    {413,460482,460482}, {295,323970,323970}
};

typedef struct {
    int targets;
    int ordered_pairs;
    int nonzero_terms;
    int positive_terms;
    int identity_failures;
} ReflectedPrimePairAudit;

static unsigned char *prime_flags(int limit, int **primes_out,
                                  int *prime_count_out)
{
    unsigned char *is_prime = calloc((size_t)limit + 1, 1);
    int *primes;
    int count = 0;

    if (!is_prime) return NULL;
    if (limit >= 2) memset(is_prime + 2, 1, (size_t)limit - 1);
    for (int prime = 2; prime <= limit / prime; prime++) {
        if (!is_prime[prime]) continue;
        for (int64_t multiple = (int64_t)prime * prime;
             multiple <= limit; multiple += prime)
            is_prime[multiple] = 0;
    }
    for (int value = 2; value <= limit; value++)
        if (is_prime[value]) count++;
    primes = malloc((size_t)count * sizeof(*primes));
    if (!primes) {
        free(is_prime);
        return NULL;
    }
    count = 0;
    for (int value = 2; value <= limit; value++)
        if (is_prime[value]) primes[count++] = value;
    *primes_out = primes;
    *prime_count_out = count;
    return is_prime;
}

static int reflected_pair_audit(const CollisionCenteredTable *table,
                                int maximum_even,
                                const int *primes,
                                int prime_count,
                                const unsigned char *is_prime,
                                ReflectedPrimePairAudit *audit)
{
    if (!table || !primes || !is_prime || !audit) return 1;
    memset(audit, 0, sizeof(*audit));

    for (int target = 4; target <= maximum_even; target += 2) {
        int64_t weighted_sum = 0;
        int64_t negative_square_sum = 0;
        if (target % table->modulus != 0) continue;
        audit->targets++;
        for (int index = 0; index < prime_count; index++) {
            int left_prime = primes[index];
            int right_prime;
            int64_t left, right, term;
            if (left_prime > target - 2) break;
            right_prime = target - left_prime;
            if (!is_prime[right_prime]) continue;
            audit->ordered_pairs++;
            left = table->centered_numerator[
                left_prime % table->modulus];
            right = table->centered_numerator[
                right_prime % table->modulus];
            term = left * right;
            weighted_sum += term;
            negative_square_sum -= left * left;
            if (term != 0) audit->nonzero_terms++;
            if (term > 0) audit->positive_terms++;
        }
        if (weighted_sum != negative_square_sum || weighted_sum > 0)
            audit->identity_failures++;
    }
    return audit->positive_terms == 0 && audit->identity_failures == 0
               ? 0 : 1;
}

int reflected_prime_pair_sign_sweep(int base, int maximum_even)
{
    CollisionCenteredTable table = {0};
    ReflectedPrimePairAudit audit;
    unsigned char *is_prime;
    int *primes = NULL;
    int prime_count = 0;
    int failures;

    if (base < 2 || base > 64) {
        fprintf(stderr, "base must be between 2 and 64\n");
        return 1;
    }
    if (maximum_even < 4 || maximum_even > REFLECTED_PAIR_MAX_EVEN ||
        maximum_even % 2 != 0) {
        fprintf(stderr, "max-even must be even and between 4 and %d\n",
                REFLECTED_PAIR_MAX_EVEN);
        return 1;
    }
    if (!collision_centered_table_build(base, 1, &table)) return 1;
    is_prime = prime_flags(maximum_even, &primes, &prime_count);
    if (!is_prime) {
        collision_centered_table_free(&table);
        fprintf(stderr, "unable to allocate the prime sieve\n");
        return 1;
    }
    failures = centered_collision_table_audit(&table, NULL, NULL);
    failures += reflected_pair_audit(
        &table, maximum_even, primes, prime_count, is_prime, &audit);

    printf("Reflected prime-pair sign\n");
    printf("Exact centered weights at base %d\n\n", base);
    printf("  even targets N <= %d with N divisible by %d\n",
           maximum_even, table.modulus);
    printf("  targets=%d\n", audit.targets);
    printf("  ordered prime pairs=%d\n", audit.ordered_pairs);
    printf("  nonzero weighted terms=%d\n", audit.nonzero_terms);
    printf("  positive weighted terms=%d  %s\n",
           audit.positive_terms,
           audit.positive_terms == 0 ? "PASS" : "FAIL");
    printf("  sum identity failures=%d  %s\n",
           audit.identity_failures,
           audit.identity_failures == 0 ? "PASS" : "FAIL");
    printf("\nEach checked term uses f(p)f(N-p)=-f(p)^2 when N=0 mod b^2.\n");
    printf("Primes below the modulus are included through the periodic zero-extended\n");
    printf("table; no initial prime segment is silently discarded.\n");
    printf("Classification  exact finite integer arithmetic.\n");
    printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");

    free(primes);
    free(is_prime);
    collision_centered_table_free(&table);
    return failures == 0 ? 0 : 1;
}

int reflected_prime_pair_sign_verify(void)
{
    unsigned char *is_prime;
    int *primes = NULL;
    int prime_count = 0;
    int table_failures = 0;
    int identity_failures = 0;
    int fixture_failures = 0;
    int positive_terms = 0;

    printf("Reflected prime-pair sign verification\n\n");
    is_prime = prime_flags(
        REFLECTED_PAIR_MAX_EVEN, &primes, &prime_count);
    if (!is_prime) {
        printf("unable to allocate the prime sieve\n");
        return 0;
    }
    for (int base_index = 0; base_index < REFLECTED_PAIR_BASE_COUNT;
         base_index++) {
        CollisionCenteredTable table = {0};
        ReflectedPrimePairAudit audit;
        if (!collision_centered_table_build(
                reflected_pair_bases[base_index], 1, &table)) {
            table_failures++;
            continue;
        }
        table_failures += centered_collision_table_audit(
            &table, NULL, NULL);
        identity_failures += reflected_pair_audit(
            &table, REFLECTED_PAIR_MAX_EVEN, primes, prime_count,
            is_prime, &audit);
        positive_terms += audit.positive_terms;
        if (audit.targets != reflected_pair_fixtures[base_index][0] ||
            audit.ordered_pairs != reflected_pair_fixtures[base_index][1] ||
            audit.nonzero_terms != reflected_pair_fixtures[base_index][2])
            fixture_failures++;
        collision_centered_table_free(&table);
    }
    free(primes);
    free(is_prime);

    printf("  six exact centered-table gates                       %s\n",
           table_failures == 0 ? "PASS" : "FAIL");
    printf("  every target sum equals the negative square sum     %s\n",
           identity_failures == 0 ? "PASS" : "FAIL");
    printf("  all declared target, pair, and nonzero-term counts  %s\n",
           fixture_failures == 0 ? "PASS" : "FAIL");
    printf("  positive weighted terms across every sweep = %d      %s\n",
           positive_terms, positive_terms == 0 ? "PASS" : "FAIL");
    printf("\n4/4 verification groups %s.\n",
           table_failures + identity_failures + fixture_failures +
           positive_terms == 0 ? "passed" : "did not pass");
    printf("Proved  the sign identity is an exact corollary of centered reflection.\n");
    printf("Finite boundary  the verifier exhausts even targets through 100000\n");
    printf("for bases 3, 5, 7, 10, 11, and 13.\n");
    return table_failures + identity_failures + fixture_failures +
           positive_terms == 0;
}

void reflected_prime_pair_sign_help(void)
{
    printf(
        "Reflected prime-pair sign\n\n"
        "Commands\n"
        "  nfield reflected-prime-pair-sign sweep <base> [--max-even <N>]\n"
        "      Exhaust even targets divisible by b^2 and every ordered prime\n"
        "      pair. The maximum supported finite boundary is 100000.\n"
        "  nfield reflected-prime-pair-sign verify\n"
        "  nfield verify reflected-prime-pair-sign\n\n"
        "Scope\n"
        "  proved             each weighted term is nonpositive and each target\n"
        "                     sum is a negative square sum.\n"
        "  exact computation integer centered numerators over a finite sweep.\n"
        "  domain detail      primes below b^2 remain in the periodic table;\n"
        "                     nonunits contribute zero rather than being removed.\n"
    );
}
