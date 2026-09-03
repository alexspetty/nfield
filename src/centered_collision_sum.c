/*
 * centered_collision_sum.c
 *
 * Exact finite tools for all-lag collision centering.
 * Centering uses the fixed reduction-fiber means of the finite table, never
 * an empirical mean from the sampled primes.
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "nfield.h"

#define CCSUM_MAX_BASE 128
#define CCSUM_MAX_CUTOFF 10000000
#define CCSUM_MAX_MODULUS 50000

typedef struct {
    int base;
    int lag;
    int modulus;
    int fiber_size;
    int phi;
    int *value;
    long long *fiber_sum;
    int *fiber_count;
} CCSumTable;

typedef struct {
    int count;
    int largest;
    long double sum;
} CCSumTarget;

static const CCSumTarget ccsum_targets[] = {
    {1000, 8167, 0.081643172557029L},
    {10000, 105019, 0.077004671817013L},
    {100000, 1300051, 0.077300690641661L},
    {664554, 9999991, 0.077215574752856L}
};

static long long ccsum_gcd_ll(long long a, long long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        long long next = a % b;
        a = b;
        b = next;
    }
    return a;
}

static void ccsum_reduce(long long *numerator, long long *denominator)
{
    long long divisor = ccsum_gcd_ll(*numerator, *denominator);
    if (divisor > 1) {
        *numerator /= divisor;
        *denominator /= divisor;
    }
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
}

static int ccsum_validate(int base, int lag, int report)
{
    int modulus = 0;
    if (base < 2 || base > CCSUM_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n", CCSUM_MAX_BASE);
        return 0;
    }
    if (lag < 1 || lag > 16) {
        if (report) fprintf(stderr, "lag must be between 1 and 16\n");
        return 0;
    }
    if (!collision_table_modulus(base, lag, &modulus) ||
        modulus > CCSUM_MAX_MODULUS) {
        if (report)
            fprintf(stderr,
                    "base^(lag+1) exceeds the finite-table limit of %d\n",
                    CCSUM_MAX_MODULUS);
        return 0;
    }
    return 1;
}

static int ccsum_build(int base, int lag, CCSumTable *table)
{
    int modulus = 0;
    if (!table || !ccsum_validate(base, lag, 0) ||
        !collision_table_modulus(base, lag, &modulus))
        return 0;
    *table = (CCSumTable){0};
    table->base = base;
    table->lag = lag;
    table->modulus = modulus;
    table->fiber_size = modulus / base;
    table->value = calloc((size_t)modulus, sizeof(*table->value));
    table->fiber_sum = calloc((size_t)base, sizeof(*table->fiber_sum));
    table->fiber_count = calloc((size_t)base, sizeof(*table->fiber_count));
    if (!table->value || !table->fiber_sum || !table->fiber_count) {
        free(table->value);
        free(table->fiber_sum);
        free(table->fiber_count);
        *table = (CCSumTable){0};
        return 0;
    }
    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1) continue;
        if (!collision_table_value(base, lag, a, &table->value[a])) {
            free(table->value);
            free(table->fiber_sum);
            free(table->fiber_count);
            *table = (CCSumTable){0};
            return 0;
        }
        int unit = a % base;
        table->fiber_sum[unit] += table->value[a];
        table->fiber_count[unit]++;
        table->phi++;
    }
    return 1;
}

static void ccsum_free(CCSumTable *table)
{
    if (!table) return;
    free(table->value);
    free(table->fiber_sum);
    free(table->fiber_count);
    *table = (CCSumTable){0};
}

static int ccsum_centered_from_table(const CCSumTable *table, int residue,
                                     long long *numerator,
                                     long long *denominator)
{
    if (!table || !numerator || !denominator || residue <= 0 ||
        residue >= table->modulus ||
        collision_table_gcd(residue, table->modulus) != 1)
        return 0;
    int unit = residue % table->base;
    long long num = (long long)table->fiber_size * table->value[residue] -
                    table->fiber_sum[unit];
    long long den = table->fiber_size;
    ccsum_reduce(&num, &den);
    *numerator = num;
    *denominator = den;
    return 1;
}

int centered_collision_fraction(int base, int lag, int residue,
                                long long *numerator,
                                long long *denominator,
                                int *table_value)
{
    if (!numerator || !denominator || !table_value) return 0;
    CCSumTable table;
    if (!ccsum_build(base, lag, &table)) return 0;
    int ok = ccsum_centered_from_table(
        &table, residue, numerator, denominator);
    if (ok) *table_value = table.value[residue];
    ccsum_free(&table);
    return ok;
}

int centered_collision_inspect(int n, int base, int lag)
{
    if (!ccsum_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (n <= modulus) {
        fprintf(stderr, "inspection requires n > base^(lag+1) = %d\n", modulus);
        return 1;
    }
    if (n > CCSUM_MAX_CUTOFF) {
        fprintf(stderr, "n must not exceed %d for direct inspection\n",
                CCSUM_MAX_CUTOFF);
        return 1;
    }
    if (collision_table_gcd(n, base) != 1) {
        fprintf(stderr, "n must be coprime to the base\n");
        return 1;
    }
    CCSumTable table;
    if (!ccsum_build(base, lag, &table)) return 1;
    int collision = 0, deviation = 0, multiplier = 0;
    int residue = n % modulus;
    long long centered_num = 0, centered_den = 0;
    int ok = collision_table_direct_deviation(
                 n, base, lag, &collision, &deviation, &multiplier) &&
             ccsum_centered_from_table(
                 &table, residue, &centered_num, &centered_den);
    int unit = residue % base;
    long long mean_num = table.fiber_sum[unit];
    long long mean_den = table.fiber_size;
    ccsum_reduce(&mean_num, &mean_den);
    int table_ok = ok && deviation == table.value[residue];

    printf("Finite collision centering at one input\n\n");
    printf("n = %d; base b = %d; lag ell = %d\n", n, base, lag);
    printf("table modulus q = b^(ell+1) = %d; n mod q = %d\n",
           modulus, residue);
    printf("multiplier [b^ell]_n = %d\n", multiplier);
    printf("direct collision count C_b,ell(n) = %d\n", collision);
    printf("direct integer deviation S_b,ell(n) = %+d\n", deviation);
    printf("finite table T_b,ell(n mod q) = %+d  %s\n",
           table.value[residue], table_ok ? "PASS" : "FAIL");
    printf("reduction fiber u = %d; exact mean mu_b,ell(u) = %lld/%lld\n",
           unit, mean_num, mean_den);
    printf("centered value T^circ = %lld/%lld = %+.12Lf\n",
           centered_num, centered_den,
           (long double)centered_num / centered_den);
    printf("The input may be prime or composite; only n>q and gcd(n,b)=1 are used.\n");
    printf("Result  %s\n", table_ok ? "PASS" : "FAIL");
    ccsum_free(&table);
    return table_ok ? 0 : 1;
}

int centered_collision_table(int base, int lag)
{
    if (!ccsum_validate(base, lag, 1)) return 1;
    CCSumTable table;
    if (!ccsum_build(base, lag, &table)) return 1;
    printf("Exact all-lag collision table\n");
    printf("base %d; lag %d; modulus q = %d\n\n",
           base, lag, table.modulus);
    printf("  a       u     T(a)     mu(u)          T^circ(a)\n");
    int ok = 1;
    for (int a = 1; a < table.modulus; a++) {
        if (collision_table_gcd(a, table.modulus) != 1) continue;
        int unit = a % base;
        long long mean_num = table.fiber_sum[unit];
        long long mean_den = table.fiber_size;
        long long centered_num = 0, centered_den = 0;
        ccsum_reduce(&mean_num, &mean_den);
        if (!ccsum_centered_from_table(
                &table, a, &centered_num, &centered_den)) {
            ok = 0;
            continue;
        }
        printf("  %-7d %-5d %+5d     %+5lld/%-5lld    %+6lld/%lld\n",
               a, unit, table.value[a], mean_num, mean_den,
               centered_num, centered_den);
    }
    printf("\n%d unit entries; fiber means are fixed by the complete table.\n",
           table.phi);
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    ccsum_free(&table);
    return ok ? 0 : 1;
}

int centered_collision_fibers(int base, int lag)
{
    if (!ccsum_validate(base, lag, 1)) return 1;
    CCSumTable table;
    if (!ccsum_build(base, lag, &table)) return 1;
    printf("Reduction-fiber means\n");
    printf("base %d; lag %d\n\n", base, lag);
    printf("  u      entries   sum T       mu(u)       centered sum\n");
    int ok = 1;
    for (int unit = 1; unit < base; unit++) {
        if (collision_table_gcd(unit, base) != 1) continue;
        long long mean_num = table.fiber_sum[unit];
        long long mean_den = table.fiber_count[unit];
        ccsum_reduce(&mean_num, &mean_den);
        long long centered_sum = 0;
        for (int a = unit; a < table.modulus; a += base) {
            if (collision_table_gcd(a, table.modulus) != 1) continue;
            centered_sum +=
                (long long)table.fiber_size * table.value[a] -
                table.fiber_sum[unit];
        }
        int fiber_ok = table.fiber_count[unit] == table.fiber_size &&
                       centered_sum == 0;
        if (!fiber_ok) ok = 0;
        printf("  %-6d %-9d %+8lld    %+5lld/%-5lld  %lld  %s\n",
               unit, table.fiber_count[unit], table.fiber_sum[unit],
               mean_num, mean_den, centered_sum,
               fiber_ok ? "PASS" : "FAIL");
    }
    printf("\nEach fiber has b^ell = %d entries and exact centered sum zero.\n",
           table.fiber_size);
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    ccsum_free(&table);
    return ok ? 0 : 1;
}

static int ccsum_identity_checks(const CCSumTable *table,
                                 int *reflection, int *grand_mean,
                                 int *fiber_size, int *fiber_zero,
                                 int *mean_reflection, int *centered_odd)
{
    long long total = 0;
    for (int unit = 1; unit < table->base; unit++) {
        if (collision_table_gcd(unit, table->base) != 1) continue;
        if (table->fiber_count[unit] != table->fiber_size) *fiber_size = 0;
        total += table->fiber_sum[unit];
        long long centered_total = 0;
        for (int a = unit; a < table->modulus; a += table->base) {
            if (collision_table_gcd(a, table->modulus) != 1) continue;
            centered_total +=
                (long long)table->fiber_size * table->value[a] -
                table->fiber_sum[unit];
        }
        if (centered_total != 0) *fiber_zero = 0;
    }
    if (2 * total != -table->phi) *grand_mean = 0;

    for (int a = 1; a < table->modulus; a++) {
        if (collision_table_gcd(a, table->modulus) != 1) continue;
        int complement = table->modulus - a;
        int unit = a % table->base;
        int complement_unit = complement % table->base;
        if (table->value[a] + table->value[complement] != -1)
            *reflection = 0;
        if (table->fiber_sum[unit] + table->fiber_sum[complement_unit] !=
            -table->fiber_size)
            *mean_reflection = 0;
        long long centered =
            (long long)table->fiber_size * table->value[a] -
            table->fiber_sum[unit];
        long long reflected_centered =
            (long long)table->fiber_size * table->value[complement] -
            table->fiber_sum[complement_unit];
        if (centered + reflected_centered != 0) *centered_odd = 0;
    }
    return 1;
}

int centered_collision_gate(int base, int lag)
{
    if (!ccsum_validate(base, lag, 1)) return 1;
    CCSumTable table;
    if (!ccsum_build(base, lag, &table)) return 1;
    int reflection = 1, grand_mean = 1, fiber_size = 1;
    int fiber_zero = 1, mean_reflection = 1, centered_odd = 1;
    ccsum_identity_checks(&table, &reflection, &grand_mean, &fiber_size,
                          &fiber_zero, &mean_reflection, &centered_odd);
    int ok = reflection && grand_mean && fiber_size && fiber_zero &&
             mean_reflection && centered_odd;
    printf("Finite spectral-gate ledger\n");
    printf("base %d; lag %d\n\n", base, lag);
    printf("  table reflection T(a)+T(-a)=-1                  %s\n",
           reflection ? "PASS" : "FAIL");
    printf("  table grand mean is -1/2                        %s\n",
           grand_mean ? "PASS" : "FAIL");
    printf("  every reduction fiber has b^ell entries         %s\n",
           fiber_size ? "PASS" : "FAIL");
    printf("  reflected fiber means sum to -1                 %s\n",
           mean_reflection ? "PASS" : "FAIL");
    printf("  centered table is odd under a -> -a             %s\n",
           centered_odd ? "PASS" : "FAIL");
    printf("  centered sum is zero on every reduction fiber   %s\n",
           fiber_zero ? "PASS" : "FAIL");
    printf("\nOddness kills every even-character coefficient. Fiber-zero kills\n"
           "every character that factors through modulus b. These exact finite\n"
           "identities are the two character-vanishing mechanisms.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    ccsum_free(&table);
    return ok ? 0 : 1;
}

static unsigned char *ccsum_sieve(int limit)
{
    unsigned char *composite = calloc((size_t)limit + 1, 1);
    if (!composite) return NULL;
    composite[0] = 1;
    if (limit >= 1) composite[1] = 1;
    for (int p = 2; p <= limit / p; p++) {
        if (composite[p]) continue;
        for (int64_t multiple = (int64_t)p * p;
             multiple <= limit; multiple += p)
            composite[multiple] = 1;
    }
    return composite;
}

static int ccsum_prime_scan(int cutoff, int base, int lag,
                            int *included, int *largest, long double *sum,
                            CCSumTarget *observed, int capacity)
{
    int modulus = 0;
    if (!included || !largest || !sum ||
        !collision_table_modulus(base, lag, &modulus) || cutoff <= modulus ||
        cutoff > CCSUM_MAX_CUTOFF)
        return 0;
    CCSumTable table;
    if (!ccsum_build(base, lag, &table)) return 0;
    unsigned char *composite = ccsum_sieve(cutoff);
    if (!composite) {
        ccsum_free(&table);
        return 0;
    }
    *included = 0;
    *largest = 0;
    *sum = 0.0L;
    int target = 0;
    for (int p = modulus + 1; p <= cutoff; p++) {
        if (composite[p] || collision_table_gcd(p, base) != 1) continue;
        int residue = p % modulus;
        int unit = residue % base;
        long long numerator =
            (long long)table.fiber_size * table.value[residue] -
            table.fiber_sum[unit];
        *sum += (long double)numerator / ((long double)table.fiber_size * p);
        (*included)++;
        *largest = p;
        if (observed && target < capacity &&
            *included == ccsum_targets[target].count) {
            observed[target].count = *included;
            observed[target].largest = p;
            observed[target].sum = *sum;
            target++;
        }
    }
    free(composite);
    ccsum_free(&table);
    return observed ? target == capacity : 1;
}

int centered_collision_sum(int cutoff, int base, int lag)
{
    if (!ccsum_validate(base, lag, 1)) return 1;
    int modulus = 0;
    collision_table_modulus(base, lag, &modulus);
    if (cutoff <= modulus || cutoff > CCSUM_MAX_CUTOFF) {
        fprintf(stderr, "cutoff must be greater than q=%d and at most %d\n",
                modulus, CCSUM_MAX_CUTOFF);
        return 1;
    }
    int included = 0, largest = 0;
    long double sum = 0.0L;
    if (!ccsum_prime_scan(cutoff, base, lag, &included, &largest, &sum,
                          NULL, 0))
        return 1;
    printf("Finite centered reciprocal-prime sum\n\n");
    printf("base b = %d; lag ell = %d; q = %d; cutoff x = %d\n",
           base, lag, modulus, cutoff);
    printf("included primes p>q = %d; largest p = %d\n", included, largest);
    printf("H^circ_b,ell(x) = %+.15Lf\n", sum);
    printf("The centering uses the fixed complete-table fiber mean, not a running mean.\n");
    printf("This is one finite partial sum. Mertens' theorem in arithmetic\n"
           "progressions supplies the analytic convergence input.\n");
    printf("Result  PASS\n");
    return 0;
}

static int ccsum_snapshot_ok(int print)
{
    int included = 0, largest = 0;
    long double sum = 0.0L;
    CCSumTarget observed[4] = {{0}};
    if (!ccsum_prime_scan(CCSUM_MAX_CUTOFF, 10, 1,
                          &included, &largest, &sum, observed, 4))
        return 0;
    int ok = included == 664554 && largest == 9999991;
    if (print) {
        printf("Reference base-ten centered collision snapshot\n");
        printf("lag one; primes p>100\n\n");
        printf("  primes   p_max       H^circ_10,1\n");
    }
    for (int i = 0; i < 4; i++) {
        int row_ok = observed[i].count == ccsum_targets[i].count &&
            observed[i].largest == ccsum_targets[i].largest &&
            fabsl(observed[i].sum - ccsum_targets[i].sum) < 5e-12L;
        if (!row_ok) ok = 0;
        if (print)
            printf("  %-8d %-10d %+.9Lf  %s\n",
                   observed[i].count, observed[i].largest,
                   observed[i].sum, row_ok ? "PASS" : "FAIL");
    }
    if (print) {
        printf("\n4/4 reference rows reproduced from fixed exact fiber means.\n");
        printf("Result  %s\n", ok ? "PASS" : "FAIL");
    }
    return ok;
}

int centered_collision_snapshot(void)
{
    return ccsum_snapshot_ok(1) ? 0 : 1;
}

int centered_collision_examples(void)
{
    int value_9 = 0, value_109 = 0;
    int lag_two = collision_table_value(10, 2, 9, &value_9) &&
                  collision_table_value(10, 2, 109, &value_109) &&
                  value_9 == 8 && value_109 == -10;
    long long numerator = 0, denominator = 0;
    int table_value = 0;
    int centered = centered_collision_fraction(
        10, 1, 91, &numerator, &denominator, &table_value) &&
        table_value == -9 && numerator == -73 && denominator == 10;
    CCSumTable base_three = {0};
    int prime_columns = ccsum_build(3, 1, &base_three) &&
        base_three.fiber_sum[1] == -2 &&
        base_three.fiber_sum[2] == -1;
    printf("Finite collision-centering examples\n\n");
    printf("  base-ten lag-two classes 9 and 109 give 8 and -10  %s\n",
           lag_two ? "PASS" : "FAIL");
    printf("  base-ten class 91 centers from -9 to -73/10       %s\n",
           centered ? "PASS" : "FAIL");
    printf("  base-three lag-one fiber means are -2/3 and -1/3  %s\n",
           prime_columns ? "PASS" : "FAIL");
    printf("Result  %s\n",
           lag_two && centered && prime_columns ? "PASS" : "FAIL");
    ccsum_free(&base_three);
    return lag_two && centered && prime_columns ? 0 : 1;
}

static int ccsum_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int ccsum_next_prime_in_class(int residue, int modulus)
{
    for (int64_t candidate = (int64_t)modulus + residue;
         candidate <= CCSUM_MAX_CUTOFF; candidate += modulus)
        if (ccsum_is_prime((int)candidate)) return (int)candidate;
    return 0;
}

static void ccsum_report(const char *label, int ok, int *passed)
{
    printf("  %-66s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int centered_collision_verify(void)
{
    int finite = 1, reflection = 1, grand_mean = 1, fiber_size = 1;
    int fiber_zero = 1, mean_reflection = 1, centered_odd = 1, direct = 1;
    int tables = 0, entries = 0, direct_checks = 0;
    for (int base = 2; base <= 12; base++) {
        for (int lag = 1; lag <= 3; lag++) {
            CCSumTable table;
            if (!ccsum_build(base, lag, &table)) {
                finite = 0;
                continue;
            }
            ccsum_identity_checks(&table, &reflection, &grand_mean,
                                  &fiber_size, &fiber_zero,
                                  &mean_reflection, &centered_odd);
            int desired = table.phi < 5 ? table.phi : 5;
            int selected = 0, rank = 0;
            for (int a = 1; a < table.modulus && selected < desired; a++) {
                if (collision_table_gcd(a, table.modulus) != 1) continue;
                int target_rank = desired == 1 ? 0 :
                    selected * (table.phi - 1) / (desired - 1);
                if (rank == target_rank) {
                    int p = ccsum_next_prime_in_class(a, table.modulus);
                    int collision = 0, deviation = 0, multiplier = 0;
                    if (p == 0 || !collision_table_direct_deviation(
                            p, base, lag, &collision, &deviation, &multiplier) ||
                        deviation != table.value[a])
                        direct = 0;
                    selected++;
                    direct_checks++;
                }
                rank++;
            }
            if (selected != desired) direct = 0;
            tables++;
            entries += table.phi;
            ccsum_free(&table);
        }
    }

    int prime_columns = 1, prime_bases = 0, prime_fibers = 0;
    for (int base = 2; base <= 97; base++) {
        if (!ccsum_is_prime(base)) continue;
        CCSumTable table;
        if (!ccsum_build(base, 1, &table)) {
            prime_columns = 0;
            continue;
        }
        prime_bases++;
        for (int unit = 1; unit < base; unit++) {
            if (table.fiber_count[unit] != base ||
                table.fiber_sum[unit] != unit - base)
                prime_columns = 0;
            prime_fibers++;
        }
        ccsum_free(&table);
    }

    int examples = centered_collision_examples() == 0;
    int snapshot = ccsum_snapshot_ok(0);
    int passed = 0;
    printf("\nFinite C verification of all-lag collision centering\n");
    printf("Exact sweep: %d tables, %d unit entries, %d direct prime representatives.\n",
           tables, entries, direct_checks);
    printf("Prime-base column sweep: %d bases and %d fibers through base 97.\n\n",
           prime_bases, prime_fibers);
    ccsum_report("general-lag finite floor tables", finite, &passed);
    ccsum_report("reflection and exact grand mean -1/2",
                 reflection && grand_mean, &passed);
    ccsum_report("equal reduction-fiber sizes", fiber_size, &passed);
    ccsum_report("reflected fiber means sum to -1", mean_reflection, &passed);
    ccsum_report("exact centered oddness", centered_odd, &passed);
    ccsum_report("zero centered sum on every reduction fiber", fiber_zero, &passed);
    ccsum_report("finite table equals sampled direct collision deviations",
                 direct, &passed);
    ccsum_report("prime-base lag-one column formula through base 97",
                 prime_columns, &passed);
    ccsum_report("printed lag-two and centered-value examples", examples, &passed);
    ccsum_report("all reference base-ten centered prime-sum rows", snapshot,
                 &passed);
    printf("\n%d/10 verification groups passed.\n", passed);
    printf("Oddness and fiber-zero give the two exact character-vanishing\n"
           "mechanisms. The prime number theorem and Mertens' theorem in arithmetic\n"
           "progressions supply the external analytic inputs for the prime limits.\n");
    return passed == 10;
}

void centered_collision_help(void)
{
    printf(
        "All-lag collision centering\n\n"
        "Build the exact finite table, center each reduction fiber, and inspect\n"
        "the surviving odd fine-scale signal.\n\n"
        "Usage:\n"
        "  nfield collision-centering inspect <n> [--base <b>] [--lag <ell>]\n"
        "  nfield collision-centering table [--base <b>] [--lag <ell>]\n"
        "  nfield collision-centering fibers [--base <b>] [--lag <ell>]\n"
        "  nfield collision-centering gate [--base <b>] [--lag <ell>]\n"
        "  nfield collision-centering sum <x> [--base <b>] [--lag <ell>]\n"
        "  nfield collision-centering snapshot\n"
        "  nfield collision-centering examples\n"
        "  nfield collision-centering verify\n"
        "  nfield verify collision-centering\n\n"
        "inspect compares the direct collision deviation with the exact table at\n"
        "one integer n>q, then subtracts the fixed mean of its reduction fiber.\n"
        "The input need not be prime. table prints the full table and centered\n"
        "values. fibers exposes every exact coarse-family mean. gate checks the\n"
        "reflection, centered oddness, and fiber-zero identities that kill even\n"
        "characters and characters factoring through the base.\n\n"
        "sum computes a finite centered reciprocal-prime sum using fixed table\n"
        "means. snapshot recomputes all four reference base-ten rows through ten\n"
        "million. The verifier checks bases 2 through 12 at lags 1 through 3,\n"
        "sampled direct representatives, and the prime-base column formula through\n"
        "97. Tables are limited to q<=50000 and direct inspection to n<=10000000.\n"
        "The gate identities establish channel vanishing directly, without\n"
        "enumerating every Dirichlet character. The prime number theorem and\n"
        "Mertens' theorem in arithmetic progressions are external analytic inputs\n"
        "for the two prime limits.\n"
    );
}
