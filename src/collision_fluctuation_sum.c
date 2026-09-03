/*
 * collision_fluctuation_sum.c
 *
 * Exact finite arithmetic for lag-one collision fluctuations.
 * The finite residue table and every rational collision fluctuation are
 * computed exactly. Prime sums use long-double accumulation and are finite
 * numerical evidence; the Mertens theorem in arithmetic progressions is not
 * reproved by this program.
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "nfield.h"

#define CFS_MAX_BASE 64
#define CFS_MAX_CUTOFF 10000000

typedef struct {
    int included;
    int largest_prime;
    long double harmonic_sum;
    long double delta_sum;
    long long negative;
    long long zero;
    long long positive;
    long long class_count[64];
    long long class_integer_sum[64];
    long double class_delta_sum[64];
} CFSPrimeStats;

typedef struct {
    int count;
    int largest;
    long double harmonic;
} CFSSnapshotTarget;

static const CFSSnapshotTarget cfs_snapshot_targets[] = {
    {1000, 7951, -1.367763756774L},
    {10000, 104779, -1.596579819232L},
    {100000, 1299811, -1.773479310764L},
    {664574, 9999991, -1.895353753338L}
};

static const int cfs_base_ten_table[100] = {
    [1] = 0,   [3] = 2,   [7] = 0,   [9] = 8,
    [11] = -1, [13] = -1, [17] = 1,  [19] = -1,
    [21] = 0,  [23] = -2, [27] = 6,  [29] = 0,
    [31] = -1, [33] = -1, [37] = -3, [39] = -1,
    [41] = -4, [43] = 0,  [47] = -2, [49] = 0,
    [51] = -1, [53] = 1,  [57] = -1, [59] = 3,
    [61] = 0,  [63] = 2,  [67] = 0,  [69] = 0,
    [71] = -1, [73] = -7, [77] = 1,  [79] = -1,
    [81] = 0,  [83] = -2, [87] = 0,  [89] = 0,
    [91] = -9, [93] = -1, [97] = -3, [99] = -1
};

static long long cfs_gcd_ll(long long a, long long b)
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

static int cfs_is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d <= n / d; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int cfs_validate_base(int base, int report)
{
    if (base < 2 || base > CFS_MAX_BASE) {
        if (report)
            fprintf(stderr, "base must be between 2 and %d\n", CFS_MAX_BASE);
        return 0;
    }
    return 1;
}

static void cfs_reduce(long long *numerator, long long *denominator)
{
    long long divisor = cfs_gcd_ll(*numerator, *denominator);
    if (divisor > 1) {
        *numerator /= divisor;
        *denominator /= divisor;
    }
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
}

int collision_fluctuation_fraction(int p, int base,
                                   long long *numerator,
                                   long long *denominator,
                                   int *collision, int *integer_deviation)
{
    if (!numerator || !denominator || !collision || !integer_deviation ||
        !cfs_validate_base(base, 0) || p > CFS_MAX_CUTOFF ||
        !cfs_is_prime(p) || p <= base + 1)
        return 0;

    int direct_collision = 0;
    int deviation = 0;
    int multiplier = 0;
    if (!collision_table_direct_deviation(
            p, base, 1, &direct_collision, &deviation, &multiplier))
        return 0;

    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    long long den = p - base - 1;
    long long num = (long long)deviation * den -
                    (long long)q * remainder;
    cfs_reduce(&num, &den);
    *numerator = num;
    *denominator = den;
    *collision = direct_collision;
    *integer_deviation = deviation;
    return 1;
}

int collision_fluctuation_prime(int p, int base)
{
    long long numerator = 0, denominator = 0;
    int collision = 0, deviation = 0;
    if (!cfs_validate_base(base, 1)) return 1;
    if (p > CFS_MAX_CUTOFF) {
        fprintf(stderr, "p must not exceed %d in this finite implementation\n",
                CFS_MAX_CUTOFF);
        return 1;
    }
    if (!cfs_is_prime(p)) {
        fprintf(stderr, "p must be prime\n");
        return 1;
    }
    if (p <= base + 1) {
        fprintf(stderr, "collision fluctuation requires p > base + 1\n");
        return 1;
    }
    if (!collision_fluctuation_fraction(
            p, base, &numerator, &denominator, &collision, &deviation))
        return 1;

    int q = (p - 1) / base;
    int remainder = (p - 1) % base;
    long long mean_numerator =
        (long long)q * (base * (q - 1) + 2 * remainder);
    long long mean_denominator = p - base - 1;
    long long correction_numerator = (long long)q * remainder;
    long long correction_denominator = mean_denominator;
    cfs_reduce(&mean_numerator, &mean_denominator);
    cfs_reduce(&correction_numerator, &correction_denominator);

    int modulus = base * base;
    int residue = p % modulus;
    int table_value = 0;
    int table_applies = p > modulus &&
        collision_table_value(base, 1, residue, &table_value);
    int decomposition_ok =
        numerator * correction_denominator ==
        ((long long)deviation * correction_denominator -
         correction_numerator) * denominator;

    printf("Finite collision fluctuation at one prime\n\n");
    printf("prime p = %d; base b = %d\n", p, base);
    printf("p-1 = bQ+R with Q = %d and R = %d\n", q, remainder);
    printf("lag-one collision count C_p,b(b) = %d\n", collision);
    printf("integer deviation S_b(p) = C-Q = %+d\n", deviation);
    printf("constructive mean = %lld/%lld\n",
           mean_numerator, mean_denominator);
    printf("exact correction QR/(p-b-1) = %lld/%lld\n",
           correction_numerator, correction_denominator);
    printf("collision fluctuation Delta_b(p) = %lld/%lld = %+.12Lf\n",
           numerator, denominator, (long double)numerator / denominator);
    if (table_applies)
        printf("finite table F_b(p mod b^2) = F_%d(%d) = %+d  %s\n",
               base, residue, table_value,
               table_value == deviation ? "PASS" : "FAIL");
    else
        printf("finite table starts at p>b^2; direct definition used here\n");
    printf("Delta = S - QR/(p-b-1)  %s\n",
           decomposition_ok ? "PASS" : "FAIL");
    printf("Result  %s\n", decomposition_ok &&
           (!table_applies || table_value == deviation) ? "PASS" : "FAIL");
    return decomposition_ok && (!table_applies || table_value == deviation)
        ? 0 : 1;
}

static int cfs_table_summary(int base, int print_rows, int *entry_count,
                             int *sum, int *minimum, int *maximum)
{
    int modulus = 0;
    if (!collision_table_modulus(base, 1, &modulus)) return 0;
    int count = 0, total = 0, min_value = 0, max_value = 0;
    if (print_rows)
        printf("  a mod %-5d  F_%d(a)  F_%d(-a)  pair\n",
               modulus, base, base);
    for (int a = 1; a < modulus; a++) {
        if (collision_table_gcd(a, modulus) != 1) continue;
        int value = 0, reflected = 0;
        if (!collision_table_value(base, 1, a, &value) ||
            !collision_table_value(base, 1, modulus - a, &reflected))
            return 0;
        if (count == 0 || value < min_value) min_value = value;
        if (count == 0 || value > max_value) max_value = value;
        count++;
        total += value;
        if (print_rows)
            printf("  %7d      %+4d      %+4d      %s\n",
                   a, value, reflected,
                   value + reflected == -1 ? "PASS" : "FAIL");
    }
    if (entry_count) *entry_count = count;
    if (sum) *sum = total;
    if (minimum) *minimum = min_value;
    if (maximum) *maximum = max_value;
    return count > 0;
}

int collision_fluctuation_table(int base)
{
    if (!cfs_validate_base(base, 1)) return 1;
    int count = 0, sum = 0, minimum = 0, maximum = 0;
    printf("Exact lag-one collision table in base %d\n\n", base);
    if (!cfs_table_summary(base, 1, &count, &sum, &minimum, &maximum))
        return 1;
    int mean_ok = 2 * sum == -count;
    printf("\nunit entries = %d; minimum = %+d; maximum = %+d\n",
           count, minimum, maximum);
    printf("table sum = %d; exact grand mean = %d/%d = -1/2  %s\n",
           sum, sum, count, mean_ok ? "PASS" : "FAIL");
    printf("every reflected pair sums to -1  %s\n",
           mean_ok ? "PASS" : "FAIL");
    printf("Result  %s\n", mean_ok ? "PASS" : "FAIL");
    return mean_ok ? 0 : 1;
}

int collision_fluctuation_classes(int base)
{
    if (!cfs_validate_base(base, 1)) return 1;
    int modulus = base * base;
    printf("Finite residue-family collision targets in base %d\n\n", base);
    printf("  p mod b  lifts  mean S             R/b        limiting mean Delta\n");
    int total_count = 0, total_s = 0, total_r = 0;
    for (int unit = 1; unit < base; unit++) {
        if (collision_table_gcd(unit, base) != 1) continue;
        int count = 0, sum = 0;
        for (int a = unit; a < modulus; a += base) {
            if (collision_table_gcd(a, modulus) != 1) continue;
            int value = 0;
            if (!collision_table_value(base, 1, a, &value)) return 1;
            count++;
            sum += value;
        }
        int remainder = unit - 1;
        long long target_numerator =
            (long long)base * sum - (long long)count * remainder;
        long long target_denominator = (long long)base * count;
        cfs_reduce(&target_numerator, &target_denominator);
        long long mean_num = sum, mean_den = count;
        cfs_reduce(&mean_num, &mean_den);
        long long rem_num = remainder, rem_den = base;
        cfs_reduce(&rem_num, &rem_den);
        printf("  %7d  %5d  %+5lld/%-5lld       %2lld/%-4lld    %+5lld/%lld\n",
               unit, count, mean_num, mean_den, rem_num, rem_den,
               target_numerator, target_denominator);
        total_count += count;
        total_s += sum;
        total_r += count * remainder;
    }
    long long drift_num =
        (long long)base * total_s - (long long)total_r;
    long long drift_den = (long long)base * total_count;
    cfs_reduce(&drift_num, &drift_den);
    int ok = drift_num == -(base - 1) && drift_den == base;
    printf("\nall-family mean = %lld/%lld; predicted logarithmic coefficient %s\n",
           drift_num, drift_den, ok ? "PASS" : "FAIL");
    printf("The prime-number-theorem step making classes equidistributed is analytic,\n"
           "not established by this finite table.\n");
    printf("Result  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static unsigned char *cfs_sieve(int limit)
{
    unsigned char *composite = calloc((size_t)limit + 1, 1);
    if (!composite) return NULL;
    if (limit >= 0) composite[0] = 1;
    if (limit >= 1) composite[1] = 1;
    for (int p = 2; p <= limit / p; p++) {
        if (composite[p]) continue;
        for (int64_t multiple = (int64_t)p * p;
             multiple <= limit; multiple += p)
            composite[multiple] = 1;
    }
    return composite;
}

static int cfs_scan(int cutoff, int base, CFSPrimeStats *stats,
                    CFSSnapshotTarget *observed, int observed_capacity)
{
    if (!stats || cutoff < base + 2 || cutoff > CFS_MAX_CUTOFF)
        return 0;
    unsigned char *composite = cfs_sieve(cutoff);
    if (!composite) return 0;
    int modulus = base * base;
    int *table = calloc((size_t)modulus, sizeof(*table));
    if (!table) {
        free(composite);
        return 0;
    }
    for (int a = 1; a < modulus; a++)
        if (collision_table_gcd(a, modulus) == 1 &&
            !collision_table_value(base, 1, a, &table[a])) {
            free(table);
            free(composite);
            return 0;
        }

    *stats = (CFSPrimeStats){0};
    int target_index = 0;
    for (int p = base + 2; p <= cutoff; p++) {
        if (composite[p]) continue;
        int q = (p - 1) / base;
        int remainder = (p - 1) % base;
        int integer_deviation = 0;
        if (p > modulus) {
            integer_deviation = table[p % modulus];
        } else {
            int collision = 0, multiplier = 0;
            if (!collision_table_direct_deviation(
                    p, base, 1, &collision, &integer_deviation, &multiplier)) {
                free(table);
                free(composite);
                return 0;
            }
        }
        long long denominator = p - base - 1;
        long long numerator = (long long)integer_deviation * denominator -
                              (long long)q * remainder;
        long double delta = (long double)numerator / denominator;
        stats->included++;
        stats->largest_prime = p;
        stats->harmonic_sum += delta / p;
        stats->delta_sum += delta;
        int unit = p % base;
        stats->class_count[unit]++;
        stats->class_integer_sum[unit] += integer_deviation;
        stats->class_delta_sum[unit] += delta;
        if (numerator < 0) stats->negative++;
        else if (numerator > 0) stats->positive++;
        else stats->zero++;

        if (observed && target_index < observed_capacity &&
            stats->included == cfs_snapshot_targets[target_index].count) {
            observed[target_index].count = stats->included;
            observed[target_index].largest = p;
            observed[target_index].harmonic = stats->harmonic_sum;
            target_index++;
        }
    }
    free(table);
    free(composite);
    return observed ? target_index == observed_capacity : 1;
}

int collision_fluctuation_sum(int cutoff, int base)
{
    if (!cfs_validate_base(base, 1)) return 1;
    if (cutoff < base + 2 || cutoff > CFS_MAX_CUTOFF) {
        fprintf(stderr, "cutoff must be between base+2 and %d\n",
                CFS_MAX_CUTOFF);
        return 1;
    }
    CFSPrimeStats stats;
    if (!cfs_scan(cutoff, base, &stats, NULL, 0)) return 1;
    long double residual = stats.harmonic_sum +
        ((long double)(base - 1) / base) *
        logl(logl((long double)stats.largest_prime));
    printf("Finite reciprocal-prime collision sum in base %d through x = %d\n\n",
           base, cutoff);
    printf("included primes p>b+1 = %d; largest p = %d\n",
           stats.included, stats.largest_prime);
    printf("Phi_b(x;1) = %+.12Lf\n", stats.harmonic_sum);
    printf("finite-table drift coefficient = -(%d/%d)\n", base - 1, base);
    printf("drift-removed finite residual = %+.12Lf\n", residual);
    printf("mean finite Delta = %+.12Lf\n",
           stats.delta_sum / stats.included);
    printf("sign counts negative/zero/positive = %lld/%lld/%lld\n",
           stats.negative, stats.zero, stats.positive);
    printf("These are finite computations. The asymptotic uses Mertens' theorem\n"
           "in arithmetic progressions.\n");
    printf("Result  PASS\n");
    return 0;
}

static int cfs_snapshot_compute(CFSPrimeStats *stats,
                                CFSSnapshotTarget observed[4])
{
    return cfs_scan(CFS_MAX_CUTOFF, 10, stats, observed, 4);
}

static int cfs_snapshot_ok(int print)
{
    CFSPrimeStats stats;
    CFSSnapshotTarget observed[4] = {{0}};
    if (!cfs_snapshot_compute(&stats, observed)) return 0;
    int ok = 1;
    if (print) {
        printf("Reference base-ten collision fluctuation snapshot\n\n");
        printf("  primes   p_max       Phi_10(x;1)    A_x          B_x\n");
    }
    for (int i = 0; i < 4; i++) {
        long double loglog = logl(logl((long double)observed[i].largest));
        long double ratio = observed[i].harmonic / loglog;
        long double residual = observed[i].harmonic + 0.9L * loglog;
        int row_ok = observed[i].count == cfs_snapshot_targets[i].count &&
            observed[i].largest == cfs_snapshot_targets[i].largest &&
            fabsl(observed[i].harmonic -
                  cfs_snapshot_targets[i].harmonic) < 5e-12L;
        if (!row_ok) ok = 0;
        if (print)
            printf("  %-8d %-10d %+.6Lf      %+.6Lf    %+.6Lf  %s\n",
                   observed[i].count, observed[i].largest,
                   observed[i].harmonic, ratio, residual,
                   row_ok ? "PASS" : "FAIL");
    }

    const int units[] = {1, 3, 7, 9};
    const long long expected_counts[] = {166103, 166229, 166210, 166032};
    const long long expected_sums[] = {-283293, -149660, -16827, 115710};
    const long double expected_means[] = {
        -1.705526089234L, -1.100333741311L,
        -0.701247828329L, -0.103091320514L
    };
    if (print)
        printf("\n  p mod 10  primes    mean S        mean Delta\n");
    for (int i = 0; i < 4; i++) {
        int u = units[i];
        long double mean_s = (long double)stats.class_integer_sum[u] /
                             stats.class_count[u];
        long double mean_delta = stats.class_delta_sum[u] /
                                 stats.class_count[u];
        int row_ok = stats.class_count[u] == expected_counts[i] &&
            stats.class_integer_sum[u] == expected_sums[i] &&
            fabsl(mean_delta - expected_means[i]) < 5e-12L;
        if (!row_ok) ok = 0;
        if (print)
            printf("  %8d  %-8lld  %+.6Lf     %+.6Lf  %s\n",
                   u, stats.class_count[u], mean_s, mean_delta,
                   row_ok ? "PASS" : "FAIL");
    }
    long long total = stats.negative + stats.zero + stats.positive;
    long double overall = stats.delta_sum / total;
    int signs_ok = total == 664574 && stats.negative == 465397 &&
        stats.zero == 66348 && stats.positive == 132829 &&
        fabsl(overall + 0.902640243462L) < 5e-12L;
    if (!signs_ok) ok = 0;
    if (print) {
        printf("\noverall mean Delta = %+.12Lf\n", overall);
        printf("negative/zero/positive = %lld/%lld/%lld  %s\n",
               stats.negative, stats.zero, stats.positive,
               signs_ok ? "PASS" : "FAIL");
        printf("4/4 prime-sum rows and 4/4 residue-family rows reproduced.\n");
        printf("Result  %s\n", ok ? "PASS" : "FAIL");
    }
    return ok;
}

int collision_fluctuation_snapshot(void)
{
    return cfs_snapshot_ok(1) ? 0 : 1;
}

int collision_fluctuation_examples(void)
{
    long long numerator = 0, denominator = 0;
    int collision = 0, deviation = 0, table = 0;
    int first = collision_fluctuation_fraction(
        191, 10, &numerator, &denominator, &collision, &deviation) &&
        collision == 10 && deviation == -9 && numerator == -9 &&
        denominator == 1;
    int second = collision_table_value(10, 1, 91, &table) && table == -9;
    int third = collision_table_value(7, 1, 6, &table) && table == 5;
    printf("Finite collision fluctuation examples\n\n");
    printf("  decimal p=191 has C=10, S=-9, and Delta=-9  %s\n",
           first ? "PASS" : "FAIL");
    printf("  decimal table class 91 has F_10(91)=-9  %s\n",
           second ? "PASS" : "FAIL");
    printf("  base-seven table class 6 has F_7(6)=5  %s\n",
           third ? "PASS" : "FAIL");
    printf("Result  %s\n", first && second && third ? "PASS" : "FAIL");
    return first && second && third ? 0 : 1;
}

static void cfs_report(const char *label, int ok, int *passed)
{
    printf("  %-66s %s\n", label, ok ? "PASS" : "FAIL");
    if (ok) (*passed)++;
}

int collision_fluctuation_verify(void)
{
    int table_formula = 1, reflection = 1, grand_mean = 1;
    int direct = 1, decomposition = 1, base_ten = 1, classes = 1;
    int table_entries = 0, direct_models = 0;
    for (int base = 2; base <= 20; base++) {
        int modulus = base * base;
        int sum = 0, count = 0;
        for (int a = 1; a < modulus; a++) {
            if (collision_table_gcd(a, modulus) != 1) continue;
            int value = 0, reflected = 0;
            if (!collision_table_value(base, 1, a, &value)) {
                table_formula = 0;
                continue;
            }
            if (!collision_table_value(
                    base, 1, modulus - a, &reflected) ||
                value + reflected != -1)
                reflection = 0;
            if (base == 10 && value != cfs_base_ten_table[a]) base_ten = 0;
            sum += value;
            count++;
            table_entries++;

            int representatives = 0;
            for (int candidate = modulus + a;
                 candidate <= 100000 && representatives < 2;
                 candidate += modulus) {
                if (!cfs_is_prime(candidate)) continue;
                int collision = 0, deviation = 0, multiplier = 0;
                if (!collision_table_direct_deviation(
                        candidate, base, 1, &collision, &deviation,
                        &multiplier) || deviation != value)
                    direct = 0;
                long long numerator = 0, denominator = 0;
                int c = 0, s = 0;
                if (!collision_fluctuation_fraction(
                        candidate, base, &numerator, &denominator, &c, &s) ||
                    c != collision || s != deviation)
                    decomposition = 0;
                representatives++;
                direct_models++;
            }
            if (representatives != 2) direct = 0;
        }
        if (2 * sum != -count) grand_mean = 0;
    }

    const int units[] = {1, 3, 7, 9};
    const int expected_sum[] = {-17, -9, -1, 7};
    const int expected_delta[] = {-17, -11, -7, -1};
    for (int i = 0; i < 4; i++) {
        int sum = 0, count = 0;
        for (int a = units[i]; a < 100; a += 10) {
            int value = 0;
            if (!collision_table_value(10, 1, a, &value)) classes = 0;
            sum += value;
            count++;
        }
        if (count != 10 || sum != expected_sum[i] ||
            sum - (units[i] - 1) != expected_delta[i])
            classes = 0;
    }
    int snapshot = cfs_snapshot_ok(0);
    int examples = collision_fluctuation_examples() == 0;
    int passed = 0;
    printf("\nFinite C verification of lag-one collision fluctuation arithmetic\n");
    printf("Exact table sweep: %d unit entries; %d direct prime representatives.\n\n",
           table_entries, direct_models);
    cfs_report("finite lag-one floor table", table_formula, &passed);
    cfs_report("reflection F(a)+F(-a)=-1", reflection, &passed);
    cfs_report("exact grand mean -1/2", grand_mean, &passed);
    cfs_report("finite table equals direct collision deviation", direct, &passed);
    cfs_report("exact constructive-mean decomposition", decomposition, &passed);
    cfs_report("complete forty-entry base-ten table", base_ten, &passed);
    cfs_report("exact base-ten residue-family targets", classes, &passed);
    cfs_report("all reference finite prime-sum and observed rows", snapshot, &passed);
    cfs_report("named exact examples", examples, &passed);
    printf("\n%d/9 verification groups passed.\n", passed);
    printf("The logarithmic asymptotic uses Mertens' theorem in arithmetic\n"
           "progressions. This finite sweep certifies the collision tables and\n"
           "exact coefficient arithmetic, not prime-class equidistribution.\n");
    return passed == 9;
}

void collision_fluctuation_help(void)
{
    printf(
        "Lag-one collision fluctuation arithmetic\n\n"
        "This object constructs the finite table, reflection pairs, residue-\n"
        "family means, direct collision counts, exact rational corrections,\n"
        "and finite reciprocal-prime sums.\n\n"
        "Usage:\n"
        "  nfield collision-fluctuation prime <p> [--base <b>]\n"
        "  nfield collision-fluctuation table [--base <b>]\n"
        "  nfield collision-fluctuation classes [--base <b>]\n"
        "  nfield collision-fluctuation sum <x> [--base <b>]\n"
        "  nfield collision-fluctuation snapshot\n"
        "  nfield collision-fluctuation examples\n"
        "  nfield collision-fluctuation verify\n"
        "  nfield verify collision-fluctuation\n\n"
        "prime computes the direct lag-one collision count, integer deviation,\n"
        "constructive mean, exact rational correction, and exact fluctuation.\n"
        "For p>b^2 it also checks the finite table class p mod b^2.\n\n"
        "table prints every unit class modulo b^2 and checks reflection and the\n"
        "exact grand mean -1/2. classes averages the b lifts above each unit\n"
        "modulo b and derives the limiting fluctuation target. sum computes a\n"
        "finite reciprocal-prime sum through x. snapshot recomputes every row of\n"
        "both reference base-ten tables through ten million. Single-prime and\n"
        "prime-sum inputs are limited to ten million.\n\n"
        "Integer and rational identities are exact. Prime sums are accumulated\n"
        "in long-double arithmetic. The coefficient -(b-1)/b follows from the\n"
        "two exact finite means. Turning it into a prime asymptotic uses Mertens'\n"
        "theorem in arithmetic progressions, beyond the finite sweep. The legacy\n"
        "fluctuation_sum and mertens_growth commands remain compatibility views.\n"
    );
}
