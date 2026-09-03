/* Exact conjugate-pair relabeling law and finite underlap ledgers. */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "finite_character_core.h"
#include "nfield.h"
#include "primitive_odd_sector_core.h"

enum {
    RELABELING_BASE_COUNT = 11,
    RELABELING_NONTRIVIAL_BASES = 10,
    RELABELING_CUTOFF_COUNT = 6
};

static const int relabeling_bases[RELABELING_BASE_COUNT] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
};

static const int relabeling_cutoffs[RELABELING_CUTOFF_COUNT] = {
    250000, 500000, 1000000, 2000000, 3000000, 5000000
};

typedef struct {
    int base;
    long double rho;
    long double z;
    long double collision_support;
    long double prime_support;
} RelabelingPrimaryFixture;

static const RelabelingPrimaryFixture primary_fixtures
    [RELABELING_NONTRIVIAL_BASES] = {
    {5, 0.6216370807L,-0.7106825304L,4.5925555685L,5.2113168112L},
    {7, 0.4801092979L,-0.8650308493L,7.0038198548L,9.7735537800L},
    {11,0.5544131202L,-1.0867453779L,14.2323135458L,30.9647686033L},
    {13,0.5711875855L,-1.3568102860L,17.9743108209L,49.7092243774L},
    {17,0.5353103814L,-1.7261424891L,28.0469456945L,87.0653026174L},
    {19,0.7690192205L,-0.9148673979L,33.1792344705L,108.3662055621L},
    {23,0.5804635141L,-2.1016861616L,44.0550919009L,177.8111690568L},
    {29,0.6095803605L,-2.2611257532L,63.9536576764L,290.0226867876L},
    {31,0.6132358722L,-2.2395750446L,69.3445570623L,334.2981081514L},
    {37,0.5739128563L,-2.9284717987L,92.0497964545L,493.7343568389L}
};

static const long double cutoff_fixtures[RELABELING_CUTOFF_COUNT][4] = {
    {0.6237291897L,0.1444555768L,0.3586040835L,0.8471950277L},
    {0.6267180468L,0.1009669493L,0.4665706698L,0.7639037016L},
    {0.5971727549L,0.0838361661L,0.4840685211L,0.7386120346L},
    {0.5908869289L,0.0714151318L,0.4801092979L,0.7690192205L},
    {0.5748378070L,0.0479932346L,0.4816178684L,0.6519210651L},
    {0.5462622287L,0.0800961919L,0.4316434918L,0.6981855048L}
};

typedef struct {
    int64_t centered_sum;
    uint64_t centered_square_sum;
    uint64_t permutations;
} RelabelingEnumeration;

static void enumerate_permutations(const int64_t *left_centered,
                                   const int64_t *right_centered,
                                   int count,
                                   int depth,
                                   int *used,
                                   int64_t dot,
                                   RelabelingEnumeration *enumeration)
{
    if (depth == count) {
        enumeration->centered_sum += dot;
        enumeration->centered_square_sum += (uint64_t)(dot * dot);
        enumeration->permutations++;
        return;
    }
    for (int index = 0; index < count; index++) {
        if (used[index]) continue;
        used[index] = 1;
        enumerate_permutations(
            left_centered, right_centered, count, depth + 1, used,
            dot + left_centered[depth] * right_centered[index],
            enumeration);
        used[index] = 0;
    }
}

static int exact_relabeling_fixture(int report)
{
    static const int64_t left[4] = {1, 2, 3, 4};
    static const int64_t right[4] = {2, 5, 7, 11};
    int64_t left_centered[4], right_centered[4];
    int used[4] = {0};
    int64_t left_total = 0, right_total = 0;
    uint64_t left_square = 0, right_square = 0;
    RelabelingEnumeration enumeration = {0};
    int failures = 0;

    for (int index = 0; index < 4; index++) {
        left_total += left[index];
        right_total += right[index];
    }
    for (int index = 0; index < 4; index++) {
        left_centered[index] = 4 * left[index] - left_total;
        right_centered[index] = 4 * right[index] - right_total;
        left_square += (uint64_t)(left_centered[index] *
                                  left_centered[index]);
        right_square += (uint64_t)(right_centered[index] *
                                   right_centered[index]);
    }
    enumerate_permutations(left_centered, right_centered, 4, 0,
                           used, 0, &enumeration);
    if (enumeration.permutations != 24 || enumeration.centered_sum != 0)
        failures++;
    if (3 * enumeration.centered_square_sum !=
        enumeration.permutations * left_square * right_square)
        failures++;
    if (report) {
        printf("Exact relabeling law\n");
        printf("Exhaustive four-pair fixture\n\n");
        printf("  permutations=%llu; expected=24  %s\n",
               (unsigned long long)enumeration.permutations,
               enumeration.permutations == 24 ? "PASS" : "FAIL");
        printf("  centered first moment=%lld; expected=0  %s\n",
               (long long)enumeration.centered_sum,
               enumeration.centered_sum == 0 ? "PASS" : "FAIL");
        printf("  exact second-moment numerator identity  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("\nThis exhausts one nonuniform rational fixture. The exact formula\n");
        printf("holds for every finite number of pairs.\n");
        printf("Classification  exact finite integer arithmetic.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    return failures;
}

int conjugate_pair_relabeling_exact_law(void)
{
    return exact_relabeling_fixture(1) == 0 ? 0 : 1;
}

static int compute_all_results(PrimitiveOddSectorResult *results,
                               int **primes_out,
                               int *prime_count_out)
{
    int *primes;
    int prime_count = 0;
    int built = 0;

    primes = finite_character_primes(
        FINITE_CHARACTER_MAX_CUTOFF, &prime_count);
    if (!primes) return 0;
    for (int base_index = 0; base_index < RELABELING_BASE_COUNT;
         base_index++) {
        if (primitive_odd_sector_compute(
                relabeling_bases[base_index], primes, prime_count,
                relabeling_cutoffs, RELABELING_CUTOFF_COUNT,
                &results[base_index]) != 0) {
            for (int index = 0; index < built; index++)
                primitive_odd_sector_result_free(&results[index]);
            free(primes);
            return 0;
        }
        built++;
    }
    *primes_out = primes;
    *prime_count_out = prime_count;
    return 1;
}

static void free_all_results(PrimitiveOddSectorResult *results, int *primes)
{
    for (int base_index = 0; base_index < RELABELING_BASE_COUNT;
         base_index++)
        primitive_odd_sector_result_free(&results[base_index]);
    free(primes);
}

static int primary_ledger_audit(int report)
{
    PrimitiveOddSectorResult results[RELABELING_BASE_COUNT] = {0};
    int *primes = NULL;
    int prime_count = 0;
    int failures = 0;
    int below = 0;
    int cutoff_index = 3;

    if (!compute_all_results(results, &primes, &prime_count)) return 1;
    (void)prime_count;
    if (report) {
        printf("Conjugate-pair relabeling\n");
        printf("Declared finite underlap ledger\n\n");
        printf("cutoff X=2000000; prime interval b^2 < p < X\n");
        printf("  b  active chars       rho             z      collision eff   prime eff\n");
    }
    for (int base_index = 1; base_index < RELABELING_BASE_COUNT;
         base_index++) {
        const PrimitiveOddSectorRow *row =
            &results[base_index].row[cutoff_index];
        const RelabelingPrimaryFixture *fixture =
            &primary_fixtures[base_index - 1];
        if (row->rho < 1.0L) below++;
        if (relabeling_bases[base_index] != fixture->base ||
            fabsl(row->rho - fixture->rho) > 5.0e-10L ||
            fabsl(row->z - fixture->z) > 5.0e-10L ||
            fabsl(row->collision_support - fixture->collision_support) >
                5.0e-9L ||
            fabsl(row->prime_support - fixture->prime_support) > 5.0e-9L)
            failures++;
        if (report)
            printf(" %2d  %6d      %.10Lf  %+.10Lf    %10.4Lf  %10.4Lf\n",
                   relabeling_bases[base_index], row->active_characters,
                   row->rho, row->z,
                   row->collision_support, row->prime_support);
    }
    if (below != RELABELING_NONTRIVIAL_BASES) failures++;
    if (report) {
        printf("\nRows below exact relabeling mean one: %d/%d.\n",
               below, RELABELING_NONTRIVIAL_BASES);
        printf("All displayed rho, z, and support fixtures  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("Classification  finite numerical evidence, not a limiting law.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    free_all_results(results, primes);
    return failures;
}

int conjugate_pair_relabeling_ledger(void)
{
    return primary_ledger_audit(1) == 0 ? 0 : 1;
}

static int cutoff_ledger_audit(int report, int *below_out)
{
    PrimitiveOddSectorResult results[RELABELING_BASE_COUNT] = {0};
    int *primes = NULL;
    int prime_count = 0;
    int failures = 0;
    int total_below = 0;

    if (!compute_all_results(results, &primes, &prime_count)) return 1;
    (void)prime_count;
    if (report) {
        printf("Conjugate-pair relabeling\n");
        printf("Six-cutoff underlap summary\n\n");
        printf("       X       mean rho       pop sd       minimum       maximum   below 1\n");
    }
    for (int cutoff_index = 0; cutoff_index < RELABELING_CUTOFF_COUNT;
         cutoff_index++) {
        long double mean = 0.0L, variance = 0.0L;
        long double minimum = 2.0L, maximum = 0.0L;
        int below = 0;
        for (int base_index = 1; base_index < RELABELING_BASE_COUNT;
             base_index++) {
            long double rho = results[base_index].row[cutoff_index].rho;
            mean += rho;
            if (rho < minimum) minimum = rho;
            if (rho > maximum) maximum = rho;
            if (rho < 1.0L) below++;
        }
        mean /= RELABELING_NONTRIVIAL_BASES;
        for (int base_index = 1; base_index < RELABELING_BASE_COUNT;
             base_index++) {
            long double delta =
                results[base_index].row[cutoff_index].rho - mean;
            variance += delta * delta;
        }
        variance /= RELABELING_NONTRIVIAL_BASES;
        if (fabsl(mean - cutoff_fixtures[cutoff_index][0]) > 5.0e-10L ||
            fabsl(sqrtl(variance) - cutoff_fixtures[cutoff_index][1]) >
                5.0e-10L ||
            fabsl(minimum - cutoff_fixtures[cutoff_index][2]) > 5.0e-10L ||
            fabsl(maximum - cutoff_fixtures[cutoff_index][3]) > 5.0e-10L ||
            below != RELABELING_NONTRIVIAL_BASES)
            failures++;
        total_below += below;
        if (report)
            printf(" %7d     %.10Lf   %.10Lf   %.10Lf   %.10Lf    %d/10\n",
                   relabeling_cutoffs[cutoff_index], mean, sqrtl(variance),
                   minimum, maximum, below);
    }
    if (report) {
        printf("\nAll %d nontrivial finite rows lie below the null mean.\n",
               total_below);
        printf("All six declared summary fixtures  %s\n",
               failures == 0 ? "PASS" : "FAIL");
        printf("The changing means do not establish cutoff stability.\n");
        printf("Classification  finite numerical evidence only.\n");
        printf("Result  %s\n", failures == 0 ? "PASS" : "FAIL");
    }
    if (below_out) *below_out = total_below;
    free_all_results(results, primes);
    return failures;
}

int conjugate_pair_relabeling_cutoffs(void)
{
    return cutoff_ledger_audit(1, NULL) == 0 ? 0 : 1;
}

int conjugate_pair_relabeling_verify(void)
{
    int below = 0;
    int exact_ok, primary_ok, cutoffs_ok;
    int passed = 0;

    printf("Conjugate-pair relabeling verification\n\n");
    exact_ok = exact_relabeling_fixture(0) == 0;
    primary_ok = primary_ledger_audit(0) == 0;
    cutoffs_ok = cutoff_ledger_audit(0, &below) == 0;
    printf("  exhaustive exact mean and variance fixture        %s\n",
           exact_ok ? "PASS" : "FAIL");
    if (exact_ok) passed++;
    printf("  ten declared rows at cutoff two million          %s\n",
           primary_ok ? "PASS" : "FAIL");
    if (primary_ok) passed++;
    printf("  all six cutoff summaries and 60/60 underlaps      %s\n",
           cutoffs_ok && below == 60 ? "PASS" : "FAIL");
    if (cutoffs_ok && below == 60) passed++;
    printf("\n%d/3 verification groups passed.\n", passed);
    printf("Proved  uniform finite permutation gives exact mean and variance.\n");
    printf("Finite evidence  every displayed row is below one, but the changing\n");
    printf("cutoff means do not define a stable repulsion constant.\n");
    printf("Open  limiting overlap, limiting coupling, and arithmetic mechanism.\n");
    return passed == 3;
}

void conjugate_pair_relabeling_help(void)
{
    printf(
        "Conjugate-pair relabeling\n\n"
        "Commands\n"
        "  nfield conjugate-pair-relabeling exact-law\n"
        "      Exhaust a nonuniform four-pair fixture for the exact mean and\n"
        "      variance identity.\n"
        "  nfield conjugate-pair-relabeling ledger\n"
        "      Reproduce rho, z, and entropy supports at X=2000000.\n"
        "  nfield conjugate-pair-relabeling cutoffs\n"
        "      Reproduce all six ten-base summary rows and 60 finite underlaps.\n"
        "  nfield conjugate-pair-relabeling verify\n"
        "  nfield verify conjugate-pair-relabeling\n\n"
        "Scope\n"
        "  proved             exact mean-one and variance law.\n"
        "  exact computation exhaustive rational fixture for that law.\n"
        "  finite numerical  explicitly bounded character and prime sums.\n"
        "  open              no stable constant, limiting overlap, or mechanism.\n"
    );
}
