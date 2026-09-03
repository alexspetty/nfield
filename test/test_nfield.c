/*
 * test_nfield.c: Unit tests for nfield core functions.
 *
 * Run via: make test
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "../src/nfield.h"
#include "../src/finite_character_core.h"
#include "../src/collision_spectrum_core.h"
#include "../src/periodic_zeta_core.h"

static int tests_run    = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define ASSERT(cond, msg) do { \
    tests_run++; \
    if (cond) { tests_passed++; } \
    else { tests_failed++; printf("  FAIL: %s\n", msg); } \
} while (0)

#define ASSERT_INT(a, b, msg) do { \
    tests_run++; \
    if ((a) == (b)) { tests_passed++; } \
    else { tests_failed++; printf("  FAIL: %s (got %d, expected %d)\n", msg, (a), (b)); } \
} while (0)

#define ASSERT_DBL(a, b, tol, msg) do { \
    tests_run++; \
    if (fabs((a) - (b)) < (tol)) { tests_passed++; } \
    else { tests_failed++; printf("  FAIL: %s (got %.8f, expected %.8f)\n", msg, (double)(a), (double)(b)); } \
} while (0)

/* ── repetend tests ─────────────────────────────────────── */

static void test_repetend(void)
{
    printf("repetend_compute:\n");

    /* 1/7 = 0.(142857) in base 10 */
    {
        Repetend r = repetend_compute(1, 7, 10);
        ASSERT_INT(r.cycle_len, 6, "1/7 cycle length = 6");
        ASSERT_INT(r.cycle_start, 0, "1/7 cycle starts at 0");
        int expected[] = {1, 4, 2, 8, 5, 7};
        int ok = 1;
        for (int i = 0; i < 6; i++)
            if (r.digits[r.cycle_start + i] != expected[i]) ok = 0;
        ASSERT(ok, "1/7 digits = 142857");
        repetend_free(&r);
    }

    /* 1/4 = 0.25 terminates */
    {
        Repetend r = repetend_compute(1, 4, 10);
        ASSERT_INT(r.cycle_len, 0, "1/4 terminates");
        ASSERT_INT(r.len, 2, "1/4 has 2 digits");
        ASSERT_INT(r.digits[0], 2, "1/4 first digit = 2");
        ASSERT_INT(r.digits[1], 5, "1/4 second digit = 5");
        repetend_free(&r);
    }

    /* 1/3 = 0.(3) in base 10 */
    {
        Repetend r = repetend_compute(1, 3, 10);
        ASSERT_INT(r.cycle_len, 1, "1/3 cycle length = 1");
        ASSERT_INT(r.digits[r.cycle_start], 3, "1/3 repeating digit = 3");
        repetend_free(&r);
    }

    /* 1/13 in base 10: cycle length 6 */
    {
        Repetend r = repetend_compute(1, 13, 10);
        ASSERT_INT(r.cycle_len, 6, "1/13 cycle length = 6");
        int expected[] = {0, 7, 6, 9, 2, 3};
        int ok = 1;
        for (int i = 0; i < 6; i++)
            if (r.digits[r.cycle_start + i] != expected[i]) ok = 0;
        ASSERT(ok, "1/13 digits = 076923");
        repetend_free(&r);
    }

    /* 2/7 is a rotation of 1/7 */
    {
        Repetend r1 = repetend_compute(1, 7, 10);
        Repetend r2 = repetend_compute(2, 7, 10);
        ASSERT_INT(r2.cycle_len, r1.cycle_len, "2/7 same cycle length as 1/7");
        /* 2/7 = 0.(285714) which is rotation of 142857 */
        int expected[] = {2, 8, 5, 7, 1, 4};
        int ok = 1;
        for (int i = 0; i < 6; i++)
            if (r2.digits[r2.cycle_start + i] != expected[i]) ok = 0;
        ASSERT(ok, "2/7 digits = 285714");
        repetend_free(&r1);
        repetend_free(&r2);
    }

    /* base 2: 1/3 = 0.(01) */
    {
        Repetend r = repetend_compute(1, 3, 2);
        ASSERT_INT(r.cycle_len, 2, "1/3 base 2 cycle length = 2");
        ASSERT_INT(r.digits[r.cycle_start], 0, "1/3 base 2 first digit = 0");
        ASSERT_INT(r.digits[r.cycle_start + 1], 1, "1/3 base 2 second digit = 1");
        repetend_free(&r);
    }

    /* edge: k=0 */
    {
        Repetend r = repetend_compute(0, 7, 10);
        ASSERT_INT(r.cycle_len, 0, "0/7 terminates");
        ASSERT_INT(r.len, 0, "0/7 has 0 digits");
        repetend_free(&r);
    }

    printf("\n");
}

/* ── field tests ────────────────────────────────────────── */

static void test_field(void)
{
    printf("field_build:\n");

    /* field of 7: all 6 fractions are rotations */
    {
        Field f = field_build(7, 10);
        ASSERT_INT(f.num_rows, 6, "field(7) has 6 rows");
        ASSERT_INT(f.base_rep.cycle_len, 6, "field(7) base cycle = 6");

        /* k=1 should have rot_index=0, alignment=1.0 */
        ASSERT_INT(f.rows[0].rot_index, 0, "1/7 rot_index = 0");
        ASSERT_DBL(f.rows[0].alignment, 1.0, 1e-10, "1/7 alignment = 1.0");

        /* all rows should have valid rotation indices */
        int all_valid = 1;
        for (int i = 0; i < 6; i++)
            if (f.rows[i].rot_index < 0) all_valid = 0;
        ASSERT(all_valid, "all 6 fractions are rotations of 1/7");

        field_free(&f);
    }

    /* field of 4: all terminate */
    {
        Field f = field_build(4, 10);
        ASSERT_INT(f.num_rows, 3, "field(4) has 3 rows");
        int all_term = 1;
        for (int i = 0; i < 3; i++)
            if (f.rows[i].rep.cycle_len != 0) all_term = 0;
        ASSERT(all_term, "all fractions of 4 terminate");
        field_free(&f);
    }

    /* field of 12: mix of terminating and repeating */
    {
        Field f = field_build(12, 10);
        ASSERT_INT(f.num_rows, 11, "field(12) has 11 rows");
        int n_term = 0, n_rep = 0;
        for (int i = 0; i < 11; i++) {
            if (f.rows[i].rep.cycle_len == 0) n_term++;
            else n_rep++;
        }
        ASSERT(n_term > 0, "field(12) has terminating fractions");
        ASSERT(n_rep > 0, "field(12) has repeating fractions");
        field_free(&f);
    }

    printf("\n");
}

/* ── alignment tests ────────────────────────────────────── */

static void test_alignment(void)
{
    printf("alignment:\n");

    /* alignment_formula: (2m-1)/(pm-1) */
    ASSERT_DBL(alignment_formula(1, 3), 1.0 / 2.0, 1e-10,
               "formula(1,3) = 0.5");
    ASSERT_DBL(alignment_formula(4, 3), 7.0 / 11.0, 1e-10,
               "formula(4,3) = 7/11");
    ASSERT_DBL(alignment_formula(10, 3), 19.0 / 29.0, 1e-10,
               "formula(10,3) = 19/29");

    /* alignment_exact for DP primes matches formula */
    {
        int dp_primes[] = {3, 7, 11};
        int smooth_m[] = {4, 5, 8, 10};
        for (int pi = 0; pi < 3; pi++) {
            int p = dp_primes[pi];
            for (int mi = 0; mi < 4; mi++) {
                int m = smooth_m[mi];
                int n = p * m;
                double exact = alignment_exact(n, 10);
                double formula = alignment_formula(m, p);
                char msg[64];
                snprintf(msg, sizeof(msg), "exact(%d) = formula(%d,%d)", n, m, p);
                ASSERT_DBL(exact, formula, 1e-10, msg);
            }
        }
    }

    /* alignment of prime p is 1/L where L = ord_p(10) */
    {
        double a7 = alignment_exact(7, 10);
        /* 1/7 matches only itself at rot=0, so alignment = 1/6 * (1 + 0*5) ...
           actually for prime p, alignment = 1/(p-1) * sum of row alignments.
           For p=7 all rows are rotations with 0 matches except self. */
        ASSERT(a7 > 0.0 && a7 < 1.0, "alignment(7) between 0 and 1");
    }

    /* smooth numbers have alignment 1.0 */
    ASSERT_DBL(alignment_exact(2, 10), 1.0, 1e-10, "alignment(2) = 1.0");
    ASSERT_DBL(alignment_exact(5, 10), 1.0, 1e-10, "alignment(5) = 1.0");
    ASSERT_DBL(alignment_exact(8, 10), 1.0, 1e-10, "alignment(8) = 1.0");
    ASSERT_DBL(alignment_exact(10, 10), 1.0, 1e-10, "alignment(10) = 1.0");

    /* Alignment uses one common long-division clock, not per-row phase reset. */
    {
        Field f = field_build(6, 2);
        ASSERT_DBL(f.rows[0].alignment, 1.0, 1e-10,
                   "1/6 matches itself at common depth");
        ASSERT_DBL(f.rows[1].alignment, 0.0, 1e-10,
                   "1/3 does not match 1/6 at common depth");
        ASSERT_DBL(f.rows[2].alignment, 1.0, 1e-10,
                   "terminating 1/2 is aligned by convention");
        ASSERT_DBL(f.rows[3].alignment, 1.0, 1e-10,
                   "2/3 matches 1/6 at common depth");
        ASSERT_DBL(f.rows[4].alignment, 0.0, 1e-10,
                   "5/6 does not match 1/6 at common depth");
        ASSERT_DBL(alignment_exact(6, 2), 3.0 / 5.0, 1e-10,
                   "synchronized alignment(6, base=2) = 3/5");
        field_free(&f);
    }

    printf("\n");
}

/* ── sigma (pairwise alignment) tests ───────────────────── */

static void test_sigma(void)
{
    printf("sigma_exact:\n");

    ASSERT(isnan(sigma_exact(2, 10)),
           "sigma(2) is undefined because no distinct unordered pair exists");

    /* sigma(p) = 0 for DP primes */
    ASSERT_DBL(sigma_exact(3, 10), 0.0, 1e-10, "sigma(3) = 0");
    ASSERT_DBL(sigma_exact(7, 10), 0.0, 1e-10, "sigma(7) = 0");
    ASSERT_DBL(sigma_exact(11, 10), 0.0, 1e-10, "sigma(11) = 0");

    /* sigma(p) > 0 for non-DP primes */
    ASSERT(sigma_exact(13, 10) > 1e-10, "sigma(13) > 0");
    ASSERT(sigma_exact(17, 10) > 1e-10, "sigma(17) > 0");

    /* Sigma is a probability. No general composite-rough-part sign claim
       is made for the signed residual F=alpha-sigma. */
    {
        int test_n[] = {6, 12, 14, 21, 33};
        for (int i = 0; i < 5; i++) {
            int n = test_n[i];
            double s = sigma_exact(n, 10);
            char msg[64];
            snprintf(msg, sizeof(msg), "sigma(%d) is in [0,1]", n);
            ASSERT(s >= 0.0 && s <= 1.0, msg);
        }
    }

    printf("\n");
}

/* ── invariants tests ───────────────────────────────────── */

static void test_invariants(void)
{
    printf("invariants_compute:\n");

    /* basic sanity */
    {
        Invariants inv = invariants_compute(7, 10);
        ASSERT_INT(inv.n, 7, "inv.n = 7");
        ASSERT_INT(inv.base, 10, "inv.base = 10");
        ASSERT_INT(inv.cycle_length, 6, "inv.cycle_length = 6");
        ASSERT(inv.curvature > 0.0, "curvature > 0 for n=7");
        ASSERT(inv.coherence >= 0.0 && inv.coherence <= 1.0,
               "coherence in [0,1]");
        ASSERT(inv.alignment > 0.0, "alignment > 0 for n=7");
    }

    /* harmonicity: L%3==0 => H3=1 */
    {
        Invariants inv7 = invariants_compute(7, 10);
        ASSERT_INT(inv7.harmonicity, 1, "H3(7) = 1 (L=6, 6%3=0)");

        Invariants inv17 = invariants_compute(17, 10);
        /* ord_17(10) = 16, 16%3 != 0 */
        ASSERT_INT(inv17.harmonicity, 0, "H3(17) = 0 (L=16)");
    }

    /* smooth: cycle_length = 0 or alignment = 1 */
    {
        Invariants inv = invariants_compute(8, 10);
        ASSERT_DBL(inv.alignment, 1.0, 1e-10, "alignment(8) = 1.0");
    }

    printf("\n");
}

/* ── bin computation tests ──────────────────────────────── */

static void test_bins(void)
{
    printf("bin computation:\n");

    /* bin-sum formula: S(p,b) = bQ^2 + R(2Q+1) */
    {
        int primes[] = {7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47};
        int np = 11;
        int b = 10;

        for (int i = 0; i < np; i++) {
            int p = primes[i];
            int bins[64] = {0};
            for (int r = 1; r < p; r++)
                bins[(b * r) / p]++;

            int S_actual = 0;
            for (int d = 0; d < b; d++)
                S_actual += bins[d] * bins[d];

            int Q = (p - 1) / b;
            int R = (p - 1) % b;
            int S_formula = b * Q * Q + R * (2 * Q + 1);

            char msg[64];
            snprintf(msg, sizeof(msg), "S(%d,10) = %d", p, S_formula);
            ASSERT_INT(S_actual, S_formula, msg);
        }
    }

    /* bin sizes: R bins of size Q+1, b-R bins of size Q */
    {
        int p = 29, b = 10;
        int Q = (p - 1) / b;
        int R = (p - 1) % b;
        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;

        int n_large = 0, n_small = 0;
        for (int d = 0; d < b; d++) {
            if (bins[d] == Q + 1) n_large++;
            else if (bins[d] == Q) n_small++;
        }
        ASSERT_INT(n_large, R, "p=29: R large bins");
        ASSERT_INT(n_small, b - R, "p=29: b-R small bins");
    }

    printf("\n");
}

/* ── multiplicative order tests ─────────────────────────── */

static void test_mult_order(void)
{
    printf("multiplicative order:\n");

    /* compute order via repetend cycle length */
    int cases[][3] = {
        /* {base, n, expected_order} */
        {10,  7,  6},
        {10, 13,  6},
        {10, 17, 16},
        {10, 19, 18},
        {10, 23, 22},
        {10, 29, 28},
        {10, 41,  5},
        { 2,  7,  3},
        { 2, 31,  5},
    };
    int nc = 9;

    for (int i = 0; i < nc; i++) {
        int base = cases[i][0];
        int n = cases[i][1];
        int expected = cases[i][2];

        Repetend r = repetend_compute(1, n, base);
        char msg[64];
        snprintf(msg, sizeof(msg), "ord_%d(%d) = %d", n, base, expected);
        ASSERT_INT(r.cycle_len, expected, msg);
        repetend_free(&r);
    }

    printf("\n");
}

/* ── golden ratio threshold tests ───────────────────────── */

static void test_golden_threshold(void)
{
    printf("golden threshold:\n");

    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    /* tier 1: smooth numbers have alignment 1.0 */
    ASSERT(alignment_exact(16, 10) >= tau, "16 is tier 1/2");
    ASSERT(alignment_exact(25, 10) >= tau, "25 is tier 1/2");

    /* tier 2: 3m with smooth m >= 4 */
    ASSERT(alignment_exact(12, 10) >= tau, "12 = 3*4 is tier 2");
    ASSERT(alignment_exact(15, 10) >= tau, "15 = 3*5 is tier 2");
    ASSERT(alignment_exact(24, 10) >= tau, "24 = 3*8 is tier 2");

    /* tier 3: rough part >= 7 */
    ASSERT(alignment_exact(7, 10) < tau, "7 is tier 3");
    ASSERT(alignment_exact(14, 10) < tau, "14 is tier 3");
    ASSERT(alignment_exact(13, 10) < tau, "13 is tier 3");
    ASSERT(alignment_exact(17, 10) < tau, "17 is tier 3");

    /* boundary: n=3 (alpha=0.5) and n=6 (alpha=0.6) are below 1/phi */
    ASSERT(alignment_exact(3, 10) < tau, "3 is below 1/phi");
    ASSERT(alignment_exact(6, 10) < tau, "6 is below 1/phi");

    /* Exact Three-Tier endpoints and composite rough-part coverage. */
    ASSERT_DBL(alignment_exact(6, 10), 3.0 / 5.0, 1e-12,
               "Three-Tier lower endpoint alpha_10(6) = 3/5");
    ASSERT_DBL(alignment_exact(12, 10), 7.0 / 11.0, 1e-12,
               "Three-Tier upper endpoint alpha_10(12) = 7/11");
    ASSERT(alignment_exact(9, 10) <= 4.0 / 7.0,
           "composite rough part 9 stays below decimal ceiling");
    ASSERT(alignment_exact(21, 10) <= 4.0 / 7.0,
           "composite rough part 21 stays below decimal ceiling");
    ASSERT(alignment_exact(27, 10) <= 4.0 / 7.0,
           "composite rough part 27 stays below decimal ceiling");
    ASSERT_DBL(alignment_exact(6, 3), 1.0, 1e-12,
               "odd-base two-core family alpha_3(6) = 1");

    printf("\n");
}

/* ── reciprocal-square selection object tests ───────────── */

static void test_reciprocal_square_selection(void)
{
    printf("reciprocal-square threshold selection:\n");

    long long numerator = 0;
    long long denominator = 0;
    long long certificate = 0;
    int remainder = 0;

    ASSERT(reciprocal_square_selection_alignment_fraction(
               3, 4, &numerator, &denominator)
           && numerator == 7 && denominator == 11,
           "p=3, m=4 gives exact alignment 7/11");
    ASSERT(reciprocal_square_selection_threshold_sign(3, 4, &certificate)
           && certificate == 5,
           "7/11 has positive exact reciprocal-golden certificate");
    ASSERT(reciprocal_square_selection_threshold_sign(3, 2, &certificate)
           && certificate == -1,
           "3/5 has negative exact reciprocal-golden certificate");
    ASSERT(reciprocal_square_selection_threshold_sign(5, 100, &certificate)
           && certificate == -110099,
           "p=5 stays below the reciprocal-golden threshold");
    ASSERT(reciprocal_square_selection_cubic_remainder(3, &remainder)
           && remainder == 0,
           "golden minimal polynomial divides the cubic at p=3");
    ASSERT(reciprocal_square_selection_cubic_remainder(5, &remainder)
           && remainder == -2,
           "golden minimal-polynomial remainder at p=5 is -2x");
    ASSERT(!reciprocal_square_selection_alignment_fraction(
               9, 4, &numerator, &denominator),
           "alignment object rejects a composite prime parameter");
    ASSERT(!reciprocal_square_selection_threshold_sign(
               3, 0, &certificate),
           "threshold object rejects a nonpositive resolution");

    printf("\n");
}

/* ── base independence tests ────────────────────────────── */

static void test_bases(void)
{
    printf("multi-base:\n");

    /* alignment formula works in other bases */
    int bases[] = {4, 12, 16};
    for (int bi = 0; bi < 3; bi++) {
        int base = bases[bi];
        /* p=3 is DP in all bases where 3 doesn't divide base */
        if (base % 3 == 0) continue;
        int n = 3 * 4;  /* m=4 is smooth in any base */
        double exact = alignment_exact(n, base);
        double formula = alignment_formula(4, 3);
        char msg[64];
        snprintf(msg, sizeof(msg), "align(12, base=%d) = formula(4,3)", base);
        ASSERT_DBL(exact, formula, 1e-10, msg);
    }

    /* repetend of 1/7 in base 7 terminates (7 divides base) */
    {
        Repetend r = repetend_compute(1, 7, 7);
        /* 1/7 in base 7 = 0.1 exactly */
        ASSERT_INT(r.cycle_len, 0, "1/7 in base 7 terminates");
        repetend_free(&r);
    }

    /* Base support is not limited to a hard-coded list of small primes. */
    ASSERT(is_b_smooth(37 * 37, 37), "37^2 is supported in base 37");
    ASSERT(is_b_smooth(37 * 41, 37 * 41),
           "37*41 is supported in base 1517");
    ASSERT(!is_b_smooth(43, 37), "43 is not supported in base 37");

    printf("\n");
}

/* ── cumulative polarity tests ──────────────────────────── */

static void cumulative_polarity(const int *digits, int len, int *out)
{
    int running = 0;
    for (int i = 0; i < len; i++) {
        running += digits[i];
        int cp = running % 9;
        if (cp == 0) cp = 9;
        out[i] = cp;
    }
}

static void test_polar(void)
{
    printf("cumulative polarity:\n");

    /* 1/7 = 0.(142857) -> cumulative sums: 1,5,7,15,20,27
       mod 9 (with 0->9): 1, 5, 7, 6, 2, 9 */
    {
        Repetend r = repetend_compute(1, 7, 10);
        const int *c = r.digits + r.cycle_start;
        int cp[6];
        cumulative_polarity(c, 6, cp);
        int expected[] = {1, 5, 7, 6, 2, 9};
        int ok = 1;
        for (int i = 0; i < 6; i++)
            if (cp[i] != expected[i]) ok = 0;
        ASSERT(ok, "1/7 polar = 1 5 7 6 2 9");
        repetend_free(&r);
    }

    /* all closed fractions of a prime end with 9 */
    {
        int primes[] = {7, 13, 17, 19, 29};
        for (int pi = 0; pi < 5; pi++) {
            int p = primes[pi];
            Field f = field_build(p, 10);
            int all_nine = 1;
            for (int i = 0; i < f.num_rows; i++) {
                const Row *row = &f.rows[i];
                if (row->rep.cycle_len == 0) continue;
                const int *c = row->rep.digits + row->rep.cycle_start;
                int L = row->rep.cycle_len;
                int cp[1024];
                cumulative_polarity(c, L, cp);
                if (cp[L - 1] != 9) all_nine = 0;
            }
            char msg[64];
            snprintf(msg, sizeof(msg), "all closed fractions of %d end polar=9", p);
            ASSERT(all_nine, msg);
            field_free(&f);
        }
    }

    /* open fractions: 1/4 = 0.25, digits 2,5, polar: 2, 7 */
    {
        Repetend r = repetend_compute(1, 4, 10);
        int cp[2];
        cumulative_polarity(r.digits, r.len, cp);
        ASSERT_INT(cp[0], 2, "1/4 polar[0] = 2");
        ASSERT_INT(cp[1], 7, "1/4 polar[1] = 7");
        repetend_free(&r);
    }

    /* open fractions: 3/4 = 0.75, digits 7,5, polar: 7, 3 */
    {
        Repetend r = repetend_compute(3, 4, 10);
        int cp[2];
        cumulative_polarity(r.digits, r.len, cp);
        ASSERT_INT(cp[0], 7, "3/4 polar[0] = 7");
        ASSERT_INT(cp[1], 3, "3/4 polar[1] = 3");
        repetend_free(&r);
    }

    /* open/closed classification */
    {
        Field f = field_build(12, 10);
        int n_open = 0, n_closed = 0;
        for (int i = 0; i < f.num_rows; i++) {
            if (f.rows[i].rep.cycle_len == 0) n_open++;
            else n_closed++;
        }
        ASSERT_INT(n_open, 3, "field(12) has 3 open fractions");
        ASSERT_INT(n_closed, 8, "field(12) has 8 closed fractions");
        field_free(&f);
    }

    /* digit sum of one full cycle is always 0 mod 9 (hence polar ends at 9) */
    {
        Repetend r = repetend_compute(1, 29, 10);
        const int *c = r.digits + r.cycle_start;
        int sum = 0;
        for (int i = 0; i < r.cycle_len; i++)
            sum += c[i];
        ASSERT_INT(sum % 9, 0, "1/29 cycle digit sum = 0 mod 9");
        repetend_free(&r);
    }

    printf("\n");
}

/* -- Digit-function structural tests ------------ */

static int gcd_test(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

static int modinv_test(int a, int m) {
    int g = m, x = 0, y = 1, a0 = a;
    while (a0) { int q = g/a0; int t = g-q*a0; g=a0; a0=t; t=x-q*y; x=y; y=t; }
    return ((x % m) + m) % m;
}

static int is_prime_test(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int d = 5; d * d <= n; d += 6)
        if (n % d == 0 || n % (d + 2) == 0) return 0;
    return 1;
}

static int collision_count_test(int p, int base)
{
    int C = 0;
    int g = base % p;
    for (int r = 1; r < p; r++) {
        int gr = (int)(((long long)g * r) % p);
        if ((base * r) / p == (base * gr) / p) C++;
    }
    return C;
}

static int collision_S_for_prime_test(int p, int base)
{
    return collision_count_test(p, base) - (p - 1) / base;
}

static void build_collision_table_test(int base, int *S, int *seen)
{
    int m = base * base;
    for (int i = 0; i < m; i++) {
        S[i] = 0;
        seen[i] = 0;
    }

    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_test(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        S[cls] = collision_S_for_prime_test(p, base);
        seen[cls] = 1;
    }
}

static void test_collision_theorems(void)
{
    printf("collision table theorem fixtures:\n");

    /* Base-10 collision periodic table from the public paper/post. */
    {
        int S[100], seen[100];
        int expected[100];
        for (int i = 0; i < 100; i++) expected[i] = 9999;
        expected[1] = 0;   expected[3] = 2;   expected[7] = 0;   expected[9] = 8;
        expected[11] = -1; expected[13] = -1; expected[17] = 1;  expected[19] = -1;
        expected[21] = 0;  expected[23] = -2; expected[27] = 6;  expected[29] = 0;
        expected[31] = -1; expected[33] = -1; expected[37] = -3; expected[39] = -1;
        expected[41] = -4; expected[43] = 0;  expected[47] = -2; expected[49] = 0;
        expected[51] = -1; expected[53] = 1;  expected[57] = -1; expected[59] = 3;
        expected[61] = 0;  expected[63] = 2;  expected[67] = 0;  expected[69] = 0;
        expected[71] = -1; expected[73] = -7; expected[77] = 1;  expected[79] = -1;
        expected[81] = 0;  expected[83] = -2; expected[87] = 0;  expected[89] = 0;
        expected[91] = -9; expected[93] = -1; expected[97] = -3; expected[99] = -1;

        build_collision_table_test(10, S, seen);
        int ok = 1;
        for (int a = 1; a < 100; a++) {
            if (gcd_test(a, 100) != 1) continue;
            if (!seen[a] || S[a] != expected[a]) ok = 0;
        }
        ASSERT(ok, "base-10 entries match the lag-one collision table");
    }

    /* Reflection identity and mean theorem across the public bases. */
    {
        int bases[] = {3, 5, 7, 10};
        for (int bi = 0; bi < 4; bi++) {
            int base = bases[bi];
            int m = base * base;
            int S[10000], seen[10000];
            build_collision_table_test(base, S, seen);

            int reflection_ok = 1;
            int sum = 0, count = 0;
            for (int a = 1; a < m; a++) {
                if (gcd_test(a, m) != 1) continue;
                if (!seen[a] || !seen[m - a] || S[a] + S[m - a] != -1)
                    reflection_ok = 0;
                sum += S[a];
                count++;
            }

            char msg[96];
            snprintf(msg, sizeof(msg), "base %d reflection S(a)+S(m-a)=-1", base);
            ASSERT(reflection_ok, msg);
            snprintf(msg, sizeof(msg), "base %d mean is exactly -1/2", base);
            ASSERT_INT(2 * sum, -count, msg);
        }
    }

    /* Finite determination: S(p) depends only on p mod b^2. */
    {
        int bases[] = {3, 5, 7, 10};
        for (int bi = 0; bi < 4; bi++) {
            int base = bases[bi];
            int m = base * base;
            int S_by_class[10000], seen[10000];
            for (int i = 0; i < m; i++) {
                S_by_class[i] = 0;
                seen[i] = 0;
            }

            int ok = 1;
            for (int p = m + 1; p <= 5000; p++) {
                if (!is_prime_test(p) || p % base == 0) continue;
                int cls = p % m;
                int S = collision_S_for_prime_test(p, base);
                if (seen[cls] && S_by_class[cls] != S) {
                    ok = 0;
                    break;
                }
                S_by_class[cls] = S;
                seen[cls] = 1;
            }

            char msg[96];
            snprintf(msg, sizeof(msg), "base %d finite determination through p<=5000", base);
            ASSERT(ok, msg);
        }
    }

    /* Neutrality theorem fixture: base 10, mod-3 class 2 has mean -1/2. */
    {
        int S[100], seen[100];
        build_collision_table_test(10, S, seen);
        int sums[3] = {0, 0, 0};
        int counts[3] = {0, 0, 0};
        for (int a = 1; a < 100; a++) {
            if (gcd_test(a, 100) != 1 || !seen[a]) continue;
            sums[a % 3] += S[a];
            counts[a % 3]++;
        }
        ASSERT_INT(2 * sums[2], -counts[2], "mod-3 class 2 mean is -1/2");
        ASSERT_INT(sums[0] + sums[1], -counts[0], "mod-3 reflected classes 0 and 1 sum to -1 per pair");
    }

    printf("\n");
}

static int mult_order_test(int base, int p)
{
    int r = 1;
    for (int L = 1; L <= p - 1; L++) {
        r = (r * base) % p;
        if (r == 1) return L;
    }
    return 0;
}

static double spectral_power_test(int p, int base, int k)
{
    const double pi = acos(-1.0);
    int bins[256] = {0};
    for (int r = 1; r < p; r++)
        bins[(base * r) / p]++;

    double phi = 0.0;
    if (k == 0) {
        for (int d = 0; d < base; d++)
            phi += (double)bins[d] * bins[d];
        return phi;
    }

    for (int d = 0; d < base; d++) {
        int n = bins[d];
        if (!n) continue;
        double num = sin(pi * k * n / (double)p);
        double den = sin(pi * k / (double)p);
        phi += (num / den) * (num / den);
    }
    return phi;
}

static int autocorrelation_direct_test(int p, int base, int ell)
{
    int g = 1;
    for (int i = 0; i < ell; i++)
        g = (g * base) % p;

    int R = 0;
    for (int r = 1; r < p; r++) {
        int gr = (int)(((long long)g * r) % p);
        if ((base * r) / p == (base * gr) / p) R++;
    }
    return R;
}

static int autocorrelation_repetend_test(int p, int base, int ell)
{
    int L = mult_order_test(base, p);
    int rep[512];
    int r = 1;
    for (int j = 0; j < L; j++) {
        rep[j] = (base * r) / p;
        r = (r * base) % p;
    }

    int R = 0;
    for (int j = 0; j < L; j++)
        if (rep[j] == rep[(j + ell) % L]) R++;
    return R;
}

static void test_spectral_autocorrelation_theorems(void)
{
    printf("spectral/autocorrelation theorem fixtures:\n");
    const double pi = acos(-1.0);

    /* Spectral-power paper: p=13 worked example. */
    {
        ASSERT_DBL(spectral_power_test(13, 10, 0), 16.0, 1e-10,
                   "Phi_13(0) = 16");
        for (int k = 1; k < 13; k++) {
            double expected = 8.0 + 8.0 * pow(cos(pi * k / 13.0), 2.0);
            char msg[64];
            snprintf(msg, sizeof(msg), "Phi_13(%d) worked-example formula", k);
            ASSERT_DBL(spectral_power_test(13, 10, k), expected, 1e-10, msg);
        }
    }

    /* Digit-partitioning primes have flat spectral power. */
    {
        for (int k = 0; k < 11; k++)
            ASSERT_DBL(spectral_power_test(11, 10, k), 10.0, 1e-10,
                       "p=11 spectral power is constant");
    }

    /* Parseval: sum_k Phi(k) = p(p-1). */
    {
        int primes[] = {11, 13, 29};
        for (int pi = 0; pi < 3; pi++) {
            int p = primes[pi];
            double total = 0.0;
            for (int k = 0; k < p; k++)
                total += spectral_power_test(p, 10, k);
            char msg[64];
            snprintf(msg, sizeof(msg), "Parseval spectral total for p=%d", p);
            ASSERT_DBL(total, (double)p * (p - 1), 1e-8, msg);
        }
    }

    /* Primitive-root cases: orbit autocorrelation equals direct digit-bin counting. */
    {
        int primes[] = {7, 29};
        for (int pi = 0; pi < 2; pi++) {
            int p = primes[pi];
            int L = mult_order_test(10, p);
            int ok = 1;
            for (int ell = 0; ell < L; ell++) {
                int direct = autocorrelation_direct_test(p, 10, ell);
                int repetend = autocorrelation_repetend_test(p, 10, ell);
                if (direct != repetend) ok = 0;
            }
            char msg[80];
            snprintf(msg, sizeof(msg), "autocorrelation direct formula for p=%d", p);
            ASSERT(ok, msg);
        }
    }

    /* Multi-orbit example from the public post: direct all-residue counts. */
    {
        int expected[] = {40, 0, 6, 6, 0};
        int ok = 1;
        for (int ell = 0; ell < 5; ell++)
            if (autocorrelation_direct_test(41, 10, ell) != expected[ell]) ok = 0;
        ASSERT(ok, "autocorrelation direct counts for p=41");
    }

    printf("\n");
}

static void test_digit_function_structure(void)
{
    printf("Digit-function structural identities:\n\n");


    int b = 3;

    /* Test palindrome at m=27 */
    {
        int m = 27;
        int ok = 1;
        for (int a = 1; a < m; a++) {
            if (a % b == 0) continue;
            for (int n = 1; n < m - 1; n++) {
                int tn = m - 1 - n;
                int dn = (int)(((long long)(n+1)*a)/m - ((long long)n*a)/m);
                int dtn = (int)(((long long)(tn+1)*a)/m - ((long long)tn*a)/m);
                if (dn != dtn) { ok = 0; break; }
            }
            if (!ok) break;
        }
        ASSERT(ok, "palindrome d_{m-1-n}(a) = d_n(a) at m=27");
    }

    /* Test f_full = 1 at m=27 */
    {
        int m = 27;
        int ok = 1;
        for (int a = 1; a < m; a++) {
            if (a % b == 0) continue;
            int N0 = 0, N2 = 0;
            for (int n = 0; n < m; n++) {
                int dn = (int)(((long long)(n+1)*a)/m - ((long long)n*a)/m);
                if (!dn) continue;
                if (n % 3 == 0) N0++;
                if (n % 3 == 2) N2++;
            }
            if (N2 - N0 != 1) { ok = 0; break; }
        }
        ASSERT(ok, "f_full(a) = 1 at m=27");
    }

    /* Test middle balance at m=27 */
    {
        int m = 27, bl = 9;
        int ok = 1;
        for (int a = 1; a < m; a++) {
            if (a % b == 0) continue;
            int N0 = 0, N2 = 0;
            for (int n = bl; n < 2*bl; n++) {
                int dn = (int)(((long long)(n+1)*a)/m - ((long long)n*a)/m);
                if (!dn) continue;
                if (n % 3 == 0) N0++;
                if (n % 3 == 2) N2++;
            }
            if (N2 - N0 != 0) { ok = 0; break; }
        }
        ASSERT(ok, "f^{B_1}(a) = 0 at m=27");
    }

    /* Test inversion invariance at m=27 */
    {
        int m = 27, bl = 9;
        int ok = 1;
        for (int a = 1; a < m; a++) {
            if (a % b == 0) continue;
            int ainv = modinv_test(a, m);
            if (ainv % b == 0) continue;
            for (int j = 0; j < 2; j++) {
                int N0a=0, N2a=0, N0i=0, N2i=0;
                for (int n = 0; n < bl; n++) {
                    int dj = n;
                    for (int jj = 0; jj < j; jj++) dj /= b;
                    dj %= b;
                    int dna = (int)(((long long)(n+1)*a)/m - ((long long)n*a)/m);
                    int dni = (int)(((long long)(n+1)*ainv)/m - ((long long)n*ainv)/m);
                    if (dj==0) { N0a+=dna; N0i+=dni; }
                    if (dj==2) { N2a+=dna; N2i+=dni; }
                }
                if ((N2a-N0a) != (N2i-N0i)) { ok = 0; break; }
            }
            if (!ok) break;
        }
        ASSERT(ok, "f_j(a) = f_j(a^{-1}) at m=27");
    }

    printf("\n");
}

/* ── Alignment-deficit lattice ─────────────────── */

static void test_deficit_lattice(void)
{
    printf("alignment-deficit lattice:\n");

    ASSERT(deficit_lattice_is_supported(24, 30),
           "24 is {2,3,5}-supported");
    ASSERT(deficit_lattice_is_supported(45, 30),
           "45 is {2,3,5}-supported");
    ASSERT(!deficit_lattice_is_supported(7, 30),
           "7 is not {2,3,5}-supported");
    ASSERT(deficit_lattice_is_supported(531441, 12),
           "3^12 is {2,3}-supported");

    {
        long long num = 0, den = 0;
        ASSERT(deficit_lattice_alignment_fraction(29, 24, &num, &den),
               "alignment fraction accepts p=29,m=24");
        ASSERT(num == 47 && den == 695,
               "alpha_30(696) = 47/695");
    }

    {
        long long num = 0, den = 0;
        ASSERT(deficit_lattice_deficit_fraction(29, 24, &num, &den),
               "deficit fraction accepts p=29,m=24");
        ASSERT(num == 27 && den == 20155,
               "delta_29(24) = 27/20155");
        ASSERT(2 * 695 - 29 * 47 == 27,
               "deficit numerator identity is exact");
    }

    {
        long long num = 0, den = 0;
        ASSERT(deficit_lattice_ratio_fraction(29, 24, 36, &num, &den),
               "deficit ratio accepts major-scale fifth");
        ASSERT(num == 1043 && den == 695,
               "delta_29(24)/delta_29(36) = 1043/695");
        ASSERT(num * 2 - den * 3 == 1,
               "finite fifth differs from 3/2 by 1/(2*695)");
    }

    {
        long long num = 0, den = 0;
        ASSERT(deficit_lattice_ratio_fraction(11, 524288, 531441,
                                              &num, &den),
               "Pythagorean comma ratio is in range");
        ASSERT(num == 5845850 && den == 5767167,
               "paper's Pythagorean comma fixture is exact");
        ASSERT(num * 524288LL - den * 531441LL == 7153,
               "comma cross-product residual equals 3^12-2^19");
    }

    {
        int major[] = {24, 27, 30, 32, 36, 40, 45, 48};
        int all_supported = 1, all_bounded = 1;
        for (int i = 0; i < 8; i++) {
            long long num = 0, den = 0;
            if (!deficit_lattice_is_supported(major[i], 30)
                || !deficit_lattice_ratio_fraction(29, 24, major[i],
                                                   &num, &den)) {
                all_supported = 0;
                break;
            }
            long long error_num = llabs(major[i] - 24);
            long long error_den = (long long)major[i] * den;
            if (error_num * 12500 >= 9 * error_den)
                all_bounded = 0;
        }
        ASSERT(all_supported, "all just-major-scale points are supported");
        ASSERT(all_bounded, "major-scale relative errors are below 7.2e-4");
    }

    ASSERT(!deficit_lattice_alignment_fraction(2, 24, NULL, NULL),
           "invalid deficit-lattice fraction request is rejected");
    printf("\n");
}

/* ── Synchronized coherence decomposition ──────── */

static void test_coherence_decomposition(void)
{
    printf("synchronized coherence decomposition:\n");

    long long an, ad, sn, sd, fn, fd;
    ASSERT(coherence_decomposition_fractions(12, 10, -1,
                                             &an, &ad, &sn, &sd, &fn, &fd),
           "Coherence-decomposition exact builder accepts n=12");
    ASSERT(an == 7 && ad == 11, "alpha_10(12) = 7/11");
    ASSERT(sn == 3 && sd == 11, "sigma_10(12) = 3/11");
    ASSERT(fn == 4 && fd == 11, "F_10(12) = 4/11");

    {
        long long an2, ad2, sn2, sd2, fn2, fd2;
        ASSERT(coherence_decomposition_fractions(12, 10, 3,
                                                  &an2, &ad2, &sn2, &sd2,
                                                  &fn2, &fd2),
               "Coherence-decomposition builder accepts a later clearing depth");
        ASSERT(an == an2 && ad == ad2 && sn == sn2 && sd == sd2
               && fn == fn2 && fd == fd2,
               "alpha, sigma, and F are independent of clearing depth");
    }

    ASSERT(coherence_decomposition_fractions(7, 10, -1,
                                             &an, &ad, &sn, &sd, &fn, &fd),
           "Coherence-decomposition exact builder accepts prime core p=7");
    ASSERT(an == 1 && ad == 6 && sn == 0 && sd == 1
           && fn == 1 && fd == 6,
           "p=7,s=1 has alpha=F=1/6 and sigma=0");

    ASSERT(coherence_decomposition_fractions(13, 10, -1,
                                             &an, &ad, &sn, &sd, &fn, &fd),
           "Coherence-decomposition exact builder accepts non-injective p=13");
    ASSERT(sn == 1 && sd == 33, "sigma_10(13) = 1/33");

    ASSERT(coherence_decomposition_fractions(77, 10, -1,
                                             &an, &ad, &sn, &sd, &fn, &fd),
           "Coherence-decomposition exact builder accepts composite rough part 77");
    ASSERT(an == 23 && ad == 228, "alpha_10(77) = 23/228");
    ASSERT(sn == 42 && sd == 475, "sigma_10(77) = 42/475");
    ASSERT(fn == 71 && fd == 5700,
           "signed residual F_10(77) = 71/5700");
    ASSERT(an * sd * fd == fn * ad * sd + sn * ad * fd,
           "composite rough part satisfies exact alpha=F+sigma identity");

    ASSERT(coherence_decomposition_fractions(8, 10, -1,
                                             &an, &ad, &sn, &sd, &fn, &fd),
           "Coherence-decomposition exact builder accepts fully supported n=8");
    ASSERT(an == 1 && ad == 1 && sn == 1 && sd == 1
           && fn == 0 && fd == 1,
           "fully supported field has alpha=sigma=1 and F=0");
    ASSERT(!coherence_decomposition_fractions(2, 10, -1,
                                              &an, &ad, &sn, &sd, &fn, &fd),
           "Coherence-decomposition builder rejects denominator two pairwise statistic");

    printf("\n");
}

/* ── Synchronized cross-alignment matrix ───────── */

static void test_cross_alignment(void)
{
    printf("synchronized cross-alignment matrix:\n");

    long long num = 0, den = 0;
    ASSERT(cross_alignment_entry_fraction(12, 10, -1, 1, 4, &num, &den),
           "Cross-alignment matrix builder accepts n=12 entry (1,4)");
    ASSERT(num == 1 && den == 1,
           "n=12 same nonterminating residue class has entry 1");
    ASSERT(cross_alignment_entry_fraction(12, 10, -1, 1, 2, &num, &den)
           && num == 0 && den == 1,
           "n=12 different residue classes have entry 0");
    ASSERT(cross_alignment_entry_fraction(12, 10, -1, 3, 6, &num, &den)
           && num == 1 && den == 1,
           "n=12 terminating pair has entry 1");
    ASSERT(cross_alignment_entry_fraction(12, 10, 3, 1, 4, &num, &den)
           && num == 1 && den == 1,
           "matrix entry is unchanged at a later common depth");

    ASSERT(cross_alignment_entry_fraction(13, 10, -1, 1, 11, &num, &den)
           && num == 1 && den == 3,
           "A_10(13)[1,11] = 1/3");
    ASSERT(cross_alignment_entry_fraction(2, 10, -1, 1, 1, &num, &den)
           && num == 1 && den == 1,
           "A_10(2) is the 1x1 identity matrix");

    {
        long long an, ad, sn, sd, fn, fd;
        ASSERT(cross_alignment_scalar_fractions(77, 10, -1,
                                                &an, &ad, &sn, &sd,
                                                &fn, &fd),
               "Cross-alignment matrix recovers scalars for composite rough part 77");
        ASSERT(an == 23 && ad == 228,
               "matrix reference row recovers alpha_10(77) = 23/228");
        ASSERT(sn == 42 && sd == 475,
               "matrix off-diagonal mean recovers sigma_10(77) = 42/475");
        ASSERT(fn == 71 && fd == 5700,
               "matrix recovery gives F_10(77) = 71/5700");
    }

    {
        double eigenvalues[16];
        int count = 0, order = 0, cosets = 0;
        ASSERT(cross_alignment_eigenvalues(13, 10, eigenvalues, 16,
                                           &count, &order, &cosets),
               "exact p=13 matrix eigensolver succeeds");
        ASSERT(count == 12 && order == 6 && cosets == 2,
               "p=13 has dimension 12, order 6, and two cosets");
        int levels_ok = 1;
        for (int i = 0; i < 6; i++)
            if (fabs(eigenvalues[i] - 2.0 / 3.0) > 1e-9) levels_ok = 0;
        for (int i = 6; i < 12; i++)
            if (fabs(eigenvalues[i] - 4.0 / 3.0) > 1e-9) levels_ok = 0;
        ASSERT(levels_ok, "p=13 spectrum is 2/3 and 4/3, each six times");

        ASSERT(cross_alignment_eigenvalues(17, 10, eigenvalues, 16,
                                           &count, &order, &cosets),
               "exact p=17 matrix eigensolver succeeds");
        int distinct = 1;
        for (int i = 1; i < count; i++)
            if (fabs(eigenvalues[i] - eigenvalues[i - 1]) > 1e-9) distinct++;
        ASSERT(count == 16 && order == 16 && cosets == 1,
               "p=17 is the primitive-root case");
        ASSERT(distinct == 9, "p=17 has exactly nine spectral levels");
        ASSERT_DBL(eigenvalues[0], 0.25, 1e-9,
                   "p=17 minimum eigenvalue is 1/4");
        ASSERT_DBL(eigenvalues[15], 1.75, 1e-9,
                   "p=17 maximum eigenvalue is 7/4");
    }

    ASSERT(!cross_alignment_entry_fraction(12, 10, -1, 0, 1, &num, &den),
           "matrix entry builder rejects row zero");
    printf("\n");
}

static void test_spectral_structure(void)
{
    printf("Spectral structure:\n");
    int order = 0, cosets = 0, occupied = 0;
    int rank = 0, bound = 0, nullity = 0, nullity_bound = 0;

    ASSERT(spectral_structure_metrics(7, 2, &order, &cosets, &occupied,
                                      &rank, &bound, &nullity, &nullity_bound),
           "Spectral-structure base-two sharpness metrics compute");
    ASSERT(order == 3 && cosets == 2 && occupied == 2,
           "base 2, p=7 has L=3, C=2, nu=2");
    ASSERT(rank == 4 && bound == 4,
           "base 2, p=7 attains the rank bound at rank four");
    ASSERT(nullity == 2 && nullity_bound == 2,
           "base 2, p=7 attains the forced nullity bound at two");

    ASSERT(spectral_structure_metrics(13, 10, &order, &cosets, &occupied,
                                      &rank, &bound, &nullity, &nullity_bound),
           "Spectral-structure decimal p=13 metrics compute");
    ASSERT(order == 6 && cosets == 2 && occupied == 10,
           "base 10, p=13 has L=6, C=2, nu=10");
    ASSERT(rank == 12 && bound == 12 && nullity == 0,
           "base 10, p=13 is full rank within the exact bound");

    {
        int Q[16] = {0};
        int count = 0;
        ASSERT(spectral_structure_cross_equality(13, 10, Q, 16, &count),
               "decimal p=13 cross-equality count computes");
        int ok = count == 6;
        int expected[] = {0, 0, 0, 2, 0, 0};
        for (int i = 0; i < count && i < 6; i++)
            if (Q[i] != expected[i]) ok = 0;
        ASSERT(ok, "decimal p=13 has Q = 2 delta_3");

        ASSERT(spectral_structure_cross_equality(7, 4, Q, 16, &count),
               "base-four p=7 cross-equality count computes");
        ASSERT(count == 3 && Q[0] == 1 && Q[1] == 1 && Q[2] == 0,
               "base-four p=7 counterexample has Q=(1,1,0)");
    }

    ASSERT(!spectral_structure_metrics(15, 10, &order, &cosets, &occupied,
                                       &rank, &bound, &nullity, &nullity_bound),
           "Spectral-structure metrics reject a composite modulus");
    printf("\n");
}

static void test_spectral_power(void)
{
    printf("Additive digit-bin spectral power:\n");
    int sizes[16] = {0}, count = 0;
    int expected[] = {1, 1, 1, 2, 1, 1, 2, 1, 1, 1};
    ASSERT(spectral_power_bin_sizes(13, 10, sizes, 16, &count),
           "Spectral-power prime-thirteen bin sizes compute");
    ASSERT_INT(count, 10, "Spectral power has ten decimal bins");
    int sizes_ok = 1;
    for (int d = 0; d < 10; d++)
        if (sizes[d] != expected[d]) sizes_ok = 0;
    ASSERT(sizes_ok, "Spectral-power prime-thirteen bin fixture is exact");

    double power[16] = {0.0};
    ASSERT(spectral_power_values(13, 10, power, 16, &count),
           "Defining digit-function Fourier power computes");
    ASSERT_INT(count, 13, "Spectral power has thirteen frequencies");
    ASSERT_DBL(power[0], 16.0, 1e-10, "Spectral-power Phi(0) is sixteen");
    double total = 0.0;
    int formula_ok = 1;
    for (int k = 0; k < 13; k++) {
        total += power[k];
        if (k > 0) {
            double cosine = cos(3.14159265358979323846 * k / 13.0);
            if (fabs(power[k] - (8.0 + 8.0 * cosine * cosine)) > 1e-9)
                formula_ok = 0;
        }
    }
    ASSERT(formula_ok, "Spectral-power prime-thirteen cosine formula holds");
    ASSERT_DBL(total, 156.0, 1e-9, "Spectral-power Parseval fixture totals 156");

    int overlap[16] = {0};
    ASSERT(spectral_power_overlap_values(13, 10, overlap, 16, &count),
           "Additive digit-bin overlap computes");
    int overlap_sum = 0;
    for (int h = 0; h < count; h++) overlap_sum += overlap[h];
    ASSERT_INT(overlap[0], 12, "Additive overlap C_add(0) is p-1");
    ASSERT_INT(overlap_sum, 16, "Additive overlap total is Phi(0)");
    int triangular[16] = {0};
    ASSERT(spectral_power_triangular_values(13, 10, triangular, 16, &count),
           "Exact additive triangular profile computes");
    int profile_ok = 1;
    for (int h = 0; h < 13; h++)
        if (overlap[h] != triangular[h]) profile_ok = 0;
    ASSERT(profile_ok, "Direct additive overlap equals the triangular profile");

    double flat[7] = {0.0};
    ASSERT(spectral_power_values(7, 8, flat, 7, &count),
           "Spectral-power flat base-eight example computes");
    int flat_ok = 1;
    for (int k = 0; k < 7; k++)
        if (fabs(flat[k] - 6.0) > 1e-10) flat_ok = 0;
    ASSERT(flat_ok, "Base-eight prime-seven spectrum is flat at six");
    ASSERT(!spectral_power_values(15, 10, power, 16, &count),
           "Spectral power rejects a composite modulus");
    ASSERT(!spectral_power_bin_sizes(5, 10, sizes, 16, &count),
           "Digit bins reject a prime dividing the base");
    printf("\n");
}

static void test_autocorrelation_formula(void)
{
    printf("Same-bin cross-spectrum and multiplicative autocorrelation:\n");
    int count = 0;
    ASSERT(autocorrelation_collision_count(13, 10, 1, &count),
           "identity multiplier collision count computes");
    ASSERT_INT(count, 12, "C(1) equals p-1");
    ASSERT(autocorrelation_collision_count(13, 10, 10, &count),
           "nontrivial multiplier collision count computes");
    int inverse_count = 0;
    ASSERT(autocorrelation_collision_count(13, 10, 4, &inverse_count),
           "inverse multiplier collision count computes");
    ASSERT_INT(count, inverse_count, "C(a) equals C(a inverse)");

    int aggregate[8] = {0}, orbit[8] = {0}, length = 0;
    ASSERT(autocorrelation_aggregate_values(7, 10, aggregate, 8, &length),
           "primitive-root aggregate autocorrelation computes");
    ASSERT_INT(length, 6, "decimal prime seven has order six");
    ASSERT(autocorrelation_orbit_values(7, 10, 1, orbit, 8, &length),
           "primitive-root reference orbit computes");
    int seven_ok = aggregate[0] == 6 && orbit[0] == 6;
    for (int lag = 1; lag < 6; lag++)
        if (aggregate[lag] != 0 || orbit[lag] != 0) seven_ok = 0;
    ASSERT(seven_ok, "decimal prime-seven autocorrelation is 6 0 0 0 0 0");

    ASSERT(autocorrelation_aggregate_values(41, 10, aggregate, 8, &length),
           "multi-orbit aggregate autocorrelation computes");
    int expected[] = {40, 0, 6, 6, 0};
    int aggregate_ok = length == 5;
    for (int lag = 0; lag < 5; lag++)
        if (aggregate[lag] != expected[lag]) aggregate_ok = 0;
    ASSERT(aggregate_ok, "decimal prime-forty-one aggregate is 40 0 6 6 0");
    ASSERT(autocorrelation_orbit_values(41, 10, 1, orbit, 8, &length),
           "multi-orbit reference word computes independently");
    int distinction_ok = orbit[0] == 5;
    for (int lag = 1; lag < 5; lag++)
        if (orbit[lag] != 0) distinction_ok = 0;
    ASSERT(distinction_ok && orbit[2] != aggregate[2],
           "reference orbit is distinguished from aggregate line slice");

    ASSERT(!autocorrelation_collision_count(15, 10, 1, &count),
           "autocorrelation rejects a composite modulus");
    ASSERT(!autocorrelation_collision_count(5, 10, 1, &count),
           "autocorrelation rejects a prime dividing the base");
    ASSERT(!autocorrelation_collision_count(13, 10, 0, &count),
           "autocorrelation rejects the zero multiplier");
    printf("\n");
}

static void test_phase_filtered_ramanujan(void)
{
    printf("Ramanujan selector and phase-gate geometry:\n");
    int collision = 0;
    double sigma_real = 0.0, sigma_imag = 0.0, mass = 0.0, gamma = 0.0;
    ASSERT(phase_gate_components(7, 10, 1, &collision, &sigma_real,
                                 &sigma_imag, &mass, &gamma),
           "phase-gate identity multiplier components compute");
    ASSERT_INT(collision, 6, "phase-gate identity has six collisions");
    ASSERT_DBL(sigma_real, 42.0, 1e-9, "phase-gate slice equals p times C");
    ASSERT_DBL(sigma_imag, 0.0, 1e-9, "phase-gate slice is real");
    ASSERT_DBL(mass, 42.0, 1e-9, "identity phase mass is forty-two");
    ASSERT_DBL(gamma, 1.0, 1e-9, "identity phase gate is one");

    ASSERT(phase_gate_components(7, 10, 3, &collision, &sigma_real,
                                 &sigma_imag, &mass, &gamma),
           "collision-free phase-gate components compute");
    ASSERT_INT(collision, 0, "multiplier three at decimal prime seven is collision-free");
    ASSERT_DBL(gamma, 0.0, 1e-9, "collision-free multiplier closes the phase gate");

    int sizes[10] = {0}, word[10] = {0}, q = 0, remainder = 0;
    ASSERT(phase_gate_bin_word_values(43, 10, sizes, word, 10,
                                      &q, &remainder),
           "Euclidean bin word computes for decimal prime forty-three");
    ASSERT_INT(q, 4, "Euclidean bin quotient is four");
    ASSERT_INT(remainder, 3, "Euclidean bin remainder is three");
    int word_ok = 1, ones = 0;
    for (int d = 0; d < 10; d++) {
        int expected_word = d == 3 || d == 6;
        if (word[d] != expected_word || sizes[d] != 4 + expected_word)
            word_ok = 0;
        ones += word[d];
    }
    ASSERT(word_ok && ones == 2,
           "remainder-three excess word has ones exactly at digits three and six");

    long long cells = 0;
    ASSERT(phase_gate_cell_count(100, 10, &cells),
           "power-lag cell count computes");
    ASSERT(cells == 100, "base-ten lag two has one hundred matching cells");
    ASSERT(!phase_gate_components(15, 10, 1, &collision, &sigma_real,
                                  &sigma_imag, &mass, &gamma),
           "phase-gate components reject a composite modulus");
    ASSERT(!phase_gate_bin_word_values(5, 10, sizes, word, 10,
                                       &q, &remainder),
           "phase-gate bin word rejects a prime dividing the base");
    ASSERT(!phase_gate_cell_count(0, 10, &cells),
           "phase-gate cell count rejects a zero multiplier");
    printf("\n");
}

static void test_bin_derangements(void)
{
    printf("Digit-bin zero gate and constructive collision mass:\n");
    int collision = 0;
    ASSERT(bin_derangements_collision_count(13, 10, 2, &collision),
           "bin-derangement collision count computes");
    ASSERT_INT(collision, 0, "decimal prime-thirteen multiplier two is deranging");
    ASSERT(bin_derangements_collision_count(13, 10, 6, &collision),
           "constructive collision count computes");
    ASSERT_INT(collision, 2, "decimal prime-thirteen multiplier six has two collisions");

    int family[9] = {0};
    int count = 0;
    ASSERT(bin_derangements_family_values(13, 10, family, 9, &count),
           "explicit deranging family computes");
    ASSERT_INT(count, 9, "decimal gate width is b-1");
    int seen[13] = {0};
    for (int i = 0; i < count; i++) seen[family[i]]++;
    int expected[] = {2, 3, 4, 5, 7, 8, 9, 10, 12};
    int family_ok = 1;
    for (size_t i = 0; i < sizeof(expected) / sizeof(expected[0]); i++)
        if (seen[expected[i]] != 1) family_ok = 0;
    ASSERT(family_ok, "explicit family equals the decimal prime-thirteen zero set");

    long long numerator = 0;
    long long denominator = 0;
    ASSERT(bin_derangements_mean_fraction(13, 10, &numerator, &denominator),
           "constructive mean fraction computes");
    ASSERT(numerator == 4 && denominator == 2,
           "decimal prime-thirteen mean is the exact fraction four over two");
    ASSERT(!bin_derangements_collision_count(15, 10, 2, &collision),
           "bin derangements reject a composite modulus");
    ASSERT(!bin_derangements_collision_count(7, 10, 2, &collision),
           "bin derangements enforce the base-smaller-than-prime domain");
    printf("\n");
}

static void test_collision_characters(void)
{
    printf("Finite residue streams and character coordinates:\n");
    long long numerator = 0;
    long long denominator = 0;
    int collision = 0;
    int multiplier = 0;
    ASSERT(collision_characters_prime_deviation(
               13, 10, 1, &numerator, &denominator, &collision, &multiplier),
           "decimal prime-thirteen collision deviation computes");
    ASSERT_INT(multiplier, 10, "lag-one multiplier is ten modulo thirteen");
    ASSERT_INT(collision, 0, "decimal prime-thirteen lag-one collision count is zero");
    ASSERT(numerator == -4 && denominator == 2,
           "decimal prime-thirteen deviation is the exact fraction negative four over two");

    ASSERT(collision_characters_prime_deviation(
               7, 2, 3, &numerator, &denominator, &collision, &multiplier),
           "identity-multiplier deviation computes");
    ASSERT_INT(multiplier, 1, "base-two lag three is identity modulo seven");
    ASSERT_INT(collision, 6, "identity multiplier collision count is p-1");
    ASSERT(numerator == 12 && denominator == 4,
           "identity-multiplier deviation is the exact fraction twelve over four");

    int prime_count = 0;
    long double real[4] = {0.0L};
    long double imag[4] = {0.0L};
    ASSERT(collision_characters_base_ten_row(
               100, &prime_count, real, imag),
           "base-ten character snapshot row computes");
    ASSERT_INT(prime_count, 20, "snapshot counts twenty eligible primes");
    ASSERT(fabsl(real[0] + 0.851414L) < 5.1e-7L,
           "snapshot principal component matches the published value");
    ASSERT(fabsl(real[1] + 0.012410L) < 5.1e-7L &&
           fabsl(imag[1] + 0.168966L) < 5.1e-7L,
           "snapshot first complex component matches the published value");
    ASSERT(fabsl(real[2] - 0.300620L) < 5.1e-7L,
           "snapshot real nonprincipal component matches the published value");

    ASSERT(!collision_characters_prime_deviation(
               11, 10, 1, &numerator, &denominator, &collision, &multiplier),
           "collision deviation excludes p equal to base plus one");
    ASSERT(!collision_characters_prime_deviation(
               15, 10, 1, &numerator, &denominator, &collision, &multiplier),
           "collision deviation rejects a composite modulus");
    ASSERT(!collision_characters_prime_deviation(
               13, 10, 0, &numerator, &denominator, &collision, &multiplier),
           "collision deviation rejects a nonpositive lag");
    printf("\n");
}

static void test_silent_primes_variance(void)
{
    printf("Finite silence and collision-variance arithmetic:\n");
    int collision = -1;
    int repetend = -1;
    int recipe = -1;
    ASSERT(silent_primes_collision_count(13, 10, 10, &collision),
           "decimal prime-thirteen global collision count computes");
    ASSERT_INT(collision, 0,
               "decimal prime-thirteen is globally silent at lag one");
    ASSERT(silent_primes_repetend_count(13, 10, 1, &repetend),
           "decimal prime-thirteen repetend count computes");
    ASSERT_INT(repetend, 0,
               "decimal prime-thirteen is repetend-silent at lag one");
    ASSERT(silent_primes_global_recipe_match(13, 10, 1, &recipe),
           "global silent-prime recipe computes");
    ASSERT_INT(recipe, 1,
               "decimal prime-thirteen satisfies the finite recipe");

    ASSERT(silent_primes_collision_count(13, 8, 8, &collision) &&
           silent_primes_repetend_count(13, 8, 1, &repetend),
           "base-eight shorter-orbit example computes");
    ASSERT(collision == 2 && repetend == 0,
           "base-eight prime-thirteen separates global and repetend silence");

    unsigned long long mean_numerator = 0;
    unsigned long long mean_denominator = 0;
    unsigned long long variance_numerator = 0;
    unsigned long long variance_denominator = 0;
    ASSERT(silent_primes_variance_fraction(
               97, 10, &mean_numerator, &mean_denominator,
               &variance_numerator, &variance_denominator),
           "exact constructive variance computes");
    ASSERT(mean_numerator == 414 && mean_denominator == 43,
           "base-ten prime-ninety-seven mean is exactly 414/43");
    ASSERT(variance_numerator == 11096 && variance_denominator == 1849,
           "base-ten prime-ninety-seven variance is exactly 11096/1849");
    ASSERT(!silent_primes_collision_count(15, 10, 1, &collision),
           "silent-prime arithmetic rejects a composite modulus");
    ASSERT(!silent_primes_variance_fraction(
               11, 10, &mean_numerator, &mean_denominator,
               &variance_numerator, &variance_denominator),
           "variance rejects an empty constructive population");
    printf("\n");
}

static void test_collision_fluctuation_sum(void)
{
    printf("Lag-one collision fluctuation arithmetic:\n");
    int value = 0;
    ASSERT(collision_table_value(10, 1, 91, &value),
           "decimal finite table class ninety-one computes");
    ASSERT_INT(value, -9, "decimal finite table class ninety-one is negative nine");
    ASSERT(collision_table_value(10, 1, 9, &value),
           "decimal finite table class nine computes");
    ASSERT_INT(value, 8, "decimal finite table maximum fixture is eight");

    int reflected = 0;
    ASSERT(collision_table_value(10, 1, 9, &value) &&
           collision_table_value(10, 1, 91, &reflected) &&
           value + reflected == -1,
           "finite table reflection pair sums to negative one");

    int collision = 0, deviation = 0, multiplier = 0;
    ASSERT(collision_table_direct_deviation(
               191, 10, 1, &collision, &deviation, &multiplier),
           "direct decimal lag-one collision deviation computes");
    ASSERT(collision == 10 && deviation == -9 && multiplier == 10,
           "direct prime representative equals its finite-table class");

    long long numerator = 0, denominator = 0;
    ASSERT(collision_fluctuation_fraction(
               191, 10, &numerator, &denominator, &collision, &deviation),
           "exact decimal collision fluctuation computes");
    ASSERT(numerator == -9 && denominator == 1,
           "decimal prime-one-ninety-one fluctuation is exactly negative nine");
    ASSERT(!collision_fluctuation_fraction(
               15, 10, &numerator, &denominator, &collision, &deviation),
           "collision fluctuation rejects a composite modulus");
    ASSERT(!collision_table_value(10, 1, 10, &value),
           "finite collision table rejects a nonunit class");
    printf("\n");
}

static void test_centered_collision_sum(void)
{
    printf("All-lag collision centering:\n");
    long long numerator = 0, denominator = 0;
    int table_value = 0;
    ASSERT(centered_collision_fraction(
               10, 1, 91, &numerator, &denominator, &table_value),
           "base-ten centered table class ninety-one computes");
    ASSERT(table_value == -9 && numerator == -73 && denominator == 10,
           "class ninety-one centers exactly to negative seventy-three tenths");

    ASSERT(centered_collision_fraction(
               3, 1, 1, &numerator, &denominator, &table_value),
           "base-three centered class computes");
    ASSERT(table_value == 0 && numerator == 2 && denominator == 3,
           "base-three class one has centered value two thirds");

    int collision = 0, deviation = 0, multiplier = 0;
    ASSERT(collision_table_direct_deviation(
               1009, 10, 2, &collision, &deviation, &multiplier),
           "base-ten lag-two direct example computes");
    ASSERT(deviation == 8 && multiplier == 100,
           "base-ten lag-two direct example matches table class nine");
    ASSERT(collision_table_direct_deviation(
               1109, 10, 2, &collision, &deviation, &multiplier),
           "second base-ten lag-two direct example computes");
    ASSERT_INT(deviation, -10,
               "base-ten lag-two class one-hundred-nine is negative ten");
    ASSERT(collision_table_direct_deviation(
               1101, 10, 2, &collision, &deviation, &multiplier),
           "generalized collision table accepts a coprime composite integer");
    ASSERT(!centered_collision_fraction(
               10, 1, 10, &numerator, &denominator, &table_value),
           "centered table rejects a nonunit residue class");
    printf("\n");
}

static void test_collision_periodic_table(void)
{
    printf("Lag-one collision table:\n");
    int value = 0;
    ASSERT(collision_periodic_value(10, 9, &value),
           "decimal periodic-table maximum class computes");
    ASSERT_INT(value, 8, "decimal periodic-table maximum is eight");
    ASSERT(collision_periodic_value(10, 91, &value),
           "decimal periodic-table minimum class computes");
    ASSERT_INT(value, -9, "decimal periodic-table minimum is negative nine");
    ASSERT(collision_periodic_value(6, 5, &value),
           "composite-base maximum class computes");
    ASSERT_INT(value, 4, "base-six periodic-table maximum is four");

    int collision = 0, deviation = 0, multiplier = 0;
    ASSERT(collision_table_direct_deviation(
               309, 10, 1, &collision, &deviation, &multiplier),
           "periodic theorem direct count accepts a composite integer");
    ASSERT_INT(deviation, 8,
               "composite integer in decimal class nine has fingerprint eight");
    ASSERT(!collision_periodic_value(10, 20, &value),
           "periodic table rejects a nonunit cell");
    ASSERT(!collision_periodic_value(1, 1, &value),
           "periodic table rejects a base below two");
    printf("\n");
}

static void test_collision_transform_strip(void)
{
    printf("Centered collision transform:\n");
    CollisionCenteredTable table = {0};
    ASSERT(collision_centered_table_build(10, 1, &table),
           "shared decimal centered collision table builds");
    ASSERT_INT(table.modulus, 100,
               "decimal lag-one centered table has modulus one hundred");
    ASSERT_INT(table.phi, 40,
               "decimal lag-one centered table has forty unit classes");
    long long numerator = 0, denominator = 0;
    ASSERT(collision_centered_table_fraction(
               &table, 91, &numerator, &denominator),
           "collision-transform centered class computes");
    ASSERT(numerator == -73 && denominator == 10,
           "collision-transform class ninety-one is negative seventy-three tenths");
    FiniteCharacterSpectrum spectrum = {0};
    ASSERT(finite_character_spectrum_compute(&table, &spectrum),
           "complete decimal collision-transform spectrum computes");
    ASSERT_INT(spectrum.character_count, 40,
               "decimal transform has forty character coefficients");
    ASSERT_INT(spectrum.allowed_count, 18,
               "decimal exact gate leaves eighteen possible channels");
    ASSERT_INT(spectrum.resolved_active_count, 17,
               "decimal transform resolves seventeen active coefficients");
    ASSERT(spectrum.maximum_even_coefficient <= spectrum.tolerance &&
           spectrum.maximum_base_factored_coefficient <= spectrum.tolerance,
           "decimal forbidden coefficients vanish at the printed tolerance");
    ASSERT(spectrum.inversion_error < 5e-11L &&
           spectrum.parseval_error < 5e-11L &&
           spectrum.conjugate_error < 5e-11L,
           "decimal transform inversion Parseval and conjugacy agree");
    finite_character_spectrum_free(&spectrum);
    collision_centered_table_free(&table);

    const long double exponent = 1.0L;
    long double sum = 0.0L;
    int prime_count = 0;
    ASSERT(collision_transform_prime_window(
               1000, 10000, 10, 1, &exponent, 1, &sum, &prime_count),
           "declared collision-transform prime window computes");
    ASSERT_INT(prime_count, 1061,
               "declared collision-transform window contains expected primes");
    ASSERT(fabsl(sum - 0.013372187894L) < 5e-13L,
           "declared collision-transform window has expected centered sum");
    printf("\n");
}

static void test_residue_three_neutrality(void)
{
    printf("Residue-three neutrality:\n");
    long long raw_sum = 0, centered_sum = 0;
    int count = 0, joint_modulus = 0;
    ASSERT(residue_three_neutrality_channel_sums(
               10, 1, 1, &raw_sum, &centered_sum,
               &count, &joint_modulus),
           "decimal true class-one channel computes");
    ASSERT(raw_sum == -20 && centered_sum == 0 && count == 40 &&
           joint_modulus == 300,
           "decimal true class-one channel is independently neutral");
    ASSERT(residue_three_neutrality_channel_sums(
               10, 1, 2, &raw_sum, &centered_sum,
               &count, &joint_modulus),
           "decimal true class-two channel computes");
    ASSERT(raw_sum == -20 && centered_sum == 0 && count == 40,
           "decimal true class-two channel is independently neutral");
    ASSERT(residue_three_neutrality_channel_sums(
               3, 1, 1, &raw_sum, &centered_sum,
               &count, &joint_modulus),
           "divisible-base true channel computes");
    ASSERT(centered_sum == 0 && count == 3 && joint_modulus == 9,
           "divisible-base true channel is a zero-sum fiber union");

    const long double exponent = 1.0L;
    long double one = 0.0L, two = 0.0L, total = 0.0L, twist = 0.0L;
    int count_one = 0, count_two = 0;
    ASSERT(residue_three_neutrality_prime_window(
               1000, 10000, 10, 1, &exponent, 1,
               &one, &two, &total, &twist,
               &count_one, &count_two),
           "declared true-channel prime split computes");
    ASSERT(count_one == 531 && count_two == 530,
           "declared true-channel split has expected class counts");
    ASSERT(fabsl((one + two) - total) < 1e-17L &&
           fabsl((one - two) - twist) < 1e-17L,
           "finite total and twist equal the exact channel sum and difference");
    printf("\n");
}

static void test_centered_tables_and_coprime_base_moments(void)
{
    printf("Centered tables and coprime-base moments:\n");
    CollisionCenteredTable table = {0};
    ASSERT(collision_centered_table_build(3, 1, &table),
           "base-three lag-one transversality table builds");
    ASSERT_INT(table.modulus, 9,
               "base-three lag-one modulus is nine");
    ASSERT_INT(table.phi, 6,
               "base-three lag-one table has six unit residues");
    ASSERT_INT(table.value[5], -1,
               "base-three residue five has raw value negative one");
    ASSERT(table.value[5] + table.value[4] == -1,
           "base-three reflected raw pair sums to negative one");
    long long numerator = 0, denominator = 0;
    ASSERT(collision_centered_table_fraction(
               &table, 5, &numerator, &denominator),
           "base-three centered residue fraction computes");
    ASSERT(numerator == -2 && denominator == 3,
           "base-three residue five has centered value negative two thirds");
    long long centered_sum = 0;
    unsigned long long scaled_square_sum = 0;
    for (int a = 1; a < table.modulus; a++) {
        if (collision_table_gcd(a, table.modulus) != 1) continue;
        centered_sum += table.centered_numerator[a];
        scaled_square_sum +=
            (unsigned long long)(table.centered_numerator[a] *
                                 table.centered_numerator[a]);
    }
    ASSERT(centered_sum == 0,
           "base-three centered table has exact global zero mean");
    ASSERT(scaled_square_sum == 48,
           "base-three scaled CRT square sum is exactly forty-eight");
    collision_centered_table_free(&table);

    ASSERT(collision_centered_table_build(5, 1, &table),
           "base-five lag-one transversality table builds");
    scaled_square_sum = 0;
    for (int a = 1; a < table.modulus; a++)
        if (collision_table_gcd(a, table.modulus) == 1)
            scaled_square_sum +=
                (unsigned long long)(table.centered_numerator[a] *
                                     table.centered_numerator[a]);
    ASSERT(scaled_square_sum == 1200,
           "base-five scaled CRT square sum is exactly twelve hundred");
    collision_centered_table_free(&table);
    printf("\n");
}

static void test_reflection_well_and_reflected_prime_pair_sign(void)
{
    CollisionCenteredTable table = {0};
    long long convolution[9] = {0};
    long long energy = 0;
    long long total = 0;
    long long goldbach_sum = 0;
    long long negative_squares = 0;
    int ordered_pairs = 0;
    int even = 1;
    int nonpositive = 1;

    printf("Additive reflection well and reflected prime-pair sign:\n");
    ASSERT(collision_centered_table_build(3, 1, &table),
           "base-three centered table builds for additive checks");
    for (int residue = 0; residue < table.modulus; residue++)
        energy += table.centered_numerator[residue] *
                  table.centered_numerator[residue];
    for (int shift = 0; shift < table.modulus; shift++) {
        for (int residue = 0; residue < table.modulus; residue++) {
            int other = shift - residue;
            if (other < 0) other += table.modulus;
            convolution[shift] += table.centered_numerator[residue] *
                                  table.centered_numerator[other];
        }
        total += convolution[shift];
    }
    for (int shift = 0; shift < table.modulus; shift++) {
        int reflected = shift == 0 ? 0 : table.modulus - shift;
        if (convolution[shift] != convolution[reflected]) even = 0;
    }
    ASSERT(energy == 48 && convolution[0] == -48,
           "base-three reflection well is the negative exact energy");
    ASSERT(total == 0 && even,
           "base-three convolution is even and has exact zero total");
    for (int prime = 2; prime <= 16; prime++) {
        int partner = 18 - prime;
        long long left, right, term;
        if (!is_prime_test(prime) || !is_prime_test(partner)) continue;
        left = table.centered_numerator[prime % table.modulus];
        right = table.centered_numerator[partner % table.modulus];
        term = left * right;
        goldbach_sum += term;
        negative_squares -= left * left;
        ordered_pairs++;
        if (term > 0) nonpositive = 0;
    }
    ASSERT(ordered_pairs == 4 && goldbach_sum == -40,
           "target eighteen has four ordered pairs and exact weight negative forty");
    ASSERT(nonpositive && goldbach_sum == negative_squares,
           "each target-eighteen term is nonpositive and the sum is negative squares");
    collision_centered_table_free(&table);
    printf("\n");
}

static void test_collision_spectrum_factorization_and_cyclotomic_certificate(void)
{
    static const int polynomial_p[8] = {1, 1, 1, 0, 0, 0, 0, 1};
    static const int polynomial_q[8] = {1, 2, 3, 1, -2, 1, 1, 2};
    static const int cyclotomic[9] = {1, 0, -1, 0, 1, 0, -1, 0, 1};
    static const int quotient[7] = {-3, 0, 1, 5, 1, 0, -3};
    int left[15] = {0};
    int right[15] = {0};
    int mismatches = 0;
    CollisionSpectrumContext context = {0};
    CollisionSpectrumCharacter character;
    CollisionSpectrumTransform transform;

    printf("Collision-spectrum factorization and cyclotomic certificate:\n");
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 8; j++) {
            int degree = 7 + i - j;
            left[degree] += polynomial_q[i] * polynomial_q[j] -
                            5 * polynomial_p[i] * polynomial_p[j];
        }
    }
    for (int i = 0; i < 9; i++)
        for (int j = 0; j < 7; j++)
            right[i + j] += cyclotomic[i] * quotient[j];
    for (int degree = 0; degree < 15; degree++)
        if (left[degree] != right[degree]) mismatches++;
    ASSERT(mismatches == 0,
           "base-five Laurent polynomial certificate is exact coefficientwise");
    ASSERT(32 * 8 + 28 * 2 - 14 * 2 + 34 * 2 - 18 * 2 - 2 * 8 == 300,
           "base-five Ramanujan fourth-moment sum is exactly three hundred");
    ASSERT(collision_spectrum_context_build(5, &context),
           "base-five collision-spectrum context builds");
    ASSERT(collision_spectrum_character_compute(&context, 1, &character),
           "first primitive odd base-five character computes");
    ASSERT(character.diagonal_error < 1e-15L &&
           character.factorization_error < 1e-15L,
           "direct diagonal and collision coefficient match both factorizations");
    ASSERT(character.fiber_cancellation_error < 1e-15L &&
           character.centering_error < 1e-15L,
           "primitive character cancels on every base fiber and removes centering");
    ASSERT(collision_spectrum_transform_compute(&context, 1, 6, &transform) &&
           transform.fractional_error < 1e-15L &&
           transform.floor_error < 1e-15L,
           "fractional-part and floor transforms match the Bernoulli formulas");
    ASSERT(fabsl(cabsl(character.diagonal_direct) -
                 sqrtl(5.0L) * cabsl(character.bernoulli_one)) < 1e-15L,
           "base-five diagonal magnitude is sqrt five times Bernoulli magnitude");
    collision_spectrum_context_free(&context);
    printf("\n");
}

static void test_periodic_zeta_and_boundary_objects(void)
{
    PeriodicZetaContext context = {0};
    PeriodicZetaContext two_power = {0};
    PeriodicZetaComparison comparison;
    char error[160];
    long double complex fiber_sum = 0.0L;
    long double complex collision_direct;
    long double complex collision_factorized;
    long double complex left_direct;
    long double complex left_factorized;
    long double complex right_direct;
    long double complex right_factorized;
    long double complex right_l_value;

    printf("Primitive cancellation, periodic zeta, and boundary recovery:\n");
    ASSERT(periodic_zeta_context_build(
               5, 1, &context, error, sizeof(error)),
           "base-five lag-one periodic-zeta context builds");
    ASSERT(context.modulus == 25 && context.phi == 20 &&
           context.diagonal_count == 5 &&
           context.diagonal[0] == 0 && context.diagonal[1] == 6 &&
           context.diagonal[2] == 12 && context.diagonal[3] == 18 &&
           context.diagonal[4] == 24,
           "base-five context has the exact modulus, totient, and lag-one diagonal");
    ASSERT(periodic_zeta_character_count(&context) == 8 &&
           periodic_zeta_character_valid(&context, 1) &&
           !periodic_zeta_character_valid(&context, 5),
           "base-five primitive odd character indices exclude imprimitive index five");
    ASSERT(cabsl(periodic_zeta_character_value(
                     &context, 1, 24) + 1.0L) < 1e-15L,
           "base-five character index one is odd");
    for (int index = 0; index < context.unit_count; index++) {
        int unit = context.units[index];
        if (unit % 5 == 1)
            fiber_sum += conjl(periodic_zeta_character_value(
                &context, 1, unit));
    }
    ASSERT(cabsl(fiber_sum) < 1e-15L,
           "one complete base-five conductor fiber cancels");
    ASSERT(periodic_zeta_model_comparison(
               &context, 1, 1, 0.5L + 0.2L * I, &comparison) &&
           comparison.relative_error < 1e-15L,
           "direct unit model sum matches the periodic-zeta factorization");
    ASSERT(periodic_zeta_model_comparison(
               &context, 1, 5, 0.5L + 0.2L * I, &comparison) &&
           comparison.relative_error < 1e-15L,
           "nonunit periodic-zeta model sum cancels");
    ASSERT(periodic_zeta_transform_comparison(
               &context, 1, 0.5L + 0.2L * I, &comparison) &&
           comparison.relative_error < 1e-15L,
           "direct centered transform matches its fixed-diagonal factorization");
    ASSERT(periodic_zeta_finite_collision_coefficient(
               &context, 1, &collision_direct, &collision_factorized) &&
           cabsl(collision_direct - collision_factorized) < 1e-15L,
           "finite collision coefficient matches its Bernoulli factorization");
    ASSERT(periodic_zeta_boundary_values(
               &context, 1,
               &left_direct, &left_factorized,
               &right_direct, &right_factorized, &right_l_value) &&
           cabsl(left_direct - left_factorized) < 1e-15L &&
           cabsl(left_direct - I * acosl(-1.0L) * collision_direct) < 1e-15L,
           "left boundary directly recovers i pi times the finite coefficient");
    ASSERT(cabsl(right_direct - right_factorized) < 1e-15L &&
           cabsl(right_l_value - right_factorized) < 1e-15L,
           "right boundary matches both Gauss-Bernoulli and cotangent L values");
    periodic_zeta_context_free(&context);

    ASSERT(periodic_zeta_context_build(
               2, 2, &two_power, error, sizeof(error)),
           "modulus-eight noncyclic unit-group context builds");
    ASSERT(two_power.modulus == 8 && two_power.diagonal_count == 4 &&
           two_power.diagonal[0] == 0 && two_power.diagonal[3] == 7 &&
           periodic_zeta_character_count(&two_power) == 1 &&
           periodic_zeta_character_valid(&two_power, 1),
           "modulus eight has the exact diagonal and expected primitive odd product character");
    ASSERT(periodic_zeta_transform_comparison(
               &two_power, 1, 0.5L + 0.2L * I, &comparison) &&
           comparison.relative_error < 1e-15L,
           "noncyclic two-power transform matches the same factorization");
    periodic_zeta_context_free(&two_power);
    printf("\n");
}

static void test_collision_coordinate_and_finite_table_objects(void)
{
    printf("Collision coordinate and finite-table objects:\n");
    int direct = 0;
    int formula = 0;
    int coordinate = 0;
    ASSERT(collision_coordinate_values(
               13, 10, 6, &direct, &formula, &coordinate),
           "collision coordinate computes for a nonidentity multiplier");
    ASSERT(direct == 2 && formula == 2 && coordinate == 11,
           "prime-thirteen multiplier-six coordinate formula is exact");
    ASSERT(!collision_coordinate_values(
               13, 10, 1, &direct, &formula, &coordinate),
           "collision coordinate rejects the identity multiplier");
    ASSERT(!collision_coordinate_values(
               15, 10, 6, &direct, &formula, &coordinate),
           "collision coordinate rejects a composite modulus");
    int congruence = 0;
    int structure = 0;
    ASSERT(collision_coordinate_conjugation_values(
               21, 10, 8, &direct, &congruence, &structure),
           "base conjugation computes on a coprime composite modulus");
    ASSERT(structure && direct == congruence,
           "composite-modulus digit and congruence collisions agree exactly");
    ASSERT(!collision_coordinate_conjugation_values(
               21, 7, 8, &direct, &congruence, &structure),
           "base conjugation rejects a modulus sharing a factor with the base");

    int table_value = 0;
    int direct_value = 0;
    ASSERT(finite_determination_compare(
               191, 10, 1, &table_value, &direct_value),
           "finite determination compares a direct representative");
    ASSERT(table_value == -9 && direct_value == -9,
           "decimal class ninety-one determines prime one-ninety-one");
    ASSERT(finite_determination_compare(
               1009, 10, 2, &table_value, &direct_value),
           "all-lag finite determination compares a lag-two representative");
    ASSERT(table_value == 8 && direct_value == 8,
           "lag-two representative matches its modulus-one-thousand table cell");
    ASSERT(finite_determination_compare(
               91, 10, 1, &table_value, &direct_value),
           "finite determination includes the quotient-zero case");
    ASSERT(table_value == -9 && direct_value == -9,
           "small decimal unit uses the same exact finite table");
    int slice_collision = 0;
    int diagonal_count = 0;
    ASSERT(finite_determination_slice_values(
               191, 10, 1, &direct, &slice_collision,
               &diagonal_count, &structure),
           "pointwise all-lag slice bridge computes");
    ASSERT(structure && direct == 10 && slice_collision == 10 &&
           diagonal_count == 10,
           "direct collision, endpoint-corrected slices, and diagonal agree");
    ASSERT(!finite_determination_compare(
               1, 10, 1, &table_value, &direct_value),
           "finite determination rejects an integer below two");

    int reflected = 0;
    ASSERT(reflection_identity_pair_values(
               10, 1, 9, &table_value, &reflected),
           "reflection pair values compute");
    ASSERT(table_value == 8 && reflected == -9 &&
           table_value + reflected == -1,
           "decimal reflected pair has exact sum negative one");
    ASSERT(!reflection_identity_pair_values(
               10, 1, 10, &table_value, &reflected),
           "reflection identity rejects a nonunit residue");
    int interior_count = 0;
    ASSERT(reflection_identity_local_values(
               10, 1, 9, &interior_count, &structure),
           "local reflection identities compute");
    ASSERT(structure && interior_count == 98,
           "every interior floor jump and endpoint satisfies reflection");

    int wraps = 0;
    int totient = 0;
    ASSERT(half_group_cardinality(10, 3, &wraps, &totient),
           "half-group cardinality computes for an interior cut");
    ASSERT(totient == 4 && wraps == 2,
           "modulus-ten wrapping set contains half of its unit group");
    int unit_count = 0;
    ASSERT(half_group_reflection_values(
               10, 3, &unit_count, &structure),
           "half-group residue reflection computes");
    ASSERT(structure && unit_count == 4,
           "residue reflection exchanges every unit wrapping comparison");
    ASSERT(!half_group_cardinality(10, 9, &wraps, &totient),
           "half-group cardinality rejects a noninterior index");
    printf("\n");
}

static void test_all_prime_labels_and_spectral_quotient(void)
{
    int direct = 0;
    int table = 0;
    int uses_table = 0;
    int labels = 0;
    int bulk = 0;
    double action_error = 0.0;

    printf("All-prime labels and finite spectral quotient:\n");
    ASSERT(all_prime_collision_label_value(
               13, 10, 1, &direct, &table, &uses_table),
           "prime-thirteen collision label computes in base ten");
    ASSERT(uses_table && direct == -1 && table == -1,
           "prime-thirteen direct label equals its exact finite-table label");
    ASSERT(all_prime_collision_label_value(
               2, 10, 1, &direct, &table, &uses_table),
           "base-prime collision label computes");
    ASSERT(!uses_table && direct == 0 && table == 0,
           "a prime dividing the base has exact collision label zero");
    ASSERT(!all_prime_collision_label_value(
               15, 10, 1, &direct, &table, &uses_table),
           "all-prime collision labels reject composite inputs");

    ASSERT(finite_spectral_quotient_metrics(
               10, 1, 40, 1.0, &labels, &bulk, &action_error),
           "finite spectral quotient passes for forty decimal prime states");
    ASSERT(labels == 11 && bulk == 29,
           "forty decimal prime states split into eleven labels and bulk twenty-nine");
    ASSERT(action_error < 1e-12,
           "full collision-label operator agrees with its finite quotient");
    ASSERT(!finite_spectral_quotient_metrics(
               10, 1, 40, 0.0, &labels, &bulk, &action_error),
           "finite spectral quotient rejects a nonpositive kernel scale");
    printf("\n");
}

static void test_finite_prefix_and_boundary_factorization(void)
{
    int weights[9] = {1, 0, 0, 0, 1, 0, 0, 0, 1};
    long long intrinsic = 0;
    long long carries = 0;
    long long weight_sum = 0;
    long long left = 0;
    long long right = 0;
    long double factorization_error = 0.0L;
    long double boundary_error = 0.0L;
    long double direct_correlation = 0.0L;
    long double dedekind_correlation = 0.0L;
    long double correlation_error = 0.0L;
    int visible_endpoints = 0;
    CarryBoundarySpectrumSummary spectrum = {0};
    BoundaryConductorLedgerSummary ledger = {0};

    printf("Finite-prefix slice and boundary factorization:\n");
    ASSERT(finite_prefix_slice_identity(
               11, 3, 2, weights, 9,
               &intrinsic, &carries, &weight_sum, &left, &right),
           "nine-state finite-prefix slice identity computes exactly");
    ASSERT(intrinsic == 4 && carries == 2 && weight_sum == 3,
           "nine-state slice has intrinsic count four and carry count two");
    ASSERT(left == 12 && right == 12,
           "both centered slice numerators equal twelve");
    ASSERT(!finite_prefix_slice_identity(
               12, 3, 2, weights, 9,
               &intrinsic, &carries, &weight_sum, &left, &right),
           "finite-prefix slice rejects a denominator sharing the base");
    ASSERT(finite_prefix_slice_identity_all_denominators(
               12, 3, 2, weights, 9,
               &intrinsic, &carries, &weight_sum, &left, &right),
           "all-denominator slice includes a denominator sharing the base");
    ASSERT(intrinsic == 3 && carries == 1 && weight_sum == 3,
           "nonunit phase has the exact ceiling-boundary count");
    ASSERT(left == 0 && right == 0,
           "nonunit centered transposition vanishes exactly");
    ASSERT(finite_prefix_slice_identity_all_denominators(
               9, 3, 2, weights, 9,
               &intrinsic, &carries, &weight_sum, &left, &right),
           "all-denominator slice includes zero phase");
    ASSERT(intrinsic == 2 && carries == 0 && left == 0 && right == 0,
           "zero phase has bulk minus the initial endpoint");

    int transient = 0;
    int persistent = 0;
    int collapse_depth = 0;
    int stable_kernel = 0;
    int stable_image = 0;
    ASSERT(positional_transport_collapse(
               28, 10, &transient, &persistent, &collapse_depth,
               &stable_kernel, &stable_image),
           "base-ten transport decomposition for denominator twenty-eight");
    ASSERT(transient == 4 && persistent == 7 && collapse_depth == 2 &&
               stable_kernel == 4 && stable_image == 7,
           "denominator twenty-eight collapses to its seven-state survivor");
    ASSERT(positional_transport_collapse(
               7, 10, &transient, &persistent, &collapse_depth,
               &stable_kernel, &stable_image),
           "coprime transport decomposition computes");
    ASSERT(transient == 1 && persistent == 7 && collapse_depth == 0 &&
               stable_kernel == 1 && stable_image == 7,
           "the world of seven has no exact-state collapse");

    ASSERT(boundary_bernoulli_factorization_compare(
               3, 2, 1, weights, 9,
               &factorization_error, &boundary_error, &visible_endpoints),
           "modulus-nine boundary-Bernoulli factorization passes");
    ASSERT(visible_endpoints == 4,
           "modulus-nine collision support has four visible endpoints");
    ASSERT(factorization_error < 1e-12L && boundary_error < 1e-12L,
           "direct transform and visible flux match their factorizations");
    ASSERT(!boundary_bernoulli_factorization_compare(
               3, 2, 3, weights, 9,
               &factorization_error, &boundary_error, &visible_endpoints),
           "boundary factorization rejects an imprimitive character exponent");
    ASSERT(boundary_bernoulli_conductor_spectrum(
               3, 2, weights, 9, &spectrum),
           "complete modulus-nine conductor spectrum computes");
    ASSERT(spectrum.odd_channels == 3 &&
               spectrum.conductor_channels[0] == 1 &&
               spectrum.conductor_channels[1] == 2 &&
               fabsl(spectrum.conductor_energy[0]) < 1.0e-12L &&
               fabsl(spectrum.conductor_energy[1] - 16.0L / 3.0L) < 1.0e-11L &&
               spectrum.energy_error < 1.0e-12L,
           "conductor channels recover the full unit energy exactly within tolerance");
    ASSERT(boundary_sawtooth_correlation(
               3, 2, 1, 2, &direct_correlation,
               &dedekind_correlation, &correlation_error),
           "unit sawtooth correlation computes in direct and Dedekind forms");
    ASSERT(fabsl(direct_correlation - dedekind_correlation) < 1.0e-12L &&
               correlation_error < 1.0e-12L,
           "direct and Mobius-Dedekind correlations agree");
    ASSERT(boundary_conductor_ledger_compute(9, weights, 9, &ledger),
           "modulus-nine conductor ledger computes with integer arithmetic");
    ASSERT(ledger.formal_boundary == 6 && ledger.unit_norm == 4 &&
               ledger.primitive_odd_moment == 24 &&
               ledger.primitive_odd_characters == 2 &&
               ledger.mean_numerator == 12 && ledger.mean_denominator == 1 &&
               ledger.antipodal_odd && ledger.conductor_balance &&
               ledger.proper_pushdowns_vanish && ledger.top_concentrated &&
               ledger.energy_count == 3 &&
               ledger.energy[0].conductor == 1 && ledger.energy[0].energy == 0 &&
               ledger.energy[1].conductor == 3 && ledger.energy[1].energy == 0 &&
               ledger.energy[2].conductor == 9 && ledger.energy[2].energy == 24 &&
               ledger.proper_conductor_energy == 0 &&
               ledger.top_conductor_energy == 24 &&
               ledger.full_odd_energy == 24,
           "modulus-nine ledger recovers boundary six and mean twelve");
    ASSERT(!boundary_conductor_ledger_compute(9, weights, 8, &ledger),
           "conductor ledger rejects a mismatched carrier length");
    printf("\n");
}

static void test_orbit_boundary_energy_objects(void)
{
    long long kernel = 0;
    long long closed = 0;
    long long full = 0;
    long long resonant_energy = 0;
    long long off_energy = 0;
    int orbit_size = 0;
    int thickness = 0;
    int character_count = 0;
    long double expansion_error = 0.0L;
    int order = 0;
    int index = 0;
    int resonant = 0;
    FiniteStateOrbitBoundarySummary finite_state = {0};

    printf("Orbit-boundary energy objects:\n");
    ASSERT(full_orbit_energy_values(
               2, 3, 2, &kernel, &closed, &orbit_size, &thickness),
           "base two generates the complete unit orbit modulo nine");
    ASSERT(kernel == 9 && closed == 9,
           "modulus-nine odd-kernel energy equals the closed value nine");
    ASSERT(orbit_size == 6 && thickness == 3,
           "modulus-nine orbit has six states and prime-power thickness three");
    ASSERT(!full_orbit_energy_values(
               4, 3, 2, &kernel, &closed, &orbit_size, &thickness),
           "full-orbit energy rejects a base that is not a primitive root");

    int transition[4] = {0, 1, 1, 0};
    int state_weights[14] = {0};
    for (int remainder = 0; remainder < 7; remainder++)
        state_weights[2 * remainder + 1] = 1;
    ASSERT(finite_state_orbit_boundary_compute(
               2, 7, 2, 1, 0, transition, 4,
               state_weights, 14, &finite_state),
           "digit-parity automaton closes on a lifted remainder cycle");
    ASSERT(finite_state.remainder_period == 3 &&
               finite_state.transient_length == 0 &&
               finite_state.cycle_length == 6 &&
               finite_state.boundary_nonzero == 2 &&
               finite_state.boundary_sum == 0 &&
               finite_state.boundary_squared_norm == 2,
           "lifted parity cycle has the exact predecessor boundary");

    ASSERT(quadratic_orbit_energy_values(
               7, &full, &resonant_energy, &off_energy,
               &closed, &character_count),
           "prime-seven quadratic-orbit energy computes exactly");
    ASSERT(full == 18 && resonant_energy == 16 &&
           off_energy == 2 && closed == 2,
           "prime-seven full, resonant, and off-resonance energies agree");
    ASSERT(character_count == 2,
           "prime seven has two off-resonance odd characters");

    ASSERT(subgroup_jacobi_expansion_compare(
               7, 2, 1, &expansion_error, &order, &index, &resonant),
           "prime-seven subgroup flux matches its Jacobi expansion");
    ASSERT(order == 3 && index == 2 && !resonant &&
           expansion_error < 1e-12L,
           "base-two subgroup has index two and exponent one is off resonance");
    ASSERT(subgroup_jacobi_expansion_compare(
               7, 2, 3, &expansion_error, &order, &index, &resonant) &&
           resonant,
           "quadratic character exponent is the resonant index-two channel");
    printf("\n");
}

static void test_prime_base_collision_energy_objects(void)
{
    PrimeBaseCollisionEnergy energy = {0};
    long double energy_ratio = 0.0L;
    long double secondary_ratio = 0.0L;
    long double coefficient = 0.0L;

    printf("Prime-base collision-energy objects:\n");
    ASSERT(prime_base_collision_energy_values(5, &energy),
           "base-five carry and Dedekind energy dictionary passes exactly");
    ASSERT(energy.energy_numerator == 1200 &&
           energy.energy_denominator == 25,
           "base-five class-centered energy is exactly forty-eight");
    ASSERT(energy.raw_variance == 54 &&
           energy.half_centered_square == 196,
           "base-five threshold normalizations match independently");
    ASSERT(energy.dedekind_scaled_numerator == 14400 &&
           energy.diagonal_scaled_numerator == 8832,
           "base-five total and diagonal Dedekind masses are exact");
    ASSERT(energy.upper_scaled_numerator == 2784 &&
           energy.lower_scaled_numerator == 2784,
           "base-five ratio orientations pair exactly");
    ASSERT(energy.threshold_equivalence && energy.column_law &&
           energy.reflection_law && energy.energy_dictionary,
           "independent finite energy identities all report success");
    ASSERT(!prime_base_collision_energy_values(9, &energy),
           "prime-base collision energy rejects a composite base");

    ASSERT(arithmetic_boundary_defect_metrics(
               5, &energy_ratio, &secondary_ratio, &coefficient),
           "arithmetic boundary-defect metrics use the exact energy");
    ASSERT(fabsl(energy_ratio - 48.0L / 125.0L) < 1.0e-18L &&
           fabsl(coefficient +
                 1.0L / (acosl(-1.0L) * acosl(-1.0L))) < 1.0e-18L,
           "finite energy ratio and proved secondary coefficient are encoded exactly");
    ASSERT(!arithmetic_boundary_defect_metrics(
               2, &energy_ratio, &secondary_ratio, &coefficient),
           "arithmetic boundary defect rejects the even-prime boundary");
    printf("\n");
}

static void test_carry_completed_carrier_objects(void)
{
    CarryCompletedCarrierSummary carrier = {0};
    CarryCompletedCarrierGramSummary gram = {0};
    long long projected_numerator = 0;
    long long projected_denominator = 0;
    long long transverse_numerator = 0;
    long long transverse_denominator = 0;
    long long translated_numerator = 0;
    long long translated_denominator = 0;

    printf("Carry-completed carrier objects:\n");
    ASSERT(carry_completed_carrier_compute(30, 7, 2, &carrier),
           "base-thirty source data constructs the completed carrier");
    ASSERT(carrier.completed_size == 360 &&
               carrier.sheet_quotient_size == 60 &&
               carrier.clock_quotient_size == 30,
           "the exact quotient sizes are 360 to 60 to 30");
    ASSERT(carrier.transition_conjugacy && carrier.half_turn_complement,
           "the successor increments one coordinate and its half-turn complements");
    ASSERT(carrier.degree_zero_cells == 180 &&
               carrier.degree_one_cells == 360 &&
               carrier.degree_two_cells == 180,
           "the six product tori have the exact balanced cell ledger");
    ASSERT(fabsl(carrier.least_positive_hodge -
                 (3.0L - sqrtl(5.0L)) / 2.0L) < 1.0e-17L,
           "the least product Hodge response is reciprocal golden squared");
    ASSERT(!carry_completed_carrier_compute(31, 7, 2, &carrier),
           "the carrier rejects a clock not divisible by the source order");

    ASSERT(carry_completed_carrier_seam_values(
               30, &projected_numerator, &projected_denominator,
               &transverse_numerator, &transverse_denominator,
               &translated_numerator, &translated_denominator),
           "the base-thirty seam energies compute exactly");
    ASSERT(projected_numerator == 421 && projected_denominator == 450 &&
               transverse_numerator == 29 && transverse_denominator == 450 &&
               translated_numerator == 29 && translated_denominator == 15,
           "the retained, transverse, and translated energies are exact");

    ASSERT(carry_completed_carrier_product_gram(
               10, 3, -3, 1, &gram),
           "the cubic-decagonal coherent Gram has an exact mode map");
    ASSERT(gram.frequency_bijection && gram.clock_size == 30 &&
               fabsl(gram.constant_response - 10.0L) < 1.0e-18L &&
               gram.golden_polynomial_hits == 4,
           "the product response has thirty modes, constant ten, and four golden roots");
    ASSERT(fabsl(gram.trace - 30.0L * 2691.0L / 2030.0L) < 1.0e-12L &&
               fabsl(gram.first_centered_response - 1.0L) < 1.0e-17L &&
               fabsl(gram.second_centered_response - 1.0L) < 1.0e-17L,
           "the formed spectrum reproduces its trace and centered cubic pair");
    printf("\n");
}

static void test_oriented_digit_comparison_objects(void)
{
    int direct = 0;
    int formula = 0;
    int norm_squared = 0;
    long long intrinsic = 0;

    printf("Oriented two-digit comparison objects:\n");
    ASSERT(oriented_digit_comparison_response_direct(10, 20, &direct) &&
           oriented_digit_comparison_response_formula(10, 20, &formula) &&
           direct == 8 && formula == 8,
           "base-ten phase twenty has exact ramified response eight");
    ASSERT(oriented_digit_comparison_response_direct(10, 21, &direct) &&
           direct == 0,
           "every unit phase is silent in the oriented comparison response");
    ASSERT(oriented_digit_comparison_response_direct(10, 0, &direct) &&
           direct == 0,
           "the zero phase is silent despite its full carrier gcd");
    ASSERT(oriented_digit_comparison_boundary_norm(10, &norm_squared) &&
           norm_squared == 54,
           "the base-ten oriented boundary has squared norm six times nine");
    ASSERT(oriented_digit_comparison_intrinsic_count(120, 10, &intrinsic) &&
           intrinsic == 8,
           "the all-denominator signed descent excess equals its phase response");
    ASSERT(oriented_digit_comparison_response_direct(5, 5, &direct) &&
           direct == 4,
           "the base-five prime-square ramified row has response four");
    ASSERT(!oriented_digit_comparison_response_formula(5, 25, &formula),
           "the phase domain rejects the carrier endpoint");
    printf("\n");
}

int main(void)
{
    printf("nfield unit tests\n");
    printf("==================================================\n\n");

    test_repetend();
    test_field();
    test_alignment();
    test_sigma();
    test_invariants();
    test_bins();
    test_mult_order();
    test_golden_threshold();
    test_reciprocal_square_selection();
    test_bases();
    test_polar();
    test_collision_theorems();
    test_spectral_autocorrelation_theorems();
    test_digit_function_structure();
    test_deficit_lattice();
    test_coherence_decomposition();
    test_cross_alignment();
    test_spectral_structure();
    test_spectral_power();
    test_autocorrelation_formula();
    test_phase_filtered_ramanujan();
    test_bin_derangements();
    test_collision_characters();
    test_silent_primes_variance();
    test_collision_fluctuation_sum();
    test_centered_collision_sum();
    test_collision_periodic_table();
    test_collision_transform_strip();
    test_residue_three_neutrality();
    test_centered_tables_and_coprime_base_moments();
    test_reflection_well_and_reflected_prime_pair_sign();
    test_collision_spectrum_factorization_and_cyclotomic_certificate();
    test_periodic_zeta_and_boundary_objects();
    test_collision_coordinate_and_finite_table_objects();
    test_all_prime_labels_and_spectral_quotient();
    test_finite_prefix_and_boundary_factorization();
    test_orbit_boundary_energy_objects();
    test_prime_base_collision_energy_objects();
    test_carry_completed_carrier_objects();
    test_oriented_digit_comparison_objects();

    printf("==================================================\n");
    printf("%d tests: %d passed, %d failed\n",
           tests_run, tests_passed, tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
