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

    printf("\n");
}

/* ── sigma (pairwise alignment) tests ───────────────────── */

static void test_sigma(void)
{
    printf("sigma_exact:\n");

    /* sigma(p) = 0 for DP primes */
    ASSERT_DBL(sigma_exact(3, 10), 0.0, 1e-10, "sigma(3) = 0");
    ASSERT_DBL(sigma_exact(7, 10), 0.0, 1e-10, "sigma(7) = 0");
    ASSERT_DBL(sigma_exact(11, 10), 0.0, 1e-10, "sigma(11) = 0");

    /* sigma(p) > 0 for non-DP primes */
    ASSERT(sigma_exact(13, 10) > 1e-10, "sigma(13) > 0");
    ASSERT(sigma_exact(17, 10) > 1e-10, "sigma(17) > 0");

    /* F = alpha - sigma >= 0 */
    {
        int test_n[] = {6, 12, 14, 21, 33};
        for (int i = 0; i < 5; i++) {
            int n = test_n[i];
            double a = alignment_exact(n, 10);
            double s = sigma_exact(n, 10);
            double F = a - s;
            char msg[64];
            snprintf(msg, sizeof(msg), "F(%d) = alpha - sigma >= 0", n);
            ASSERT(F >= -1e-10, msg);
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

/* -- Paper G: digit function structural tests ------------ */

static int gcd_test(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

static int modinv_test(int a, int m) {
    int g = m, x = 0, y = 1, a0 = a;
    while (a0) { int q = g/a0; int t = g-q*a0; g=a0; a0=t; t=x-q*y; x=y; y=t; }
    return ((x % m) + m) % m;
}

static void test_paper_g(void)
{
    printf("Paper G structural identities:\n\n");


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
    test_bases();
    test_polar();
    test_paper_g();

    printf("==================================================\n");
    printf("%d tests: %d passed, %d failed\n",
           tests_run, tests_passed, tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
