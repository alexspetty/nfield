/*
 * Verification routines for papers 1, 2, 3, 5, 8.
 * Extracted from the nfield engine for standalone use.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "nfield.h"
void verify_paper(void)

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    printf("==================================================================\n");
    printf("Verifying: Why the Golden Ratio Selects the Prime Three\n");
    printf("==================================================================\n");

    /* ── Theorem 1 ──────────────────────────────────────── */

    printf("\nTheorem 1: alignment(3m) = (2m-1)/(3m-1)\n");
    int t1_ok = 1;
    int ms[] = {1, 2, 4, 5, 8, 10, 16, 20, 25, 32};
    for (int i = 0; i < 10; i++) {
        int m = ms[i];
        int n = 3 * m;
        double computed  = alignment_exact(n, 10);
        double predicted = alignment_formula(m, 3);
        int ok = fabs(computed - predicted) < 1e-10;
        if (!ok) t1_ok = 0;
        printf("  m=%3d n=%3d  computed=%.6f  predicted=%.6f  %s\n",
               m, n, computed, predicted, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", t1_ok ? "PASS" : "FAIL");

    /* ── Theorem 2 ──────────────────────────────────────── */

    printf("\nTheorem 2: threshold at m >= phi^2 = %.6f\n", phi * phi);
    int t2_ok = 1;
    for (int m = 1; m <= 5; m++) {
        double val = alignment_formula(m, 3);
        int above    = val >= tau;
        int expected = m >= 3;
        int ok = (above == expected);
        if (!ok) t2_ok = 0;
        printf("  m=%d: alpha=%.6f  >= 1/phi: %d  expected: %d  %s\n",
               m, val, above, expected, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", t2_ok ? "PASS" : "FAIL");

    /* ── Theorem 3 ──────────────────────────────────────── */

    printf("\nTheorem 3: self-referential characterization\n");
    printf("  tau^2 + tau   = %.10f  (should be 1)\n", tau*tau + tau);
    printf("  tau^4         = %.10f\n", tau*tau*tau*tau);
    printf("  2 - 3*tau     = %.10f\n", 2.0 - 3.0*tau);
    printf("  tau^4 = 2-3t  : %s\n",
           fabs(tau*tau*tau*tau - (2.0-3.0*tau)) < 1e-14 ? "true" : "false");

    double poly = tau*tau*tau - tau*tau - 3.0*tau + 2.0;
    printf("  t^3-t^2-3t+2  = %.2e  (should be 0)\n", poly);

    printf("\n  Uniqueness (m* = 1/tau^2):\n");
    int primes[] = {2, 3, 5, 7};
    for (int i = 0; i < 4; i++) {
        int p = primes[i];
        double denom = 2.0 - p * tau;
        if (denom > 0) {
            double m_star = (1.0 - tau) / denom;
            int golden = fabs(m_star - phi*phi) < 1e-10;
            printf("    p=%d: m*=%.6f  golden: %s\n",
                   p, m_star, golden ? "yes" : "no");
        } else {
            printf("    p=%d: no solution (2-p*tau < 0)\n", p);
        }
    }

    /* ── Three-tier classification ──────────────────────── */

    printf("\nConjecture: three-tier classification (n <= 200)\n");
    int exceptions = 0;
    for (int n = 2; n <= 200; n++) {
        double a = alignment_exact(n, 10);
        if (a >= tau) {
            int smooth = is_b_smooth(n, 10);
            int tier2  = (n % 3 == 0) && is_b_smooth(n / 3, 10) && (n / 3 >= 4);
            if (!smooth && !tier2) {
                printf("  EXCEPTION: n=%d, alpha=%.6f\n", n, a);
                exceptions++;
            }
        }
    }
    if (exceptions == 0)
        printf("  No exceptions. Classification holds for n <= 200.\n");

    /* ── Base independence ──────────────────────────────── */

    printf("\nBase independence: checking bases where 3 is relevant\n");

    /* base 4: smooth = powers of 2.  base 10: 2^a*5^b.  base 16: powers of 2. */
    struct { int base; int ms[4]; } cases[] = {
        { 4,  {4, 8, 16, 32}},     /* 4-smooth: powers of 2 */
        {10,  {4, 5,  8, 10}},     /* 10-smooth: 2^a * 5^b  */
        {16,  {4, 8, 16, 32}},     /* 16-smooth: powers of 2 */
        {22,  {4, 8, 16, 32}},     /* 22=2*11, smooth: 2^a * 11^b, but use 2^a */
    };

    for (int bi = 0; bi < 4; bi++) {
        printf("  base %d:\n", cases[bi].base);
        for (int i = 0; i < 4; i++) {
            int m = cases[bi].ms[i];
            int n = 3 * m;
            double computed  = alignment_exact(n, cases[bi].base);
            double predicted = alignment_formula(m, 3);
            int ok = fabs(computed - predicted) < 1e-10;
            printf("    m=%2d n=%3d  computed=%.6f  predicted=%.6f  %s\n",
                   m, n, computed, predicted, ok ? "ok" : "FAIL");
        }
    }

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 2 verification ────────────────────────────────── */

static int is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int has_zero_cross_alignment(int p, int base)
{
    /* check if ALL k/p (k=2..p-1) have zero position-wise
       alignment with 1/p in the given base */
    Field f = field_build(p, base);
    int zero = 1;
    for (int i = 0; i < f.num_rows; i++) {
        if (f.rows[i].k == 1) continue;
        if (f.rows[i].alignment > 1e-12) {
            zero = 0;
            break;
        }
    }
    field_free(&f);
    return zero;
}

void verify_paper2(void)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    printf("==================================================================\n");
    printf("Verifying: Digit-Partitioning Primes and the Alignment Formula\n");
    printf("==================================================================\n");

    /* ── Theorem 1: characterization p <= b+1 ──────────── */

    printf("\nTheorem (characterization): p is DP iff p <= b+1\n");
    int t1_ok = 1;

    int bases[] = {4, 6, 8, 10, 12, 16, 20};
    int nbases = 7;

    for (int bi = 0; bi < nbases; bi++) {
        int base = bases[bi];
        printf("  base %d:\n", base);
        for (int p = 2; p <= base + 5; p++) {
            if (!is_prime(p)) continue;
            if (base % p == 0) continue;
            int dp = has_zero_cross_alignment(p, base);
            int predicted = (p <= base + 1);
            int ok = (dp == predicted);
            if (!ok) t1_ok = 0;
            printf("    p=%2d: dp=%d predicted=%d %s\n",
                   p, dp, predicted, ok ? "ok" : "FAIL");
        }
    }
    printf("  Result: %s\n", t1_ok ? "PASS" : "FAIL");

    /* ── Lemma: digit function δ(r)=r-1 when p=b+1 ────── */

    printf("\nLemma: delta(r) = r-1 when p = b+1\n");
    int t2_ok = 1;
    for (int bi = 0; bi < nbases; bi++) {
        int base = bases[bi];
        int p = base + 1;
        if (!is_prime(p)) continue;
        int ok = 1;
        for (int r = 1; r < p; r++) {
            int d = (base * r) / p;
            if (d != r - 1) { ok = 0; break; }
        }
        if (!ok) t2_ok = 0;
        printf("  base %d, p=%d: delta(r)=r-1 for all r: %s\n",
               base, p, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", t2_ok ? "PASS" : "FAIL");

    /* ── Universal alignment formula ───────────────────── */

    printf("\nTheorem (alignment): alpha(pm) = (2m-1)/(pm-1) for all DP primes\n");
    int t3_ok = 1;

    struct { int base; int p; int ms[4]; } cases[] = {
        { 4,  3, {4, 8, 16, 32}},
        { 4,  5, {4, 8, 16, 32}},
        {10,  3, {4, 5, 8, 10}},
        {10,  7, {2, 4, 5, 8}},
        {10, 11, {2, 4, 5, 8}},
        {12,  5, {4, 8, 12, 16}},
        {12,  7, {4, 8, 12, 16}},
        {12, 11, {4, 8, 12, 16}},
        {12, 13, {4, 8, 12, 16}},
        {16,  3, {4, 8, 16, 32}},
        {16,  7, {4, 8, 16, 32}},
        {16, 13, {4, 8, 16, 32}},
        {16, 17, {4, 8, 16, 32}},
    };
    int ncases = 13;

    for (int ci = 0; ci < ncases; ci++) {
        int base = cases[ci].base;
        int p    = cases[ci].p;
        printf("  base %d, p=%d:\n", base, p);
        for (int i = 0; i < 4; i++) {
            int m = cases[ci].ms[i];
            if (!is_b_smooth(m, base)) continue;
            int n = p * m;
            double computed  = alignment_exact(n, base);
            double predicted = alignment_formula(m, p);
            int ok = fabs(computed - predicted) < 1e-10;
            if (!ok) t3_ok = 0;
            printf("    m=%2d n=%3d  computed=%.6f  predicted=%.6f  %s\n",
                   m, n, computed, predicted, ok ? "ok" : "FAIL");
        }
    }
    printf("  Result: %s\n", t3_ok ? "PASS" : "FAIL");

    /* ── Golden ratio selects p=3 universally ──────────── */

    printf("\nGolden threshold: 2/p >= 1/phi only for p <= 3\n");
    printf("  1/phi = %.6f\n", tau);
    for (int p = 2; p <= 17; p++) {
        if (!is_prime(p)) continue;
        double limit = 2.0 / p;
        printf("  p=%2d: 2/p = %.4f  >= 1/phi: %s\n",
               p, limit, limit >= tau ? "yes" : "no");
    }

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}


void verify_paper3(void)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    printf("==================================================================\n");
    printf("Verifying: The Alignment Limit for All Primes\n");
    printf("==================================================================\n");

    int test_primes[] = {13, 17, 19, 23, 29, 31, 37, 41, 43, 47};
    int ntp = 10;

    /* ── Lemma: bin-sum formula ────────────────────────── */

    printf("\nLemma: S(p,b) = bq^2 + r(2q+1)\n");
    int s1_ok = 1;
    for (int i = 0; i < ntp; i++) {
        int p = test_primes[i];
        int b = 10;
        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;
        int S_actual = 0;
        for (int d = 0; d < b; d++)
            S_actual += bins[d] * bins[d];
        int q = (p - 1) / b;
        int rem = (p - 1) % b;
        int S_formula = b * q * q + rem * (2 * q + 1);
        int ok = (S_actual == S_formula);
        if (!ok) s1_ok = 0;
        printf("  p=%2d: S=%3d formula=%3d %s\n",
               p, S_actual, S_formula, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Alignment limit convergence ───────────────────── */

    printf("\nTheorem: limit = (L+T)/(pL)\n");
    int s2_ok = 1;
    for (int i = 0; i < ntp; i++) {
        int p = test_primes[i];
        int b = 10;
        int L = mult_order(b, p);
        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;
        int T = 0, r = 1;
        for (int j = 0; j < L; j++) {
            T += bins[(b * r) / p];
            r = (r * b) % p;
        }
        double lim = (double)(L + T) / ((double)p * L);
        double alpha = alignment_exact(p * 64, b);
        double diff = fabs(alpha - lim);
        int ok = (diff < 0.01);
        if (!ok) s2_ok = 0;
        printf("  p=%2d: limit=%.6f alpha(%dp)=%.6f diff=%.4f %s\n",
               p, lim, 64, alpha, diff, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    /* ── Golden bound ──────────────────────────────────── */

    printf("\nTheorem: L(p) < 1/phi for all p >= 5\n");
    printf("  1/phi = %.6f\n", tau);
    int s3_ok = 1;
    for (int p = 3; p <= 47; p++) {
        if (!is_prime(p)) continue;
        if (p == 5) continue;
        int b = 10;
        int L = mult_order(b, p);
        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;
        int T = 0, r = 1;
        for (int j = 0; j < L; j++) {
            T += bins[(b * r) / p];
            r = (r * b) % p;
        }
        double lim = (double)(L + T) / ((double)p * L);
        if (p >= 5 && lim >= tau) {
            s3_ok = 0;
            printf("  p=%2d: %.6f >= 1/phi  FAIL\n", p, lim);
        } else {
            printf("  p=%2d: %.6f  %s\n", p, lim,
                   p == 3 ? ">= 1/phi (expected)" : "< 1/phi");
        }
    }
    printf("  Result: %s\n", s3_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

void verify_paper5(void)
{
    double phi = (1.0 + sqrt(5.0)) / 2.0;
    double tau = 1.0 / phi;

    printf("==================================================================\n");
    printf("Verifying: The Coherence Decomposition\n");
    printf("==================================================================\n");

    /* ── Decomposition formulas for DP primes ──────────── */

    printf("\nTheorem: alpha=(2s-1)/(ps-1), F=s/(ps-1), sigma=(s-1)/(ps-1)\n");
    int s1_ok = 1;

    int primes[] = {3, 7, 11};
    int smooth[] = {1, 2, 4, 5, 8};

    for (int pi = 0; pi < 3; pi++) {
        int p = primes[pi];
        printf("  p=%d:\n", p);
        for (int si = 0; si < 5; si++) {
            int s = smooth[si];
            int n = p * s;

            double a = alignment_exact(n, 10);
            double sig = sigma_exact(n, 10);
            double F = a - sig;

            double a_pred = (2.0*s - 1) / ((double)p*s - 1);
            double F_pred = (double)s / ((double)p*s - 1);
            double s_pred = (double)(s-1) / ((double)p*s - 1);

            int ok_a = fabs(a - a_pred) < 1e-4;
            int ok_F = fabs(F - F_pred) < 1e-4;
            int ok_s = fabs(sig - s_pred) < 1e-4;
            if (!ok_a || !ok_F || !ok_s) s1_ok = 0;

            printf("    s=%d: a=%.4f/%.4f F=%.4f/%.4f sig=%.4f/%.4f %s\n",
                   s, a, a_pred, F, F_pred, sig, s_pred,
                   (ok_a && ok_F && ok_s) ? "ok" : "FAIL");
        }
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Golden gap ────────────────────────────────────── */

    printf("\nTheorem: 1/phi in gap (1/p, 2/p) iff p=3\n");
    printf("  1/phi = %.6f\n", tau);
    for (int p = 3; p <= 13; p += 2) {
        if (p == 5 || p == 9) continue;
        int in_gap = (1.0/p < tau) && (tau < 2.0/p);
        printf("  p=%2d: F_lim=1/%d=%.4f  a_lim=2/%d=%.4f  in_gap=%s\n",
               p, p, 1.0/p, p, 2.0/p, in_gap ? "yes" : "no");
    }

    /* ── Sigma-zero characterization ───────────────────── */

    printf("\nProposition: sigma(p) = 0 iff p <= b+1\n");
    int s2_ok = 1;
    for (int p = 3; p <= 19; p++) {
        if (!is_prime(p)) continue;
        if (p == 5) continue;
        double sig = sigma_exact(p, 10);
        int is_dp = (p <= 11);
        int sig_zero = (sig < 1e-10);
        int ok = (sig_zero == is_dp);
        if (!ok) s2_ok = 0;
        printf("  p=%2d: sigma=%.6f  dp=%d  sigma_zero=%d  %s\n",
               p, sig, is_dp, sig_zero, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

void verify_paper8(void)
{
    printf("==================================================================\n");
    printf("Verifying: The Spectral Power of the Digit Function\n");
    printf("==================================================================\n");

    /* ── Phi(0) = S(p,b) ──────────────────────────────── */

    printf("\nCorollary: Phi(0) = S(p,b) = bq^2 + r(2q+1)\n");
    int s1_ok = 1;

    int test_primes[] = {7, 11, 13, 17, 19, 23, 29, 37, 41};
    int ntp = 9;

    for (int i = 0; i < ntp; i++) {
        int p = test_primes[i];
        int b = 10;

        /* Phi(0) = sum n_d^2 */
        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;
        int phi0 = 0;
        for (int d = 0; d < b; d++)
            phi0 += bins[d] * bins[d];

        /* S formula */
        int q = (p - 1) / b;
        int rem = (p - 1) % b;
        int S = b * q * q + rem * (2 * q + 1);

        int ok = (phi0 == S);
        if (!ok) s1_ok = 0;
        printf("  p=%2d: Phi(0)=%3d S=%3d %s\n", p, phi0, S, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Parseval: sum Phi(k) = p(p-1) ────────────────── */

    printf("\nParseval: sum Phi(k) = p(p-1)\n");
    int s2_ok = 1;

    for (int i = 0; i < ntp; i++) {
        int p = test_primes[i];
        int b = 10;

        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;

        double total = 0.0;
        for (int k = 0; k < p; k++) {
            if (k == 0) {
                for (int d = 0; d < b; d++)
                    total += (double)bins[d] * bins[d];
            } else {
                for (int d = 0; d < b; d++) {
                    int nd = bins[d];
                    if (nd == 0) continue;
                    double num = sin(M_PI * k * nd / (double)p);
                    double den = sin(M_PI * k / (double)p);
                    total += (num / den) * (num / den);
                }
            }
        }

        int expected = p * (p - 1);
        int ok = fabs(total - expected) < 0.5;
        if (!ok) s2_ok = 0;
        printf("  p=%2d: sum=%.1f expected=%d %s\n",
               p, total, expected, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    /* ── Dirichlet kernel matches exact DFT ───────────── */

    printf("\nTheorem: Phi(k) = sum |sin(pi*k*nd/p)/sin(pi*k/p)|^2\n");
    int s3_ok = 1;

    for (int i = 0; i < 5; i++) {
        int p = test_primes[i];
        int b = 10;

        int bins_arr[64] = {0};
        for (int r = 1; r < p; r++)
            bins_arr[(b * r) / p]++;

        /* exact Phi via DFT */
        int ok_all = 1;
        for (int k = 1; k < p; k++) {
            /* exact: sum_d |sum_{r in bin(d)} e^{-2pi*i*k*r/p}|^2 */
            double exact = 0.0;
            for (int d = 0; d < b; d++) {
                double re = 0.0, im = 0.0;
                for (int r = 1; r < p; r++) {
                    if ((b * r) / p != d) continue;
                    double angle = -2.0 * M_PI * k * r / p;
                    re += cos(angle);
                    im += sin(angle);
                }
                exact += re * re + im * im;
            }

            /* formula */
            double formula = 0.0;
            for (int d = 0; d < b; d++) {
                int nd = bins_arr[d];
                if (nd == 0) continue;
                double num = sin(M_PI * k * nd / (double)p);
                double den = sin(M_PI * k / (double)p);
                formula += (num / den) * (num / den);
            }

            if (fabs(exact - formula) > 0.01) {
                ok_all = 0;
                s3_ok = 0;
                printf("  p=%d k=%d: exact=%.4f formula=%.4f FAIL\n",
                       p, k, exact, formula);
            }
        }
        if (ok_all)
            printf("  p=%2d: all k match  ok\n", p);
    }
    printf("  Result: %s\n", s3_ok ? "PASS" : "FAIL");

    /* ── DP primes: flat spectrum ─────────────────────── */

    printf("\nDP primes: Phi(k) = p-1 for all k\n");
    int s4_ok = 1;
    int dp_primes[] = {3, 7, 11};
    for (int i = 0; i < 3; i++) {
        int p = dp_primes[i];
        int b = 10;
        int bins_arr[64] = {0};
        for (int r = 1; r < p; r++)
            bins_arr[(b * r) / p]++;

        int flat = 1;
        for (int k = 1; k < p; k++) {
            double phi_k = 0.0;
            for (int d = 0; d < b; d++) {
                int nd = bins_arr[d];
                if (nd == 0) continue;
                double num = sin(M_PI * k * nd / (double)p);
                double den = sin(M_PI * k / (double)p);
                phi_k += (num / den) * (num / den);
            }
            if (fabs(phi_k - (p - 1)) > 0.01) flat = 0;
        }
        if (!flat) s4_ok = 0;
        printf("  p=%2d: flat spectrum: %s\n", p, flat ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s4_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        printf("Usage: verify_papers1_8 <1|2|3|5|8|all>\n");
        return 1;
    }
    if (strcmp(argv[1], "1") == 0 || strcmp(argv[1], "all") == 0) verify_paper();
    if (strcmp(argv[1], "2") == 0 || strcmp(argv[1], "all") == 0) verify_paper2();
    if (strcmp(argv[1], "3") == 0 || strcmp(argv[1], "all") == 0) verify_paper3();
    if (strcmp(argv[1], "5") == 0 || strcmp(argv[1], "all") == 0) verify_paper5();
    if (strcmp(argv[1], "8") == 0 || strcmp(argv[1], "all") == 0) verify_paper8();
    return 0;
}
