/*
 * verify.c: Verification of published theorems.
 *
 * Verifies the computational claims in:
 *   Paper A: The Collision Invariant (arXiv:2604.00045)
 *   Paper B: The Collision Transform (arXiv:2604.00047)
 *   Paper C: The Collision Spectrum (arXiv:2604.00054)
 *   Paper E: The Collision Prime Number Theorem
 *   Paper F: The Polarity Field and Zero Avoidance
 *
 * Usage:
 *   nfield verify <theorem>
 *   nfield verify all
 *
 * Theorem names:
 *   gate-width         Exactly b-1 deranging multipliers (Paper A)
 *   mobius-family       Deranging set = {-u/(b-u) mod p} (Paper A)
 *   sum-rule           Sum of C(g) = S(p,b) (Paper A)
 *   mean-formula       Mean collision count over constructive g (Paper A)
 *   finite-det         S depends only on p mod b^2 (Paper A)
 *   antisymmetry       S(a) + S(b^2-a) = -1 (Paper A/E)
 *   mean-half          Mean of S over units = -1/2 (Paper A/E)
 *   all                Run all verifications
 *
 * 2026 Alexander S. Petty
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "../src/nfield.h"

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

static int is_prime(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int mod_inverse(int a, int p) {
    int g = p, x = 0, y = 1;
    int ta = a;
    while (ta != 0) {
        int q = g / ta;
        int t = g - q * ta; g = ta; ta = t;
        t = x - q * y; x = y; y = t;
    }
    return ((x % p) + p) % p;
}

static int collision_count(int g, int p, int b) {
    int C = 0;
    for (int r = 1; r < p; r++) {
        int gr = (int)(((long long)g * r) % p);
        if (gr == 0) continue;
        if ((b * r) / p == (b * gr) / p)
            C++;
    }
    return C;
}

static int power_mod(int base, int exp, int mod) {
    long long result = 1, b = base % mod;
    while (exp > 0) {
        if (exp & 1) result = result * b % mod;
        b = b * b % mod;
        exp >>= 1;
    }
    return (int)result;
}

/* ── Gate Width Theorem ───────────────────────────────── */

static int verify_gate_width(void)
{
    printf("Gate Width Theorem (Paper A)\n");
    printf("  Claim: exactly b-1 deranging multipliers for every prime p > b\n\n");

    int primes[] = {7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                    53, 59, 61, 67, 71, 73, 79, 83, 89, 97};
    int np = 21;
    int bases[] = {3, 7, 10, 12, 16};
    int nb = 5;
    int all_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int pass = 1;
        int tested = 0;
        for (int ti = 0; ti < np; ti++) {
            int p = primes[ti];
            if (p % b == 0 || p <= b) continue;
            tested++;

            int deranging = 0;
            for (int g = 1; g < p; g++)
                if (collision_count(g, p, b) == 0)
                    deranging++;

            if (deranging != b - 1) {
                pass = 0;
                printf("  FAIL: base %d, p=%d: %d deranging (expected %d)\n",
                       b, p, deranging, b - 1);
            }
        }
        printf("  base %2d: %d primes tested, gate width = %d  %s\n",
               b, tested, b - 1, pass ? "PASS" : "FAIL");
        if (!pass) all_ok = 0;
    }
    return all_ok;
}

/* ── Mobius Family ────────────────────────────────────── */

static int verify_mobius_family(void)
{
    printf("Mobius Family (Paper A)\n");
    printf("  Claim: deranging set = {-u/(b-u) mod p : u=1..b-1}\n\n");

    int primes[] = {13, 17, 29, 37, 41, 53, 61, 73, 89, 97};
    int np = 10;
    int bases[] = {7, 10, 12};
    int nb = 3;
    int all_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int pass = 1;
        for (int ti = 0; ti < np; ti++) {
            int p = primes[ti];
            if (p % b == 0 || p <= b) continue;

            /* observed deranging set */
            int *obs = calloc(p, sizeof(int));
            for (int g = 1; g < p; g++)
                if (collision_count(g, p, b) == 0)
                    obs[g] = 1;

            /* predicted: g = -u/(b-u) mod p */
            int *pred = calloc(p, sizeof(int));
            for (int u = 1; u < b; u++) {
                int bu = ((b - u) % p + p) % p;
                if (bu == 0) continue;
                int inv = mod_inverse(bu, p);
                int g = (int)(((long long)(p - u) % p * inv) % p);
                g = ((g % p) + p) % p;
                if (g > 0 && g < p)
                    pred[g] = 1;
            }

            for (int g = 1; g < p; g++) {
                if (obs[g] != pred[g]) {
                    pass = 0;
                    printf("  FAIL: base %d, p=%d, g=%d: obs=%d pred=%d\n",
                           b, p, g, obs[g], pred[g]);
                    break;
                }
            }
            free(obs);
            free(pred);
        }
        printf("  base %2d: formula matches observed  %s\n", b,
               pass ? "PASS" : "FAIL");
        if (!pass) all_ok = 0;
    }
    return all_ok;
}

/* ── Sum Rule ─────────────────────────────────────────── */

static int verify_sum_rule(void)
{
    printf("Sum Rule (Paper A)\n");
    printf("  Claim: sum_{g=1}^{p-1} C(g) = S(p,b) = sum n_d^2\n\n");

    int primes[] = {13, 17, 29, 37, 41, 53, 61, 73, 89, 97};
    int np = 10;
    int b = 10;
    int all_ok = 1;

    for (int ti = 0; ti < np; ti++) {
        int p = primes[ti];

        int sum_C = 0;
        for (int g = 1; g < p; g++)
            sum_C += collision_count(g, p, b);

        int bins[64] = {0};
        for (int r = 1; r < p; r++)
            bins[(b * r) / p]++;
        int S = 0;
        for (int d = 0; d < b; d++)
            S += bins[d] * bins[d];

        int ok = (sum_C == S);
        if (!ok) {
            printf("  FAIL: p=%d: sum=%d S=%d\n", p, sum_C, S);
            all_ok = 0;
        }
    }
    if (all_ok)
        printf("  base %d: all primes satisfy sum rule  PASS\n", b);
    return all_ok;
}

/* ── Mean Formula ─────────────────────────────────────── */

static int verify_mean_formula(void)
{
    printf("Mean Collision Count (Paper A)\n");
    printf("  Claim: mean C(g) over constructive g = Q(b(Q-1)+2R)/(b(Q-1)+R)\n\n");

    int primes[] = {17, 29, 37, 53, 61, 97, 131, 179, 193};
    int np = 9;
    int b = 10;
    int all_ok = 1;

    for (int ti = 0; ti < np; ti++) {
        int p = primes[ti];
        if (p <= b + 1) continue;
        int Q = (p - 1) / b;
        int R = (p - 1) % b;

        int n_constr = 0;
        double sum_constr = 0.0;
        for (int g = 2; g < p; g++) {
            int C = collision_count(g, p, b);
            if (C > 0) {
                n_constr++;
                sum_constr += C;
            }
        }

        double predicted = (double)Q * (b * (Q - 1) + 2 * R)
                         / (double)(b * (Q - 1) + R);
        double actual = n_constr > 0 ? sum_constr / n_constr : 0.0;
        int ok = fabs(actual - predicted) < 0.01;
        printf("  p=%3d Q=%2d R=%d: actual=%.4f predicted=%.4f  %s\n",
               p, Q, R, actual, predicted, ok ? "ok" : "FAIL");
        if (!ok) all_ok = 0;
    }
    printf("  Result: %s\n", all_ok ? "PASS" : "FAIL");
    return all_ok;
}

/* ── Finite Determination ─────────────────────────────── */

static int verify_finite_det(void)
{
    printf("Finite Determination (Paper A)\n");
    printf("  Claim: S(p) depends only on p mod b^2\n\n");

    int bases[] = {3, 5, 7, 10};
    int nb = 4;
    int all_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;

        int s_first[256];
        int s_seen[256];
        memset(s_seen, 0, sizeof(s_seen));
        int varies = 0;

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;

            int C = collision_count(power_mod(b, 1, p), p, b);
            int S = C - (p - 1) / b;
            int cls = p % m;

            if (!s_seen[cls]) {
                s_first[cls] = S;
                s_seen[cls] = 1;
            } else if (S != s_first[cls]) {
                varies++;
            }
        }

        int ok = (varies == 0);
        printf("  base %2d, mod %3d: %s\n", b, m,
               ok ? "DETERMINED  PASS" : "FAIL");
        if (!ok) all_ok = 0;
    }
    return all_ok;
}

/* ── Antisymmetry ─────────────────────────────────────── */

static int verify_antisymmetry(void)
{
    printf("Antisymmetry (Papers A, E)\n");
    printf("  Claim: S(a) + S(b^2 - a) = -1 for all coprime a\n\n");

    int bases[] = {3, 5, 7, 10};
    int nb = 4;
    int all_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;

        int s_val[256];
        int s_known[256];
        memset(s_known, 0, sizeof(s_known));

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;
            int cls = p % m;
            if (s_known[cls]) continue;

            int C = collision_count(power_mod(b, 1, p), p, b);
            s_val[cls] = C - (p - 1) / b;
            s_known[cls] = 1;
        }

        int ok = 1;
        for (int a = 1; a < m; a++) {
            int a2 = m - a;
            if (!s_known[a] || !s_known[a2]) continue;
            /* check coprime */
            int ga = a, ha = m;
            while (ha) { int t = ha; ha = ga % ha; ga = t; }
            if (ga != 1) continue;

            if (s_val[a] + s_val[a2] != -1) {
                printf("  FAIL: base %d, S(%d)+S(%d) = %d\n",
                       b, a, a2, s_val[a] + s_val[a2]);
                ok = 0;
            }
        }
        printf("  base %2d: S(a)+S(m-a) = -1  %s\n", b,
               ok ? "PASS" : "FAIL");
        if (!ok) all_ok = 0;
    }
    return all_ok;
}

/* ── Mean = -1/2 ──────────────────────────────────────── */

static int verify_mean_half(void)
{
    printf("Mean = -1/2 (Papers A, E)\n");
    printf("  Claim: average of S over coprime classes = -1/2\n\n");

    int bases[] = {3, 5, 7, 10};
    int nb = 4;
    int all_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;

        int s_val[256];
        int s_known[256];
        memset(s_known, 0, sizeof(s_known));

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;
            int cls = p % m;
            if (s_known[cls]) continue;

            int C = collision_count(power_mod(b, 1, p), p, b);
            s_val[cls] = C - (p - 1) / b;
            s_known[cls] = 1;
        }

        double sum = 0;
        int count = 0;
        for (int a = 1; a < m; a++) {
            if (!s_known[a]) continue;
            int ga = a, ha = m;
            while (ha) { int t = ha; ha = ga % ha; ga = t; }
            if (ga != 1) continue;
            sum += s_val[a];
            count++;
        }
        double avg = sum / count;
        int ok = fabs(avg - (-0.5)) < 0.001;
        printf("  base %2d: mean = %.6f  %s\n", b, avg,
               ok ? "PASS" : "FAIL");
        if (!ok) all_ok = 0;
    }
    return all_ok;
}

/* ── Dispatch ─────────────────────────────────────────── */

static void usage(void)
{
    printf(
        "nfield verify: verify published theorems\n\n"
        "Usage: nfield verify <theorem>\n\n"
        "Theorems:\n"
        "  gate-width      Exactly b-1 deranging multipliers (Paper A)\n"
        "  mobius-family    Deranging set = {-u/(b-u) mod p} (Paper A)\n"
        "  sum-rule         Sum of C(g) = S(p,b) (Paper A)\n"
        "  mean-formula     Mean collision count formula (Paper A)\n"
        "  finite-det       S depends only on p mod b^2 (Paper A)\n"
        "  antisymmetry     S(a) + S(b^2-a) = -1 (Papers A, E)\n"
        "  mean-half        Mean of S over units = -1/2 (Papers A, E)\n"
        "  all              Run all verifications\n"
    );
}

int verify_dispatch(const char *name)
{
    int total = 0, passed = 0;

    typedef struct { const char *name; int (*fn)(void); } entry;
    entry tests[] = {
        {"gate-width",    verify_gate_width},
        {"mobius-family",  verify_mobius_family},
        {"sum-rule",      verify_sum_rule},
        {"mean-formula",  verify_mean_formula},
        {"finite-det",    verify_finite_det},
        {"antisymmetry",  verify_antisymmetry},
        {"mean-half",     verify_mean_half},
    };
    int n = sizeof(tests) / sizeof(tests[0]);

    int run_all = strcmp(name, "all") == 0;

    for (int i = 0; i < n; i++) {
        if (run_all || strcmp(name, tests[i].name) == 0) {
            printf("\n");
            printf("============================================================\n");
            int ok = tests[i].fn();
            printf("============================================================\n");
            total++;
            if (ok) passed++;
        }
    }

    if (total == 0) {
        usage();
        return 1;
    }

    printf("\n%d/%d verifications passed.\n", passed, total);
    return passed == total ? 0 : 1;
}
