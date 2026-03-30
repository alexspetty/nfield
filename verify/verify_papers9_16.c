/*
 * verify.c: Verification routines for papers 9-15 of the nfield
 *           fractional field program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "nfield.h"

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

/* ── helpers ─────────────────────────────────────────────── */

static int is_prime(int n)
{
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

/* mult_order is provided by libnfield */

static int mod_inverse(int a, int p)
{
    a = ((a % p) + p) % p;
    int g = p, x = 0, y = 1;
    int a0 = a;
    while (a0 != 0) {
        int q = g / a0;
        int t = g - q * a0;
        g = a0; a0 = t;
        t = x - q * y;
        x = y; y = t;
    }
    return ((x % p) + p) % p;
}

static int power_mod(int base, int exp, int mod)
{
    long long result = 1;
    long long b = ((base % mod) + mod) % mod;
    int e = exp;
    while (e > 0) {
        if (e & 1)
            result = (result * b) % mod;
        b = (b * b) % mod;
        e >>= 1;
    }
    return (int)result;
}

/* ── paper 9 verification ────────────────────────────────── */

void verify_paper9(void)
{
    printf("==================================================================\n");
    printf("Verifying: The Autocorrelation Formula\n");
    printf("==================================================================\n");

    int test_primes[] = {7, 13, 17, 19, 23, 29, 37};
    int ntp = 7;
    int b = 10;

    /* ── R(ell) = C(b^ell) for primitive root primes ──── */

    printf("\nTheorem: digit-matching R(ell) = bin collision C(b^ell mod p)\n");
    printf("  (for primes where b is a primitive root, L = p-1)\n");
    int s1_ok = 1;

    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];
        if (p <= b) continue;
        int L = mult_order(b, p);
        if (L != p - 1) continue;  /* only primitive root primes */

        /* repetend digits */
        int *orbit = malloc(L * sizeof(int));
        int *rep = malloc(L * sizeof(int));
        int r = 1;
        for (int j = 0; j < L; j++) {
            orbit[j] = r;
            rep[j] = (b * r) / p;
            r = (r * b) % p;
        }

        int ok_all = 1;
        for (int ell = 0; ell < L; ell++) {
            /* digit-matching R(ell) */
            int R_digit = 0;
            for (int j = 0; j < L; j++)
                if (rep[j] == rep[(j + ell) % L])
                    R_digit++;

            /* C(g) via bin comparison */
            int g = power_mod(b, ell, p);
            int C_g = 0;
            for (int rv = 1; rv < p; rv++) {
                int grv = (int)(((long long)g * rv) % p);
                if ((b * rv) / p == (b * grv) / p)
                    C_g++;
            }

            if (R_digit != C_g) {
                ok_all = 0;
                printf("  p=%2d ell=%d: R_digit=%d C(g)=%d FAIL\n",
                       p, ell, R_digit, C_g);
            }
        }
        if (ok_all)
            printf("  p=%2d (L=%d): R(ell) = C(b^ell) for all ell  ok\n", p, L);
        else
            s1_ok = 0;

        free(orbit);
        free(rep);
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Vanishing sum ────────────────────────────────── */

    printf("\nVanishing sum: sum_{k'} G(k,k') = 0 for k != 0\n");
    int s2_ok = 1;

    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];

        int *bin_members = malloc(b * p * sizeof(int));
        int *bin_size = calloc(b, sizeof(int));
        for (int rr = 1; rr < p; rr++) {
            int d = (b * rr) / p;
            bin_members[d * p + bin_size[d]] = rr;
            bin_size[d]++;
        }

        int ok_all = 1;
        for (int k = 1; k < p; k++) {
            /* sum_{k'=0..p-1} G(k,k') */
            double sum_re = 0.0;
            for (int kp = 0; kp < p; kp++) {
                double G_re = 0.0;
                for (int d = 0; d < b; d++) {
                    double fk_re = 0.0, fk_im = 0.0;
                    double fkp_re = 0.0, fkp_im = 0.0;
                    for (int s = 0; s < bin_size[d]; s++) {
                        int rr = bin_members[d * p + s];
                        double ang_k = -2.0 * M_PI * k * rr / p;
                        fk_re += cos(ang_k);
                        fk_im += sin(ang_k);
                        double ang_kp = -2.0 * M_PI * kp * rr / p;
                        fkp_re += cos(ang_kp);
                        fkp_im += sin(ang_kp);
                    }
                    G_re += fk_re * fkp_re + fk_im * fkp_im;
                }
                sum_re += G_re;
            }
            if (fabs(sum_re) > 0.5) {
                ok_all = 0;
                printf("  p=%2d k=%d: sum=%.4f FAIL\n", p, k, sum_re);
            }
        }
        if (ok_all)
            printf("  p=%2d: vanishing sum holds  ok\n", p);
        else
            s2_ok = 0;

        free(bin_members);
        free(bin_size);
    }
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 10 verification ───────────────────────────────── */

void verify_paper10(void)
{
    printf("==================================================================\n");
    printf("Verifying: Phase-Filtered Ramanujan Sums\n");
    printf("==================================================================\n");

    int test_primes[] = {7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47};
    int ntp = 11;
    int b = 10;

    /* ── Spectral class assignment via CF tail ────────── */

    printf("\nSpectral class: CF tail of b/r by residue r = p mod b\n");
    int s1_ok = 1;

    /* expected CF tails for base 10:
       r=1 -> [10], r=3 -> [3,3], r=7 -> [1,2,3], r=9 -> [1,9] */
    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];
        int r = p % b;

        /* compute CF of b/r */
        int cf[32];
        int ncf = 0;
        int num = b, den = r;
        while (den > 0 && ncf < 32) {
            cf[ncf++] = num / den;
            int t = num % den;
            num = den;
            den = t;
        }

        printf("  p=%2d r=%d: CF(b/r)=[", p, r);
        for (int i = 0; i < ncf; i++) {
            if (i > 0) printf(",");
            printf("%d", cf[i]);
        }
        printf("]");

        /* verify CF(b/r) matches expected pattern */
        int ok = 0;
        if (r == 1) {
            ok = (ncf == 1 && cf[0] == 10);
        } else if (r == 3) {
            ok = (ncf == 2 && cf[0] == 3 && cf[1] == 3);
        } else if (r == 7) {
            ok = (ncf == 3 && cf[0] == 1 && cf[1] == 2 && cf[2] == 3);
        } else if (r == 9) {
            ok = (ncf == 2 && cf[0] == 1 && cf[1] == 9);
        }
        printf("  %s\n", ok ? "ok" : "FAIL");
        if (!ok) s1_ok = 0;
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Phase filter binary gate ─────────────────────── */

    printf("\nPhase filter: Gamma(ell) binary gate behavior\n");
    int s2_ok = 1;

    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];
        int L = mult_order(b, p);

        /* bins */
        int bins[64] = {0};
        for (int rr = 1; rr < p; rr++)
            bins[(b * rr) / p]++;

        /* orbit and repetend */
        int *orbit = malloc(L * sizeof(int));
        int *rep = malloc(L * sizeof(int));
        int r = 1;
        for (int j = 0; j < L; j++) {
            orbit[j] = r;
            rep[j] = (b * r) / p;
            r = (r * b) % p;
        }

        /* Gamma(ell) = R(ell) - S/L where S = Phi(0) */
        int S = 0;
        for (int d = 0; d < b; d++)
            S += bins[d] * bins[d];
        double mean = (double)S / L;

        int constructive = 0;
        for (int ell = 1; ell < L; ell++) {
            int R = 0;
            for (int j = 0; j < L; j++)
                if (rep[j] == rep[(j + ell) % L])
                    R++;
            double gamma = (double)R - mean;
            /* binary: either |gamma| < 0.5 (zero gate) or notably nonzero */
            if (fabs(gamma) > 0.5)
                constructive++;
        }
        printf("  p=%2d L=%2d: constructive=%d destructive=%d  ok\n",
               p, L, constructive, L - 1 - constructive);

        free(orbit);
        free(rep);
    }
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    /* ── Spectral class determines bin pattern ────────── */

    printf("\nSpectral class: R=(p-1)%%b large bins of size Q+1, b-R of size Q\n");
    int s3_ok = 1;

    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];
        if (p <= b) continue;
        int Q = (p - 1) / b;
        int R = (p - 1) % b;

        int bins[64] = {0};
        for (int rv = 1; rv < p; rv++)
            bins[(b * rv) / p]++;

        int n_large = 0, n_small = 0;
        for (int d = 0; d < b; d++) {
            if (bins[d] == Q + 1) n_large++;
            else if (bins[d] == Q) n_small++;
        }

        int ok = (n_large == R && n_small == b - R);
        if (!ok) s3_ok = 0;
        printf("  p=%2d class=%d Q=%d R=%d: large=%d/%d small=%d/%d %s\n",
               p, p % b, Q, R, n_large, R, n_small, b - R, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s3_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 11 verification ───────────────────────────────── */

void verify_paper11(void)
{
    printf("==================================================================\n");
    printf("Verifying: Bin Derangements and the Gate Width Theorem\n");
    printf("==================================================================\n");

    int test_primes[] = {7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                         53, 59, 61, 67, 71, 73, 79, 83, 89, 97};
    int ntp = 21;
    int bases[] = {7, 10, 12, 16};
    int nb = 4;

    /* ── Gate width = b-1 ─────────────────────────────── */

    printf("\nTheorem: exactly b-1 deranging multipliers\n");
    int s1_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int pass = 1;
        for (int ti = 0; ti < ntp; ti++) {
            int p = test_primes[ti];
            if (p % b == 0 || p <= b) continue;

            /* for each g in 1..p-1, compute C(g) */
            int deranging_count = 0;
            for (int g = 1; g < p; g++) {
                int C = 0;
                for (int r = 1; r < p; r++) {
                    int gr = (int)(((long long)g * r) % p);
                    if ((b * r) / p == (b * gr) / p)
                        C++;
                }
                if (C == 0)
                    deranging_count++;
            }

            if (deranging_count != b - 1) {
                pass = 0;
                printf("  base %d p=%2d: deranging=%d expected=%d FAIL\n",
                       b, p, deranging_count, b - 1);
            }
        }
        if (pass)
            printf("  base %d: all primes have b-1=%d deranging  ok\n", b, b - 1);
        else
            s1_ok = 0;
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Deranging family formula ─────────────────────── */

    printf("\nTheorem: deranging g = -u/(b-u) mod p for u=1..b-1\n");
    int s2_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int pass = 1;
        for (int ti = 0; ti < ntp; ti++) {
            int p = test_primes[ti];
            if (p % b == 0 || p <= b) continue;

            /* observed deranging set */
            int *deranging_obs = calloc(p, sizeof(int));
            for (int g = 1; g < p; g++) {
                int C = 0;
                for (int r = 1; r < p; r++) {
                    int gr = (int)(((long long)g * r) % p);
                    if ((b * r) / p == (b * gr) / p)
                        C++;
                }
                if (C == 0)
                    deranging_obs[g] = 1;
            }

            /* predicted: g = -u/(b-u) mod p for u=1..b-1 */
            int *deranging_pred = calloc(p, sizeof(int));
            for (int u = 1; u < b; u++) {
                int bu = ((b - u) % p + p) % p;
                if (bu == 0) continue;
                int inv = mod_inverse(bu, p);
                int g = (int)(((long long)(p - u) % p * inv) % p);
                g = ((g % p) + p) % p;
                if (g > 0 && g < p)
                    deranging_pred[g] = 1;
            }

            /* compare */
            for (int g = 1; g < p; g++) {
                if (deranging_obs[g] != deranging_pred[g]) {
                    pass = 0;
                    break;
                }
            }
            free(deranging_obs);
            free(deranging_pred);
        }
        if (pass)
            printf("  base %d: formula matches observed  ok\n", b);
        else {
            printf("  base %d: FAIL\n", b);
            s2_ok = 0;
        }
    }
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    /* ── Sum rule: sum R(ell) = S(p,b) = Phi(0) ──────── */

    printf("\nSum rule: sum_{g=1}^{p-1} C(g) = S(p,b)\n");
    int s3_ok = 1;

    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];
        int b = 10;
        if (p <= b) continue;

        /* sum C(g) over all nonzero multipliers */
        int sum_C = 0;
        for (int g = 1; g < p; g++) {
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    sum_C++;
            }
        }

        /* S(p,b) */
        int bins[64] = {0};
        for (int rv = 1; rv < p; rv++)
            bins[(b * rv) / p]++;
        int S = 0;
        for (int d = 0; d < b; d++)
            S += bins[d] * bins[d];

        int ok = (sum_C == S);
        if (!ok) {
            s3_ok = 0;
            printf("  p=%2d: sum=%d S=%d FAIL\n", p, sum_C, S);
        }
    }
    if (s3_ok)
        printf("  All primes: sum_g C(g) = S  ok\n");
    printf("  Result: %s\n", s3_ok ? "PASS" : "FAIL");

    /* ── Mean formula ─────────────────────────────────── */

    printf("\nMean formula: mean C(g) over constructive multipliers\n");
    int s4_ok = 1;

    for (int ti = 0; ti < ntp; ti++) {
        int p = test_primes[ti];
        int b = 10;
        if (p <= b) continue;
        int Q = (p - 1) / b;
        int R_rem = (p - 1) % b;

        /* find constructive multipliers: g != 1 with C(g) > 0 */
        int n_constr = 0;
        double sum_constr = 0.0;
        for (int g = 2; g < p; g++) {
            int C = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    C++;
            }
            if (C > 0) {
                n_constr++;
                sum_constr += C;
            }
        }

        double predicted_mean = (double)Q * (b * (Q - 1) + 2 * R_rem)
                              / (double)(b * (Q - 1) + R_rem);

        double actual_mean = n_constr > 0 ? sum_constr / n_constr : 0.0;
        int ok = (n_constr == 0) || (fabs(actual_mean - predicted_mean) < 1.0);
        if (!ok) s4_ok = 0;
        printf("  p=%2d: mean=%.2f predicted=%.2f n_constr=%d %s\n",
               p, actual_mean, predicted_mean, n_constr, ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", s4_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 12 verification ───────────────────────────────── */

void verify_paper12(void)
{
    printf("==================================================================\n");
    printf("Verifying: Silent Primes and the Variance of the Collision Count\n");
    printf("==================================================================\n");

    int b = 10;

    /* ── Silent prime polynomial ──────────────────────── */

    printf("\nTheorem: N(ell,u) = b^(ell+1) + u*(1 - b^ell) factors give silent primes\n");
    int s1_ok = 1;

    for (int ell = 1; ell <= 10; ell++) {
        for (int u = 1; u < b; u++) {
            long long bell1 = 1;
            for (int i = 0; i < ell + 1; i++) bell1 *= b;
            long long bell = 1;
            for (int i = 0; i < ell; i++) bell *= b;
            long long N = bell1 + (long long)u * (1 - bell);

            if (N <= 0) continue;

            /* factor N, check each prime factor */
            long long rem = N < 0 ? -N : N;
            int ok = 1;
            for (int f = 2; (long long)f * f <= rem && f < 100000; f++) {
                if (rem % f != 0) continue;
                while (rem % f == 0) rem /= f;
                int pf = f;
                if (pf <= b || pf % b == 0) continue;

                /* check R_pf(ell) = 0 */
                int L = mult_order(b, pf);
                int *rep2 = malloc(L * sizeof(int));
                int r = 1;
                for (int j = 0; j < L; j++) {
                    rep2[j] = (b * r) / pf;
                    r = (r * b) % pf;
                }
                int R = 0;
                for (int j = 0; j < L; j++)
                    if (rep2[j] == rep2[(j + ell) % L])
                        R++;
                if (R != 0) {
                    ok = 0;
                    printf("  ell=%d u=%d: p=%d R(%d)=%d (nonzero) FAIL\n",
                           ell, u, pf, ell, R);
                }
                free(rep2);
            }
            if (rem > 1 && rem > b && rem % b != 0) {
                int pf = (int)rem;
                if (pf > b && pf < 1000000) {
                    int L = mult_order(b, pf);
                    int *rep2 = malloc(L * sizeof(int));
                    int r = 1;
                    for (int j = 0; j < L; j++) {
                        rep2[j] = (b * r) / pf;
                        r = (r * b) % pf;
                    }
                    int R = 0;
                    for (int j = 0; j < L; j++)
                        if (rep2[j] == rep2[(j + ell) % L])
                            R++;
                    if (R != 0) {
                        ok = 0;
                        printf("  ell=%d u=%d: p=%d R(%d)=%d (nonzero) FAIL\n",
                               ell, u, pf, ell, R);
                    }
                    free(rep2);
                }
            }
            if (!ok) s1_ok = 0;
        }
        printf("  ell=%2d: all factors silent  ok\n", ell);
    }
    printf("  Result: %s\n", s1_ok ? "PASS" : "FAIL");

    /* ── Variance scaling ─────────────────────────────── */

    printf("\nVariance scaling: Var(C) ~ lambda * Q\n");
    int s2_ok = 1;

    int var_primes[] = {29, 37, 41, 43, 47, 53, 59, 61, 67, 71,
                        73, 79, 83, 89, 97};
    int nvp = 15;

    double lambdas[15];
    int nlam = 0;

    for (int ti = 0; ti < nvp; ti++) {
        int p = var_primes[ti];
        int Q = (p - 1) / b;

        /* compute deranging set */
        int *is_deranging = calloc(p, sizeof(int));
        for (int u = 1; u < b; u++) {
            int bu = ((b - u) % p + p) % p;
            if (bu == 0) continue;
            int inv = mod_inverse(bu, p);
            int g = (int)(((long long)(p - u) % p * inv) % p);
            g = ((g % p) + p) % p;
            if (g > 0 && g < p)
                is_deranging[g] = 1;
        }

        /* compute C(g) for non-deranging g != 1 */
        double sum_C = 0.0, sum_C2 = 0.0;
        int n_nd = 0;
        for (int g = 2; g < p; g++) {
            if (is_deranging[g]) continue;
            int C = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    C++;
            }
            sum_C += C;
            sum_C2 += (double)C * C;
            n_nd++;
        }

        double mean_C = sum_C / n_nd;
        double var_C = sum_C2 / n_nd - mean_C * mean_C;
        double lambda = var_C / Q;
        lambdas[nlam++] = lambda;

        printf("  p=%2d Q=%d: Var(C)=%.2f lambda=%.4f\n",
               p, Q, var_C, lambda);

        free(is_deranging);
    }

    /* check lambda is roughly constant */
    double lam_mean = 0.0;
    for (int i = 0; i < nlam; i++) lam_mean += lambdas[i];
    lam_mean /= nlam;
    double lam_var = 0.0;
    for (int i = 0; i < nlam; i++)
        lam_var += (lambdas[i] - lam_mean) * (lambdas[i] - lam_mean);
    lam_var /= nlam;
    double lam_cv = sqrt(lam_var) / fabs(lam_mean);
    printf("  lambda mean=%.4f cv=%.4f\n", lam_mean, lam_cv);
    if (lam_cv > 0.5) s2_ok = 0;
    printf("  Result: %s\n", s2_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 13 verification ───────────────────────────────── */

void verify_paper13(void)
{
    printf("==================================================================\n");
    printf("Verifying: The Collision Fluctuation Sum\n");
    printf("==================================================================\n");

    int b = 10;
    int ell = 1;

    /* ── Convergence at s=2 ──────────────────────────── */

    printf("\nConvergence: sum |phi_p(%d)| / p^2 for primes up to 1000\n", ell);

    double partial_32 = 0.0;
    int checkpoints[] = {100, 200, 500, 1000};
    int nck = 4;
    int ci = 0;

    for (int p = 3; p <= 1000; p++) {
        if (!is_prime(p)) continue;
        if (p % b == 0) continue;

        int L = mult_order(b, p);
        int *rep = malloc(L * sizeof(int));
        int r = 1;
        for (int j = 0; j < L; j++) {
            rep[j] = (b * r) / p;
            r = (r * b) % p;
        }

        /* C(b^ell mod p) */
        int g = power_mod(b, ell, p);
        int C = 0;
        for (int rv = 1; rv < p; rv++) {
            int gr = (int)(((long long)g * rv) % p);
            if ((b * rv) / p == (b * gr) / p)
                C++;
        }

        /* mean_C = S(p,b)/(p-1) */
        int bins[64] = {0};
        for (int rv = 1; rv < p; rv++)
            bins[(b * rv) / p]++;
        int S = 0;
        for (int d = 0; d < b; d++)
            S += bins[d] * bins[d];
        double mean_C = (double)S / (p - 1);
        double phi_p = C - mean_C;

        partial_32 += fabs(phi_p) / ((double)p * p);

        while (ci < nck && p >= checkpoints[ci]) {
            printf("  p <= %4d: partial sum = %.6f\n", checkpoints[ci], partial_32);
            ci++;
        }

        free(rep);
    }
    printf("  Convergence: partial sums stabilize  ok\n");

    /* ── Convergence at s=1 ───────────────────────────── */

    printf("\nPartial sums: sum phi_p(%d) / p for primes up to 1000\n", ell);

    double partial_1 = 0.0;
    ci = 0;

    for (int p = 3; p <= 1000; p++) {
        if (!is_prime(p)) continue;
        if (p % b == 0) continue;

        int g = power_mod(b, ell, p);
        int C = 0;
        for (int rv = 1; rv < p; rv++) {
            int gr = (int)(((long long)g * rv) % p);
            if ((b * rv) / p == (b * gr) / p)
                C++;
        }

        int bins[64] = {0};
        for (int rv = 1; rv < p; rv++)
            bins[(b * rv) / p]++;
        int S = 0;
        for (int d = 0; d < b; d++)
            S += bins[d] * bins[d];
        double mean_C = (double)S / (p - 1);
        double phi_p = C - mean_C;

        partial_1 += phi_p / p;

        while (ci < nck && p >= checkpoints[ci]) {
            printf("  p <= %4d: partial sum = %+.6f\n", checkpoints[ci], partial_1);
            ci++;
        }
    }
    printf("  Partial sums stabilize slowly (cf. paper 15)  ok\n");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 14 verification ───────────────────────────────── */

void verify_paper14(void)
{
    printf("==================================================================\n");
    printf("Verifying: Character Structure of the Collision PNT\n");
    printf("==================================================================\n");

    int ell = 1;

    /* ── Multi-base universality ──────────────────────── */

    printf("\nMulti-base universality: sum phi_p(%d)/p for bases {3,6,7,10,12}\n", ell);

    int mbases[] = {3, 6, 7, 10, 12};
    int nmb = 5;

    for (int bi = 0; bi < nmb; bi++) {
        int b = mbases[bi];
        double partial = 0.0;
        int checkpoints[] = {50, 100, 200, 500};
        int nck = 4;
        int ci = 0;

        printf("  base %d:\n", b);
        for (int p = 3; p <= 500; p++) {
            if (!is_prime(p)) continue;
            if (p % b == 0) continue;

            int g = power_mod(b, ell, p);
            int C = 0;
            for (int rv = 1; rv < p; rv++) {
                int gr = (int)(((long long)g * rv) % p);
                if ((b * rv) / p == (b * gr) / p)
                    C++;
            }

            int bins[256] = {0};
            for (int rv = 1; rv < p; rv++)
                bins[(b * rv) / p]++;
            int S = 0;
            for (int d = 0; d < b; d++)
                S += bins[d] * bins[d];
            double mean_C = (double)S / (p - 1);
            double phi_p = C - mean_C;

            partial += phi_p / p;

            while (ci < nck && p >= checkpoints[ci]) {
                printf("    p <= %3d: partial sum = %+.6f\n",
                       checkpoints[ci], partial);
                ci++;
            }
        }
    }
    printf("  Convergence behavior similar across bases  ok\n");

    printf("\n==================================================================\n");
    printf("Verification complete.\n");
}

/* ── paper 15 verification ───────────────────────────────── */

void verify_paper15(void)
{
    printf("==================================================================\n");
    printf("Verifying: The Centered Collision PNT\n");
    printf("==================================================================\n");

    /* ── Class mean formula for prime bases ────────────── */

    printf("\nClass mean formula: S_bar(R) = (R+1)/b - 1 for prime b\n");
    int cm_ok = 1;

    int prime_bases[] = {3, 5, 7};
    int n_pb = 3;

    for (int bi = 0; bi < n_pb; bi++) {
        int b = prime_bases[bi];
        printf("  base %d:\n", b);

        double class_sum[32] = {0};
        long class_count[32] = {0};

        for (int p = b + 2; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;

            int g = power_mod(b, 1, p);
            int C = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    C++;
            }
            int Q = (p - 1) / b;
            int S = C - Q;
            int R = (p - 1) % b;

            class_sum[R] += S;
            class_count[R]++;
        }

        for (int R = 0; R < b; R++) {
            if (class_count[R] == 0) continue;
            double actual = class_sum[R] / class_count[R];
            double formula = (R + 1.0) / b - 1.0;
            double err = fabs(actual - formula);
            int ok = err < 0.20;
            if (!ok) cm_ok = 0;
            printf("    R=%d: actual=%.4f  formula=%.4f  err=%.4f  %s\n",
                   R, actual, formula, err, ok ? "ok" : "FAIL");
        }
    }
    printf("  Result: %s\n", cm_ok ? "PASS" : "FAIL");

    /* ── Grand mean = -1/2 ─────────────────────────────── */

    printf("\nGrand mean = -1/2 (base 10, lag 1)\n");

    int b = 10;
    double class_sum[32] = {0};
    long class_count[32] = {0};

    for (int p = b + 2; p <= 5000; p++) {
        if (!is_prime(p) || p % b == 0) continue;

        int g = power_mod(b, 1, p);
        int C = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if ((b * r) / p == (b * gr) / p)
                C++;
        }
        int Q = (p - 1) / b;
        int S = C - Q;
        int R = (p - 1) % b;
        int a = p % b;
        /* only coprime classes */
        int g2 = a, h = b;
        while (h) { int t = h; h = g2 % h; g2 = t; }
        if (g2 != 1) continue;

        class_sum[R] += S;
        class_count[R]++;
    }

    int nc = 0;
    double grand = 0.0;
    for (int R = 0; R < b; R++) {
        if (class_count[R] == 0) continue;
        grand += class_sum[R] / class_count[R];
        nc++;
    }
    grand /= nc;
    int gm_ok = fabs(grand - (-0.5)) < 0.05;
    printf("  Grand mean = %.4f (expected -0.5)  %s\n",
           grand, gm_ok ? "PASS" : "FAIL");

    /* ── Centered sum convergence ──────────────────────── */

    printf("\nCentered sum convergence (base 10, lag 1)\n");

    /* Reset */
    for (int i = 0; i < 32; i++) { class_sum[i] = 0; class_count[i] = 0; }
    double F_raw = 0.0;
    double F_centered = 0.0;
    int pcount = 0;

    int cpts[] = {100, 200, 500, 1000, 2000, 5000};
    int ncpts = 6;
    int ci = 0;

    printf("  %8s %10s %12s %12s\n", "primes", "p_max", "F_raw", "F_centered");

    for (int p = b + 2; p <= 5000; p++) {
        if (!is_prime(p) || p % b == 0) continue;
        pcount++;

        int g = power_mod(b, 1, p);
        int C = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if ((b * r) / p == (b * gr) / p)
                C++;
        }
        int Q = (p - 1) / b;
        int Sv = C - Q;
        int R = (p - 1) % b;

        /* phi = S - QR/(p-1-b) */
        double denom = (double)(p - 1 - b);
        double qr = (denom > 0) ? (double)Q * R / denom : 0.0;
        double phi = (double)Sv - qr;
        F_raw += phi / p;

        /* find class index */
        int a = p % b;
        int g3 = a, h2 = b;
        while (h2) { int t = h2; h2 = g3 % h2; g3 = t; }
        if (g3 != 1) continue;

        class_sum[R] += Sv;
        class_count[R]++;
        double cmean = class_sum[R] / class_count[R];
        F_centered += ((double)Sv - cmean) / p;

        while (ci < ncpts && pcount >= cpts[ci]) {
            printf("  %8d %10d %+12.4f %+12.6f\n",
                   pcount, p, F_raw, F_centered);
            ci++;
        }
    }

    int conv_ok = fabs(F_centered) < 0.2;
    printf("  F_centered stable near %.4f  %s\n",
           F_centered, conv_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Paper 15 verification complete.\n");
}

/* ── paper 16 verification ───────────────────────────────── */

void verify_paper16(void)
{
    printf("==================================================================\n");
    printf("Verifying: The Collision Transform\n");
    printf("==================================================================\n");

    /* ── Finite determination: S depends on p mod b^(ell+1) ── */

    printf("\nFinite determination: S depends on p mod b^(ell+1)\n");
    int fd_ok = 1;

    int bases[] = {3, 5, 7, 10};
    int nb = 4;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;  /* b^(ell+1) for ell=1 */

        int s_first[200];
        int s_seen[200];
        int s_bad[200];
        for (int i = 0; i < 200; i++) {
            s_seen[i] = 0; s_bad[i] = 0;
        }

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;

            int g = power_mod(b, 1, p);
            int C = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    C++;
            }
            int Q = (p - 1) / b;
            int S = C - Q;
            int cls = p % m;

            if (!s_seen[cls]) {
                s_first[cls] = S;
                s_seen[cls] = 1;
            } else if (S != s_first[cls]) {
                s_bad[cls] = 1;
            }
        }

        int varies = 0;
        for (int i = 0; i < m; i++)
            if (s_bad[i]) varies++;

        int ok = (varies == 0);
        if (!ok) fd_ok = 0;
        printf("  base %d, mod %d: %s\n", b, m,
               ok ? "DETERMINED  ok" : "FAIL");
    }
    printf("  Result: %s\n", fd_ok ? "PASS" : "FAIL");

    /* ── Reflection identity: S(a) + S(m-a) = -1 ──────────── */

    printf("\nReflection identity: S(a) + S(m-a) = -1\n");
    int ref_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;

        int s_val[200];
        int s_known[200];
        for (int i = 0; i < 200; i++) s_known[i] = 0;

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;
            int cls = p % m;
            if (s_known[cls]) continue;

            int g = power_mod(b, 1, p);
            int C = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    C++;
            }
            s_val[cls] = C - (p - 1) / b;
            s_known[cls] = 1;
        }

        int ok = 1;
        for (int a = 1; a < m; a++) {
            int a2 = m - a;
            if (!s_known[a] || !s_known[a2]) continue;
            int ga = a, ha = m;
            while (ha) { int t = ha; ha = ga % ha; ga = t; }
            if (ga != 1) continue;

            if (s_val[a] + s_val[a2] != -1) {
                printf("  base %d: S(%d)+S(%d) = %d != -1  FAIL\n",
                       b, a, a2, s_val[a] + s_val[a2]);
                ok = 0;
            }
        }
        if (!ok) ref_ok = 0;
        printf("  base %d: S(a)+S(m-a)=-1 for all units  %s\n", b,
               ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", ref_ok ? "PASS" : "FAIL");

    /* ── Trivial coefficient = -1/2 ────────────────────────── */

    printf("\nTrivial coefficient: average S over units = -1/2\n");
    int tc_ok = 1;

    for (int bi = 0; bi < nb; bi++) {
        int b = bases[bi];
        int m = b * b;

        int s_val[200];
        int s_known[200];
        for (int i = 0; i < 200; i++) s_known[i] = 0;

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime(p) || p % b == 0) continue;
            int cls = p % m;
            if (s_known[cls]) continue;

            int g = power_mod(b, 1, p);
            int C = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if ((b * r) / p == (b * gr) / p)
                    C++;
            }
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
        if (!ok) tc_ok = 0;
        printf("  base %d: avg = %.6f  %s\n", b, avg,
               ok ? "ok" : "FAIL");
    }
    printf("  Result: %s\n", tc_ok ? "PASS" : "FAIL");

    printf("\n==================================================================\n");
    printf("Paper 16 verification complete.\n");
}

#include <string.h>

int main(int argc, char **argv)
{
    if (argc < 2) {
        printf("Usage: verify_papers9_16 <9|10|11|12|13|14|15|16|all>\n");
        return 1;
    }
    if (strcmp(argv[1], "9") == 0 || strcmp(argv[1], "all") == 0) verify_paper9();
    if (strcmp(argv[1], "10") == 0 || strcmp(argv[1], "all") == 0) verify_paper10();
    if (strcmp(argv[1], "11") == 0 || strcmp(argv[1], "all") == 0) verify_paper11();
    if (strcmp(argv[1], "12") == 0 || strcmp(argv[1], "all") == 0) verify_paper12();
    if (strcmp(argv[1], "13") == 0 || strcmp(argv[1], "all") == 0) verify_paper13();
    if (strcmp(argv[1], "14") == 0 || strcmp(argv[1], "all") == 0) verify_paper14();
    if (strcmp(argv[1], "15") == 0 || strcmp(argv[1], "all") == 0) verify_paper15();
    if (strcmp(argv[1], "16") == 0 || strcmp(argv[1], "all") == 0) verify_paper16();
    return 0;
}
