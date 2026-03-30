/*
 * goldbach_class.c - Goldbach restricted to collision classes.
 *
 * Cody's idea: pick a positive-density subset A of units mod m
 * from the collision geometry, and ask if every large even N
 * is p + q with both p, q in A.
 *
 * Natural choices for A:
 * 1. Wrapping set W (half the units, by half-group theorem)
 * 2. High-collision class: units with S(a) >= 0
 * 3. Specific spectral class R
 * 4. Neutral class (a = 2 mod 3 at lag 1)
 *
 * For each choice, compute:
 * - density of A among units
 * - R_A(N) = #{p+q=N : p,q in A mod m} for even N
 * - Compare with R(N) = total Goldbach count
 * - Check: is R_A(N) > 0 for all large even N?
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_N 200000
#define B 10
#define M (B * B)

static int sieve[MAX_N + 1];

static void build_sieve(void) {
    memset(sieve, 1, sizeof(sieve));
    sieve[0] = sieve[1] = 0;
    for (int i = 2; i * i <= MAX_N; i++)
        if (sieve[i])
            for (int j = i * i; j <= MAX_N; j += i)
                sieve[j] = 0;
}

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    build_sieve();

    /* Build S table */
    int S_table[M];
    int has_S[M];
    memset(has_S, 0, sizeof(has_S));

    for (int p = M + 1; p < 50000; p++) {
        if (!sieve[p] || gcd(p, B) != 1) continue;
        int a = p % M;
        if (has_S[a]) continue;
        int C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)B * r / p);
            long long br = (long long)B * r % p;
            int d2 = (int)((long long)B * br / p);
            if (d1 == d2) C++;
        }
        S_table[a] = C - (p - 1) / B;
        has_S[a] = 1;
    }

    /* Define collision classes */
    int units[M], n_units = 0;
    for (int a = 1; a < M; a++)
        if (gcd(a, M) == 1) units[n_units++] = a;

    /* Class 1: S >= 0 (high collision) */
    int high_collision[M];
    memset(high_collision, 0, sizeof(high_collision));
    int n_high = 0;
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (has_S[a] && S_table[a] >= 0) {
            high_collision[a] = 1;
            n_high++;
        }
    }

    /* Class 2: S < 0 (low collision) */
    int low_collision[M];
    memset(low_collision, 0, sizeof(low_collision));
    int n_low = 0;
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (has_S[a] && S_table[a] < 0) {
            low_collision[a] = 1;
            n_low++;
        }
    }

    /* Class 3: neutral mod-3 class (a = 2 mod 3) */
    int neutral[M];
    memset(neutral, 0, sizeof(neutral));
    int n_neutral = 0;
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (a % 3 == 2) {
            neutral[a] = 1;
            n_neutral++;
        }
    }

    /* Class 4: biased mod-3 class (a = 1 mod 3) */
    int biased[M];
    memset(biased, 0, sizeof(biased));
    int n_biased = 0;
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (a % 3 == 1) {
            biased[a] = 1;
            n_biased++;
        }
    }

    printf("Classes (base %d, m=%d, %d units):\n", B, M, n_units);
    printf("  High collision (S>=0): %d units (%.1f%%)\n",
           n_high, 100.0 * n_high / n_units);
    printf("  Low collision  (S<0):  %d units (%.1f%%)\n",
           n_low, 100.0 * n_low / n_units);
    printf("  Neutral (a=2 mod 3):   %d units (%.1f%%)\n",
           n_neutral, 100.0 * n_neutral / n_units);
    printf("  Biased  (a=1 mod 3):   %d units (%.1f%%)\n",
           n_biased, 100.0 * n_biased / n_units);
    printf("\n");

    /* Check membership function for primes */
    /* A prime p is "in class" if p > M, gcd(p,B)=1, and p%M is in the class */

    /* Count Goldbach representations in each class */
    int first_fail_high = 0, first_fail_low = 0;
    int first_fail_neutral = 0, first_fail_biased = 0;
    int min_R_high = 999999, min_R_low = 999999;
    int min_R_neutral = 999999, min_R_biased = 999999;

    printf("%8s %6s %6s %6s %6s %6s\n",
           "N", "R(N)", "R_high", "R_low", "R_neut", "R_bias");

    for (int N = M + 4; N <= MAX_N; N += 2) {
        int R = 0, R_high = 0, R_low = 0, R_neut = 0, R_bias = 0;

        for (int p = 3; p <= N - 3; p += 2) {
            if (!sieve[p]) continue;
            int q = N - p;
            if (q < 3 || !sieve[q]) continue;
            if (p > q) break;

            R++;

            /* Check if both p and q are in class */
            int p_in_high = 0, p_in_low = 0, p_in_neut = 0, p_in_bias = 0;
            int q_in_high = 0, q_in_low = 0, q_in_neut = 0, q_in_bias = 0;

            if (p > M && gcd(p, B) == 1) {
                int ap = p % M;
                p_in_high = high_collision[ap];
                p_in_low = low_collision[ap];
                p_in_neut = neutral[ap];
                p_in_bias = biased[ap];
            }
            if (q > M && gcd(q, B) == 1) {
                int aq = q % M;
                q_in_high = high_collision[aq];
                q_in_low = low_collision[aq];
                q_in_neut = neutral[aq];
                q_in_bias = biased[aq];
            }

            if (p_in_high && q_in_high) R_high++;
            if (p_in_low && q_in_low) R_low++;
            if (p_in_neut && q_in_neut) R_neut++;
            if (p_in_bias && q_in_bias) R_bias++;
        }

        if (R_high < min_R_high) min_R_high = R_high;
        if (R_low < min_R_low) min_R_low = R_low;
        if (R_neut < min_R_neutral) min_R_neutral = R_neut;
        if (R_bias < min_R_biased) min_R_biased = R_bias;

        if (R_high == 0 && first_fail_high == 0 && N > 1000)
            first_fail_high = N;
        if (R_low == 0 && first_fail_low == 0 && N > 1000)
            first_fail_low = N;
        if (R_neut == 0 && first_fail_neutral == 0 && N > 1000)
            first_fail_neutral = N;
        if (R_bias == 0 && first_fail_biased == 0 && N > 1000)
            first_fail_biased = N;

        if (N % 20000 == 0) {
            printf("%8d %6d %6d %6d %6d %6d\n",
                   N, R, R_high, R_low, R_neut, R_bias);
        }
    }

    printf("\nSummary (N from %d to %d):\n", M + 4, MAX_N);
    printf("  High collision: min R_A = %d, first fail at N = %d\n",
           min_R_high, first_fail_high);
    printf("  Low collision:  min R_A = %d, first fail at N = %d\n",
           min_R_low, first_fail_low);
    printf("  Neutral:        min R_A = %d, first fail at N = %d\n",
           min_R_neutral, first_fail_neutral);
    printf("  Biased:         min R_A = %d, first fail at N = %d\n",
           min_R_biased, first_fail_biased);

    return 0;
}
