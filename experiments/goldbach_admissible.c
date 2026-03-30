/*
 * goldbach_admissible.c - Goldbach with admissible collision subsets.
 *
 * Instead of requiring both primes in the SAME class,
 * allow p in class A and q in class B where A and B
 * are collision-defined subsets.
 *
 * Key test: for the wrapping set W (exactly half the units),
 * count Goldbach representations where at least one prime
 * is in W. Does every large even N have such a representation?
 *
 * Also: for the high-collision set (S >= 0), count reps
 * where at least one prime has high collision.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_N 500000
#define B 10
#define M (B * B)

static char sieve[MAX_N + 1];

static void build_sieve(void) {
    memset(sieve, 1, sizeof(sieve));
    sieve[0] = sieve[1] = 0;
    for (int i = 2; (long long)i * i <= MAX_N; i++)
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
    int S_table[M], has_S[M];
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

    /* Class: S >= 0 */
    int high[M];
    memset(high, 0, sizeof(high));
    int n_high = 0;
    for (int a = 1; a < M; a++) {
        if (gcd(a, M) != 1 || !has_S[a]) continue;
        if (S_table[a] >= 0) { high[a] = 1; n_high++; }
    }

    /* Precompute class membership for each prime */
    /* For speed, just store whether p is "high" based on p % M */

    printf("High-collision units: %d / 40 (50%%)\n\n", n_high);

    /* Test 1: at least one prime has high collision */
    /* Test 2: both primes have high collision */
    /* Test 3: exactly one has high collision */

    int n_fail_atleast1 = 0, n_fail_both = 0;
    int min_atleast1 = 999999, min_both = 999999;
    long long sum_atleast1 = 0, sum_both = 0, sum_total = 0;
    int count = 0;

    printf("%8s %6s %6s %6s %6s %6s\n",
           "N", "R(N)", "R_>=1", "R_both", "ratio1", "ratio2");

    for (int N = 200; N <= MAX_N; N += 2) {
        int R = 0, R_atleast1 = 0, R_both = 0;

        for (int p = 3; p <= N - 3; p += 2) {
            if (!sieve[p]) continue;
            int q = N - p;
            if (q < 3 || !sieve[q]) continue;
            if (p > q) break;

            R++;

            int p_high = 0, q_high = 0;
            if (p > M && gcd(p, B) == 1)
                p_high = high[p % M];
            if (q > M && gcd(q, B) == 1)
                q_high = high[q % M];

            if (p_high || q_high) R_atleast1++;
            if (p_high && q_high) R_both++;
        }

        if (R_atleast1 == 0 && N > 1000) n_fail_atleast1++;
        if (R_both == 0 && N > 1000) n_fail_both++;
        if (R_atleast1 < min_atleast1) min_atleast1 = R_atleast1;
        if (R_both < min_both) min_both = R_both;

        sum_total += R;
        sum_atleast1 += R_atleast1;
        sum_both += R_both;
        count++;

        if (N % 50000 == 0 && R > 0) {
            printf("%8d %6d %6d %6d %6.3f %6.3f\n",
                   N, R, R_atleast1, R_both,
                   (double)R_atleast1 / R,
                   (double)R_both / R);
        }
    }

    double ratio1 = (double)sum_atleast1 / sum_total;
    double ratio2 = (double)sum_both / sum_total;

    printf("\nSummary (N from 200 to %d):\n", MAX_N);
    printf("  At-least-one high: fails=%d, min=%d, avg ratio=%.4f\n",
           n_fail_atleast1, min_atleast1, ratio1);
    printf("  Both high:         fails=%d, min=%d, avg ratio=%.4f\n",
           n_fail_both, min_both, ratio2);
    printf("  Expected (random): at-least-one=%.4f, both=%.4f\n",
           1.0 - 0.5*0.5, 0.5*0.5);

    /* Print the S values for the high-collision units */
    printf("\nHigh-collision units (S >= 0):\n");
    for (int a = 1; a < M; a++) {
        if (high[a])
            printf("  a=%2d S=%+d (a mod 3=%d)\n", a, S_table[a], a%3);
    }

    return 0;
}
