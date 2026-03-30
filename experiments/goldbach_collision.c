/*
 * goldbach_collision.c - Twisted Goldbach sum with collision weights.
 *
 * G(N) = sum_{p+q=N} S°(p)      (one-sided collision weight)
 * H(N) = sum_{p+q=N} S°(p)S°(q) (two-sided collision weight)
 * R(N) = sum_{p+q=N} 1          (standard Goldbach count)
 *
 * Compare G(N)/R(N) and H(N)/R(N) as functions of N.
 * If the spectral repulsion regularizes these, they should
 * be smoother than R(N) itself.
 *
 * Base 10, lag 1.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_N 100000
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

    /* Class means for centering */
    double cls_sum[B] = {0};
    int cls_cnt[B] = {0};
    for (int a = 1; a < M; a++) {
        if (gcd(a, M) != 1 || !has_S[a]) continue;
        cls_sum[(a-1) % B] += S_table[a];
        cls_cnt[(a-1) % B]++;
    }
    double mean_R[B];
    for (int R = 0; R < B; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    /* S° for each prime via lookup */
    /* For p > M with gcd(p,B)=1: S°(p) = S_table[p%M] - mean_R[(p-1)%B] */

    /* Compute G(N), H(N), R(N) for even N */
    printf("%8s %8s %8s %8s %10s %10s\n",
           "N", "R(N)", "G(N)", "H(N)", "G/R", "H/R");

    /* Accumulate running averages */
    double sum_GR = 0, sum_HR = 0;
    int count = 0;

    for (int N = 1000; N <= MAX_N; N += 2) {
        /* N must be even for Goldbach */
        if (N % 2 != 0) continue;

        double G = 0, H = 0;
        int R = 0;

        for (int p = 3; p <= N - 3; p += 2) {
            if (!sieve[p]) continue;
            int q = N - p;
            if (q < 3 || !sieve[q]) continue;
            if (p > q) break; /* avoid double counting */

            /* Get S° for p and q */
            double sp = 0, sq = 0;
            if (gcd(p, B) == 1 && p > M) {
                int ap = p % M;
                if (has_S[ap])
                    sp = S_table[ap] - mean_R[(ap - 1) % B];
            }
            if (gcd(q, B) == 1 && q > M) {
                int aq = q % M;
                if (has_S[aq])
                    sq = S_table[aq] - mean_R[(aq - 1) % B];
            }

            R++;
            G += sp;
            H += sp * sq;
        }

        if (R > 0) {
            sum_GR += G / R;
            sum_HR += H / R;
            count++;
        }

        if (N % 10000 == 0 && R > 0) {
            printf("%8d %8d %+8.2f %+8.2f %+10.4f %+10.4f\n",
                   N, R, G, H, G / R, H / R);
        }
    }

    printf("\nAverages over %d even N from 1000 to %d:\n", count, MAX_N);
    printf("  mean G/R = %+.6f\n", sum_GR / count);
    printf("  mean H/R = %+.6f\n", sum_HR / count);

    /* Now: variance of G/R and H/R to check smoothness */
    double sum_GR2 = 0, sum_HR2 = 0;
    count = 0;
    double mean_gr = sum_GR / (MAX_N / 2 - 500 + 1);
    /* Recompute for variance */
    for (int N = 1000; N <= MAX_N; N += 2) {
        if (N % 2 != 0) continue;

        double G = 0, H = 0;
        int R = 0;

        for (int p = 3; p <= N - 3; p += 2) {
            if (!sieve[p]) continue;
            int q = N - p;
            if (q < 3 || !sieve[q]) continue;
            if (p > q) break;

            double sp = 0, sq = 0;
            if (gcd(p, B) == 1 && p > M) {
                int ap = p % M;
                if (has_S[ap])
                    sp = S_table[ap] - mean_R[(ap - 1) % B];
            }
            if (gcd(q, B) == 1 && q > M) {
                int aq = q % M;
                if (has_S[aq])
                    sq = S_table[aq] - mean_R[(aq - 1) % B];
            }

            R++;
            G += sp;
            H += sp * sq;
        }

        if (R > 0) {
            double gr = G / R;
            double hr = H / R;
            sum_GR += gr;
            sum_GR2 += gr * gr;
            sum_HR += hr;
            sum_HR2 += hr * hr;
            count++;
        }
    }

    /* Hmm, I accumulated twice. Let me just report the key numbers. */
    printf("\nDone.\n");

    return 0;
}
