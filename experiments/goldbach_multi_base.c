/*
 * goldbach_multi_base.c - H(N)/R(N) across bases.
 * Is the constant -6.5 base-specific? Does it have a formula?
 *
 * Also: compute the variance of H/R to quantify smoothness.
 * And: check if the constant relates to known quantities
 * (grand mean, phi(m), number of odd characters, etc.)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_N 100000

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

void run_base(int B) {
    int M = B * B;

    /* Build S table */
    int S_table[M];
    int has_S[M];
    memset(has_S, 0, sizeof(int) * M);

    for (int p = M + 1; p < 80000; p++) {
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

    /* Class means */
    double cls_sum[B];
    int cls_cnt[B];
    memset(cls_sum, 0, sizeof(double) * B);
    memset(cls_cnt, 0, sizeof(int) * B);
    for (int a = 1; a < M; a++) {
        if (gcd(a, M) != 1 || !has_S[a]) continue;
        cls_sum[(a-1) % B] += S_table[a];
        cls_cnt[(a-1) % B]++;
    }
    double mean_R[B];
    for (int R = 0; R < B; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    /* Compute sum of S°(a)^2 over units (for comparison) */
    double sum_sc2 = 0;
    int n_units = 0;
    for (int a = 1; a < M; a++) {
        if (gcd(a, M) != 1 || !has_S[a]) continue;
        double sc = S_table[a] - mean_R[(a-1) % B];
        sum_sc2 += sc * sc;
        n_units++;
    }
    double var_sc = sum_sc2 / n_units;

    /* Compute H/R for even N */
    double sum_hr = 0, sum_hr2 = 0;
    double sum_gr = 0;
    int count = 0;

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
            double hr = H / R;
            double gr = G / R;
            sum_hr += hr;
            sum_hr2 += hr * hr;
            sum_gr += gr;
            count++;
        }
    }

    double mean_hr = sum_hr / count;
    double mean_gr = sum_gr / count;
    double var_hr = sum_hr2 / count - mean_hr * mean_hr;

    /* Known quantities */
    int phi = n_units;
    int n_odd = phi / 2;

    printf("%5d %4d %4d %+10.4f %+10.4f %10.4f %10.4f %+10.4f\n",
           B, phi, n_odd, mean_hr, mean_gr,
           sqrt(var_hr), var_sc,
           -var_sc);
}

int main(void) {
    build_sieve();

    printf("%5s %4s %4s %10s %10s %10s %10s %10s\n",
           "base", "phi", "odd", "mean_H/R", "mean_G/R",
           "std_H/R", "var_S°", "-var_S°");

    int bases[] = {3, 5, 7, 10, 11, 13};
    for (int i = 0; i < 6; i++)
        run_base(bases[i]);

    return 0;
}
/* Already compiled. Just need to add base 10 call. */
