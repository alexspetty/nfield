/*
 * two_thirds.c - Per-base mod-3 means of S to find the source of 2/3.
 *
 * For each base b, compute S_1(a) for all units a mod b².
 * Then compute the mean of S over units a ≡ 1 mod 3 vs a ≡ 2 mod 3.
 * See if the ratio mean_1 / (mean_1 + mean_2) = 2/3 for every base.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

static int is_prime(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

int main(void) {
    printf("%5s %6s %10s %10s %10s %10s %8s\n",
           "base", "units", "mean_1", "mean_2", "mean_0",
           "grand", "ratio");

    for (int b = 2; b <= 30; b++) {
        int m = b * b;

        /* Build S table for all units mod m */
        double S[m];
        int has[m];
        memset(has, 0, sizeof(int) * m);

        for (int p = m + 1; p < 50000; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            if (has[a]) continue;

            /* Compute collision count C(b mod p) */
            int C = 0;
            for (int r = 1; r < p; r++) {
                int d1 = (int)((long long)b * r / p);
                long long br_mod_p = (long long)b * r % p;
                int d2 = (int)((long long)b * br_mod_p / p);
                if (d1 == d2) C++;
            }
            int Q = (p - 1) / b;
            S[a] = C - Q;
            has[a] = 1;
        }

        /* Compute mod-3 means */
        double sum_0 = 0, sum_1 = 0, sum_2 = 0;
        int cnt_0 = 0, cnt_1 = 0, cnt_2 = 0;

        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1 || !has[a]) continue;
            int k = a % 3;
            if (k == 0) { sum_0 += S[a]; cnt_0++; }
            else if (k == 1) { sum_1 += S[a]; cnt_1++; }
            else { sum_2 += S[a]; cnt_2++; }
        }

        double mean_0 = cnt_0 > 0 ? sum_0 / cnt_0 : 0;
        double mean_1 = cnt_1 > 0 ? sum_1 / cnt_1 : 0;
        double mean_2 = cnt_2 > 0 ? sum_2 / cnt_2 : 0;
        double grand = (sum_0 + sum_1 + sum_2) / (cnt_0 + cnt_1 + cnt_2);

        /* Ratio: what fraction of the total (negative) mean comes from class 1? */
        /* Since grand mean = -1/2, and we want to see the split */
        double total = fabs(mean_1) + fabs(mean_2);
        double ratio = total > 0.001 ? fabs(mean_1) / total : 0;

        printf("%5d %6d %+10.4f %+10.4f %+10.4f %+10.4f %8.4f\n",
               b, cnt_0 + cnt_1 + cnt_2,
               mean_1, mean_2, mean_0, grand, ratio);
    }

    return 0;
}
