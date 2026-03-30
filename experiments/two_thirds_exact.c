/*
 * Check if mean_2 = -1/2 exactly for 3∤b.
 * Also verify mean_0 + mean_1 = -1 exactly.
 * And check: does the reflection a -> m-a map class 2 to itself?
 */

#include <stdio.h>
#include <string.h>

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
    printf("=== Checking mean_2 = -1/2 for 3∤b ===\n\n");

    for (int b = 2; b <= 40; b++) {
        if (b % 3 == 0) continue;  /* skip 3|b for now */
        int m = b * b;

        /* Build S table */
        int S[m];
        int has[m];
        memset(has, 0, sizeof(int) * m);

        for (int p = m + 1; p < 80000; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            if (has[a]) continue;

            int C = 0;
            for (int r = 1; r < p; r++) {
                int d1 = (int)((long long)b * r / p);
                long long br = (long long)b * r % p;
                int d2 = (int)((long long)b * br / p);
                if (d1 == d2) C++;
            }
            S[a] = C - (p - 1) / b;
            has[a] = 1;
        }

        /* Check m mod 3 */
        int m_mod3 = m % 3;

        /* Sum S over each mod-3 class */
        int sum[3] = {0, 0, 0};
        int cnt[3] = {0, 0, 0};

        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1 || !has[a]) continue;
            sum[a % 3] += S[a];
            cnt[a % 3]++;
        }

        /* Check if class 2 self-pairs under reflection */
        int self_pairs = 0, cross_pairs = 0;
        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1 || !has[a]) continue;
            if (a % 3 != 2) continue;
            int ref = m - a;
            if (ref % 3 == 2) self_pairs++;
            else cross_pairs++;
        }

        /* Exact check: 2*sum_2 = -cnt_2 means mean_2 = -1/2 */
        int exact = (2 * sum[2] == -cnt[2]);

        printf("b=%2d  m=%4d  m%%3=%d  |"
               "  sum0=%+5d/%2d  sum1=%+5d/%2d  sum2=%+5d/%2d  |"
               "  2*sum2=%-5d -cnt2=%-5d  exact=%s  |"
               "  sum01=%+5d -cnt01=%-5d  |"
               "  cls2: self=%d cross=%d\n",
               b, m, m_mod3,
               sum[0], cnt[0], sum[1], cnt[1], sum[2], cnt[2],
               2*sum[2], -cnt[2], exact ? "YES" : "NO",
               sum[0]+sum[1], -(cnt[0]+cnt[1]),
               self_pairs, cross_pairs);
    }

    printf("\n=== Now checking 3|b ===\n\n");
    for (int b = 3; b <= 30; b += 3) {
        int m = b * b;

        int S[m];
        int has[m];
        memset(has, 0, sizeof(int) * m);

        for (int p = m + 1; p < 80000; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            if (has[a]) continue;

            int C = 0;
            for (int r = 1; r < p; r++) {
                int d1 = (int)((long long)b * r / p);
                long long br = (long long)b * r % p;
                int d2 = (int)((long long)b * br / p);
                if (d1 == d2) C++;
            }
            S[a] = C - (p - 1) / b;
            has[a] = 1;
        }

        int sum[3] = {0, 0, 0};
        int cnt[3] = {0, 0, 0};
        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1 || !has[a]) continue;
            sum[a % 3] += S[a];
            cnt[a % 3]++;
        }

        printf("b=%2d  m=%4d  m%%3=%d  |"
               "  sum0=%+5d/%2d  sum1=%+5d/%2d  sum2=%+5d/%2d\n",
               b, m, m % 3,
               sum[0], cnt[0], sum[1], cnt[1], sum[2], cnt[2]);
    }

    return 0;
}
