/*
 * neutrality_general.c - Test neutrality for all primes q, not just q=3.
 *
 * For each base b and each prime q not dividing b:
 * - Compute the self-mapping class k = m*(q+1)/2 mod q
 * - Check if mean of S over units a ≡ k mod q equals -1/2
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
    int primes_q[] = {3, 5, 7, 11, 13, 17, 19};
    int nq = sizeof(primes_q) / sizeof(primes_q[0]);

    printf("%5s %5s %5s %8s %6s %6s %8s %5s\n",
           "base", "q", "k", "sum_k", "cnt_k", "2sum+c", "mean_k", "ok?");

    for (int b = 2; b <= 20; b++) {
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

        for (int qi = 0; qi < nq; qi++) {
            int q = primes_q[qi];
            if (b % q == 0) continue;  /* skip q | b */

            /* Self-mapping class: k = m*(q+1)/2 mod q */
            int m_mod_q = m % q;
            /* 2^{-1} mod q = (q+1)/2 */
            int inv2 = (q + 1) / 2;
            int k = (m_mod_q * inv2) % q;

            /* Sum S over units a ≡ k mod q */
            int sum_k = 0, cnt_k = 0;
            for (int a = 1; a < m; a++) {
                if (gcd(a, m) != 1 || !has[a]) continue;
                if (a % q == k) {
                    sum_k += S[a];
                    cnt_k++;
                }
            }

            /* Check: 2*sum_k == -cnt_k means mean = -1/2 */
            int exact = (2 * sum_k == -cnt_k);
            double mean_k = cnt_k > 0 ? (double)sum_k / cnt_k : 0;

            if (!exact || b <= 5) {  /* print failures and small bases */
                printf("%5d %5d %5d %8d %6d %6d %+8.4f %5s\n",
                       b, q, k, sum_k, cnt_k,
                       2*sum_k + cnt_k, mean_k,
                       exact ? "YES" : "NO");
            }
        }
    }

    /* Summary */
    printf("\n--- Full check: all bases 2-20, all primes q <= 19 ---\n");
    int total = 0, pass = 0;

    for (int b = 2; b <= 20; b++) {
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

        for (int qi = 0; qi < nq; qi++) {
            int q = primes_q[qi];
            if (b % q == 0) continue;

            int m_mod_q = m % q;
            int inv2 = (q + 1) / 2;
            int k = (m_mod_q * inv2) % q;

            int sum_k = 0, cnt_k = 0;
            for (int a = 1; a < m; a++) {
                if (gcd(a, m) != 1 || !has[a]) continue;
                if (a % q == k) {
                    sum_k += S[a];
                    cnt_k++;
                }
            }

            total++;
            if (2 * sum_k == -cnt_k) pass++;
            else printf("FAIL: b=%d q=%d k=%d sum=%d cnt=%d\n",
                        b, q, k, sum_k, cnt_k);
        }
    }

    printf("Passed: %d / %d\n", pass, total);

    return 0;
}
