// Base 60 at 10^7 primes using finite determination
// S depends on p mod 3600. Compute S table once, then lookup.

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#define B 60
#define M (B * B)  // 3600

int is_prime(long n) {
    if (n < 2) return 0;
    if (n == 2 || n == 3) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (long i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

long power_mod(long base, long exp, long mod) {
    long result = 1; base %= mod;
    while (exp > 0) {
        if (exp & 1) result = (__int128)result * base % mod;
        base = (__int128)base * base % mod;
        exp >>= 1;
    }
    return result;
}

int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int collision_count(long g, long p, int b) {
    int count = 0;
    for (long r = 1; r < p; r++) {
        int d_r = (int)((long long)b * r / p);
        long gr = (__int128)g * r % p;
        int d_gr = (int)((long long)b * gr / p);
        if (d_r == d_gr) count++;
    }
    return count;
}

int main() {
    long max_p = 200000000;  // 2 * 10^8 to get ~10^7 coprime primes

    printf("BASE 60: finite determination lookup\n");
    printf("Modulus = %d, phi = 960\n\n", M);

    // Step 1: Build S table for all coprime classes mod 3600
    int S_table[M];
    int S_known[M];
    memset(S_known, 0, sizeof(S_known));

    fprintf(stderr, "Building S table (one prime per class)...\n");
    int classes_found = 0;
    int classes_needed = 0;

    // Count needed classes
    for (int a = 1; a < M; a++)
        if (gcd(a, B) == 1) classes_needed++;

    for (long p = M + 1; classes_found < classes_needed && p < 1000000; p++) {
        if (!is_prime(p)) continue;
        if (p % 2 == 0 || p % 3 == 0 || p % 5 == 0) continue;

        int cls = (int)(p % M);
        if (S_known[cls]) continue;

        long g = power_mod(B, 1, p);
        int C = collision_count(g, p, B);
        int Q = (int)((p - 1) / B);
        S_table[cls] = C - Q;
        S_known[cls] = 1;
        classes_found++;

        if (classes_found % 100 == 0)
            fprintf(stderr, "  %d/%d classes\n", classes_found, classes_needed);
    }
    fprintf(stderr, "S table complete: %d classes\n\n", classes_found);

    // Step 2: Compute class means
    // Group by R = (p-1) mod b
    double cls_sum[64] = {0};
    long cls_count[64] = {0};
    for (int a = 1; a < M; a++) {
        if (!S_known[a]) continue;
        int R = (a - 1) % B;
        cls_sum[R] += S_table[a];
        cls_count[R]++;
    }
    double cls_mean[64];
    for (int R = 0; R < B; R++) {
        if (cls_count[R] > 0)
            cls_mean[R] = cls_sum[R] / cls_count[R];
    }

    double grand = 0; int gc = 0;
    for (int R = 0; R < B; R++) {
        if (cls_count[R] > 0) { grand += cls_mean[R]; gc++; }
    }
    grand /= gc;
    printf("Grand mean: %.6f (expect -0.5)\n\n", grand);

    // Step 3: Sum over primes using lookup
    double s_list[] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    int ns = 6;
    double F[6] = {0};

    long prime_count = 0;
    long checkpoints[] = {1000, 5000, 10000, 50000, 100000,
                          500000, 1000000, 5000000, 10000000};
    int nck = 9;
    int ci = 0;

    printf("%-10s %-10s", "primes", "p_max");
    for (int si = 0; si < ns; si++)
        printf("  s=%-5.2f", s_list[si]);
    printf("\n");

    for (long p = M + 1; p <= max_p; p++) {
        if (!is_prime(p)) continue;
        if (p % 2 == 0 || p % 3 == 0 || p % 5 == 0) continue;

        int cls = (int)(p % M);
        if (!S_known[cls]) continue;

        int S = S_table[cls];
        int R = (p - 1) % B;
        double S_cent = S - cls_mean[R];
        double lp = log((double)p);

        for (int si = 0; si < ns; si++)
            F[si] += S_cent * exp(-s_list[si] * lp);

        prime_count++;

        if (ci < nck && prime_count >= checkpoints[ci]) {
            printf("%-10ld %-10ld", prime_count, p);
            for (int si = 0; si < ns; si++)
                printf("  %+7.3f", F[si]);
            printf("\n");
            ci++;
        }
    }

    printf("\n%-10s %-10s", "FINAL", "");
    for (int si = 0; si < ns; si++)
        printf("  %+7.3f", F[si]);
    printf("  (%ld primes)\n", prime_count);

    return 0;
}
