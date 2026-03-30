// Test penetration depth across bases
// Does sigma_0 depend on b?

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

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

void probe_base(int b, long max_p) {
    printf("\n=== BASE %d, primes to %ld ===\n", b, max_p);

    // Count coprime classes
    int num_cls = 0;
    int cls_map[64];
    for (int a = 1; a < b; a++) {
        int g = a, h = b;
        while (h) { int t = h; h = g % h; g = t; }
        if (g == 1) cls_map[num_cls++] = a;
    }

    // Sieve and compute
    #define MAXN 80000
    long primes[MAXN];
    int S_vals[MAXN];
    int cls_vals[MAXN];
    long np = 0;

    for (long p = b + 2; p <= max_p && np < MAXN; p++) {
        if (!is_prime(p) || p % b == 0) continue;
        primes[np] = p;

        long g = power_mod(b, 1, p);
        int C = collision_count(g, p, b);
        S_vals[np] = C - (int)((p - 1) / b);

        int a = (int)(p % b);
        for (int i = 0; i < num_cls; i++)
            if (cls_map[i] == a) { cls_vals[np] = i; break; }
        np++;
    }

    // Class means
    double cls_sum[64] = {0};
    long cls_count[64] = {0};
    for (long i = 0; i < np; i++) {
        cls_sum[cls_vals[i]] += S_vals[i];
        cls_count[cls_vals[i]]++;
    }
    double cls_mean[64];
    for (int i = 0; i < num_cls; i++)
        cls_mean[i] = cls_sum[i] / cls_count[i];

    // F°(s) at key s values
    double s_list[] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    int ns = 6;
    double F[6] = {0};

    for (long i = 0; i < np; i++) {
        double sc = S_vals[i] - cls_mean[cls_vals[i]];
        double lp = log((double)primes[i]);
        for (int si = 0; si < ns; si++)
            F[si] += sc * exp(-s_list[si] * lp);
    }

    printf("  %ld primes, p_max = %ld\n  ", np, primes[np-1]);
    for (int si = 0; si < ns; si++)
        printf("s=%.1f:%+7.3f  ", s_list[si], F[si]);
    printf("\n");

    // Check stability: compute at half the primes too
    double F_half[6] = {0};
    long half = np / 2;
    for (long i = 0; i < half; i++) {
        double sc = S_vals[i] - cls_mean[cls_vals[i]];
        double lp = log((double)primes[i]);
        for (int si = 0; si < ns; si++)
            F_half[si] += sc * exp(-s_list[si] * lp);
    }

    printf("  half: ");
    for (int si = 0; si < ns; si++)
        printf("s=%.1f:%+7.3f  ", s_list[si], F_half[si]);
    printf("\n  drift:");
    for (int si = 0; si < ns; si++) {
        double drift = fabs(F[si] - F_half[si]);
        printf("s=%.1f: %6.3f  ", s_list[si], drift);
    }
    printf("\n");
}

int main() {
    probe_base(3, 200000);
    probe_base(5, 300000);
    probe_base(7, 500000);
    probe_base(10, 1000000);
    probe_base(12, 500000);
    return 0;
}
