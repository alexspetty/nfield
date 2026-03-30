// Probe: does the centered sum F°(s) converge for s < 1?
// If so, the collision structure sees into the critical strip.
//
// F°(s) = sum_p S°_p / p^s
// At s=1: converges (proved). At s<1: unknown.

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

int main() {
    int b = 10;
    int lag = 1;
    long max_p = 500000;

    printf("Probing F°(s) for s = 1.0, 0.95, 0.9, 0.8, 0.7, 0.5\n");
    printf("Base %d, lag %d, primes to %ld\n\n", b, lag, max_p);

    // Sieve primes and compute S
    #define MAX_P 50000
    long primes[MAX_P];
    int S_vals[MAX_P];
    int cls_vals[MAX_P];
    long np = 0;

    int coprime_classes[] = {1, 3, 7, 9};
    int R_for_class[] = {0, 2, 6, 8};

    for (long p = b + 2; p <= max_p && np < MAX_P; p++) {
        if (!is_prime(p) || p % b == 0) continue;

        long g = power_mod(b, lag, p);
        int C = collision_count(g, p, b);
        int Q = (int)((p - 1) / b);
        primes[np] = p;
        S_vals[np] = C - Q;

        int a = (int)(p % b);
        for (int i = 0; i < 4; i++)
            if (coprime_classes[i] == a) { cls_vals[np] = i; break; }

        np++;
    }

    printf("Computed %ld primes\n\n", np);

    // Compute class means
    double class_sum[4] = {0};
    long class_count[4] = {0};
    for (long i = 0; i < np; i++) {
        class_sum[cls_vals[i]] += S_vals[i];
        class_count[cls_vals[i]]++;
    }
    double class_mean[4];
    for (int i = 0; i < 4; i++)
        class_mean[i] = class_sum[i] / class_count[i];

    // Compute F°(s) at various s values
    double s_vals[] = {1.0, 0.95, 0.9, 0.85, 0.8, 0.7, 0.5};
    int ns = 7;

    // Print at checkpoints
    long checkpoints[] = {1000, 2000, 5000, 10000, 20000, 41000};
    int nck = 6;

    printf("%-8s", "primes");
    for (int si = 0; si < ns; si++)
        printf("  s=%-5.2f", s_vals[si]);
    printf("\n");

    double F[7] = {0};

    int ci = 0;
    for (long i = 0; i < np; i++) {
        double S_cent = S_vals[i] - class_mean[cls_vals[i]];

        for (int si = 0; si < ns; si++)
            F[si] += S_cent / pow((double)primes[i], s_vals[si]);

        long n = i + 1;
        if (ci < nck && n >= checkpoints[ci]) {
            printf("%-8ld", n);
            for (int si = 0; si < ns; si++)
                printf("  %+7.4f", F[si]);
            printf("\n");
            ci++;
        }
    }

    printf("\n%-8s", "FINAL");
    for (int si = 0; si < ns; si++)
        printf("  %+7.4f", F[si]);
    printf("  (%ld primes)\n", np);

    // Check: is F°(s) growing or stable for s < 1?
    printf("\nInterpretation:\n");
    printf("  If F°(s) is STABLE: collision structure sees into the strip at s.\n");
    printf("  If F°(s) GROWS: the collision structure stops at s=1.\n");

    return 0;
}
