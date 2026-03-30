// Deep probe: find where F°(s) transitions from convergence to divergence
// Use OpenMP for speed

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
    long max_p = 2000000;

    #define MAX_P 150000
    long primes[MAX_P];
    int S_vals[MAX_P];
    int cls_vals[MAX_P];
    long np = 0;

    fprintf(stderr, "Sieving...\n");
    for (long p = b + 2; p <= max_p && np < MAX_P; p++) {
        if (!is_prime(p) || p % b == 0) { continue; }
        primes[np] = p;
        np++;
    }
    fprintf(stderr, "Found %ld primes. Computing collisions...\n", np);

    #pragma omp parallel for schedule(dynamic, 200)
    for (long i = 0; i < np; i++) {
        long p = primes[i];
        long g = power_mod(b, 1, p);
        int C = collision_count(g, p, b);
        int Q = (int)((p - 1) / b);
        S_vals[i] = C - Q;

        int a = (int)(p % b);
        int coprime[] = {1, 3, 7, 9};
        for (int j = 0; j < 4; j++)
            if (coprime[j] == a) { cls_vals[i] = j; break; }

        if (i % 20000 == 0) fprintf(stderr, "  %ld/%ld\n", i, np);
    }

    fprintf(stderr, "Computing class means and F°(s)...\n");

    double class_sum[4] = {0};
    long class_count[4] = {0};
    for (long i = 0; i < np; i++) {
        class_sum[cls_vals[i]] += S_vals[i];
        class_count[cls_vals[i]]++;
    }
    double class_mean[4];
    for (int i = 0; i < 4; i++)
        class_mean[i] = class_sum[i] / class_count[i];

    // Fine-grained s values around the transition
    double s_list[] = {1.0, 0.9, 0.8, 0.75, 0.7, 0.65, 0.6, 0.55, 0.5};
    int ns = 9;

    long checkpoints[] = {5000, 10000, 20000, 50000, 100000, 148930};
    int nck = 6;

    double F[9] = {0};
    int ci = 0;

    printf("%-8s", "primes");
    for (int si = 0; si < ns; si++)
        printf("  s=%-5.2f", s_list[si]);
    printf("\n");

    for (long i = 0; i < np; i++) {
        double S_cent = S_vals[i] - class_mean[cls_vals[i]];
        double logp = log((double)primes[i]);

        for (int si = 0; si < ns; si++)
            F[si] += S_cent * exp(-s_list[si] * logp);

        long n = i + 1;
        if (ci < nck && n >= checkpoints[ci]) {
            printf("%-8ld", n);
            for (int si = 0; si < ns; si++)
                printf("  %+8.3f", F[si]);
            printf("\n");
            ci++;
        }
    }

    printf("\n%-8s", "FINAL");
    for (int si = 0; si < ns; si++)
        printf("  %+8.3f", F[si]);
    printf("  (%ld primes, p_max=%ld)\n", np, primes[np-1]);

    return 0;
}
