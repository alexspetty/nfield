// Centered fluctuation sum - OpenMP parallel, direct collision count
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#define MAX_PRIMES 700000

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

// Direct collision count - O(p)
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

int main(int argc, char *argv[]) {
    int b = 10;
    int lag = 1;
    long max_p = 10000000;

    if (argc > 1) max_p = atol(argv[1]);
    if (argc > 2) b = atoi(argv[2]);
    if (argc > 3) lag = atoi(argv[3]);

    // Sieve primes
    long *primes = malloc(MAX_PRIMES * sizeof(long));
    long np = 0;
    for (long p = b + 1; p <= max_p && np < MAX_PRIMES; p++) {
        if (is_prime(p) && p % b != 0) primes[np++] = p;
    }
    fprintf(stderr, "Sieved %ld primes up to %ld\n", np, primes[np-1]);

    // Compute S for each prime in parallel
    int *S_vals = calloc(np, sizeof(int));
    int *cls_vals = calloc(np, sizeof(int));

    // Coprime classes
    int num_classes = 0;
    int coprime_classes[64];
    for (int a = 1; a < b; a++) {
        int g = a, h = b;
        while (h) { int t = h; h = g % h; g = t; }
        if (g == 1) coprime_classes[num_classes++] = a;
    }

    fprintf(stderr, "Computing collision counts...\n");

    #pragma omp parallel for schedule(dynamic, 100)
    for (long i = 0; i < np; i++) {
        long p = primes[i];
        long g = power_mod(b, lag, p);
        int C = collision_count(g, p, b);
        long Q = (p - 1) / b;
        S_vals[i] = C - (int)Q;

        int a = (int)(p % b);
        for (int j = 0; j < num_classes; j++) {
            if (coprime_classes[j] == a) { cls_vals[i] = j; break; }
        }

        if (i % 50000 == 0) fprintf(stderr, "  %ld/%ld\n", i, np);
    }

    fprintf(stderr, "Accumulating sums...\n");

    // Sequential accumulation
    double F_raw = 0.0, F_S = 0.0;
    double class_S_sum[64] = {0};
    long class_count[64] = {0};
    double F_centered = 0.0;
    int S_hist[200] = {0};

    printf("%-10s %-12s %-10s %-10s %-12s %-12s\n",
           "primes", "p_max", "F_raw", "F_S", "F_cent", "F_c/llp");

    for (long i = 0; i < np; i++) {
        long p = primes[i];
        long Q = (p - 1) / b;
        long R = (p - 1) % b;
        int S = S_vals[i];
        int cls = cls_vals[i];

        double denom = (double)(p - 1 - b);
        double qr_term = (denom > 0) ? (double)Q * R / denom : 0.0;
        double phi = (double)S - qr_term;

        F_raw += phi / p;
        F_S += (double)S / p;

        class_S_sum[cls] += S;
        class_count[cls]++;
        double class_mean_S = class_S_sum[cls] / class_count[cls];
        F_centered += ((double)S - class_mean_S) / p;

        if (S + 100 >= 0 && S + 100 < 200) S_hist[S + 100]++;

        long n = i + 1;
        if (n == 100 || n == 500 || n == 1000 || n == 2000 ||
            n == 5000 || n == 10000 || n == 20000 || n == 50000 ||
            n == 100000 || n == 200000 || n == 500000 ||
            n == np) {
            double llp = log(log((double)p));
            printf("%-10ld %-12ld %-10.4f %-10.4f %-12.6f %-12.6f\n",
                   n, p, F_raw, F_S, F_centered, F_centered / llp);
        }
    }

    printf("\n--- S value distribution ---\n");
    for (int i = 0; i < 200; i++) {
        if (S_hist[i] > 0)
            printf("S=%-4d  count=%-8d  frac=%.6f\n",
                   i - 100, S_hist[i], (double)S_hist[i] / np);
    }

    printf("\n--- Per-class means ---\n");
    for (int i = 0; i < num_classes; i++) {
        int a = coprime_classes[i];
        printf("class %d (R=%d): mean_S = %.6f  count = %ld\n",
               a, (a - 1 + b) % b,
               class_count[i] > 0 ? class_S_sum[i] / class_count[i] : 0.0,
               class_count[i]);
    }

    free(primes); free(S_vals); free(cls_vals);
    return 0;
}
