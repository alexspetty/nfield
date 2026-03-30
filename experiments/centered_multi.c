// Centered fluctuation sum: multiple lags and bases
// Tests universality of centered convergence

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

void run_one(int b, int lag, long max_p) {
    printf("\n========== BASE %d, LAG %d, primes to %ld ==========\n", b, lag, max_p);

    int num_classes = 0;
    int coprime_classes[64];
    for (int a = 1; a < b; a++) {
        int g = a, h = b;
        while (h) { int t = h; h = g % h; g = t; }
        if (g == 1) coprime_classes[num_classes++] = a;
    }

    // Sieve primes
    long *primes = malloc(200000 * sizeof(long));
    long np = 0;
    for (long p = b + 2; p <= max_p && np < 200000; p++) {
        if (is_prime(p) && p % b != 0) primes[np++] = p;
    }

    // Compute C and S in parallel
    int *S_vals = calloc(np, sizeof(int));
    int *cls_vals = calloc(np, sizeof(int));

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
    }

    // Accumulate
    double F_raw = 0.0;
    double class_S_sum[64] = {0};
    long class_count[64] = {0};
    double F_centered = 0.0;

    printf("%-10s %-12s %-10s %-12s %-12s\n",
           "primes", "p_max", "F_raw", "F_cent", "F_c/llp");

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

        class_S_sum[cls] += S;
        class_count[cls]++;
        double class_mean_S = class_S_sum[cls] / class_count[cls];
        F_centered += ((double)S - class_mean_S) / p;

        long n = i + 1;
        if (n == 1000 || n == 5000 || n == 10000 ||
            n == 50000 || n == 100000 || n == np) {
            double llp = log(log((double)p));
            printf("%-10ld %-12ld %-10.4f %-12.6f %-12.6f\n",
                   n, p, F_raw, F_centered, F_centered / llp);
        }
    }

    printf("Per-class means:\n");
    for (int i = 0; i < num_classes; i++) {
        int a = coprime_classes[i];
        if (class_count[i] > 0)
            printf("  class %d (R=%d): mean_S = %.4f  n=%ld\n",
                   a, (a-1+b)%b, class_S_sum[i]/class_count[i], class_count[i]);
    }

    free(primes); free(S_vals); free(cls_vals);
}

int main() {
    // Base 10, multiple lags
    run_one(10, 1, 1000000);
    run_one(10, 2, 1000000);
    run_one(10, 3, 1000000);
    run_one(10, 5, 1000000);

    // Other bases, lag 1
    run_one(3, 1, 200000);
    run_one(7, 1, 500000);
    run_one(12, 1, 500000);

    return 0;
}
