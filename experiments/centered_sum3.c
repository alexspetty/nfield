// Centered fluctuation sum - CORRECT collision parameter
// c = b * (1 - g)^{-1} mod p, where g = b^lag mod p

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

long mod_inv(long a, long p) {
    return power_mod(((a % p) + p) % p, p - 2, p);
}

// Compute S via sawtooth with CORRECT c = b(1-g)^{-1} mod p
int compute_S(long g, long p, int b) {
    long one_minus_g = ((1 - g) % p + p) % p;
    if (one_minus_g == 0) return 0;  // g = 1, trivial
    long c = (__int128)b * mod_inv(one_minus_g, p) % p;
    long Q = (p - 1) / b;
    int S = 0;
    for (long m = 1; m <= Q; m++) {
        long mc = (__int128)m * c % p;
        long mb = (__int128)m * b % p;
        if (mc > mb) S++;
        else if (mc < mb) S--;
    }
    return S;
}

int main(int argc, char *argv[]) {
    int b = 10;
    int lag = 1;
    long max_p = 10000000;

    if (argc > 1) max_p = atol(argv[1]);
    if (argc > 2) b = atoi(argv[2]);
    if (argc > 3) lag = atoi(argv[3]);

    printf("Centered fluctuation sum (CORRECT c): base %d, lag %d, primes to %ld\n\n",
           b, lag, max_p);

    // Coprime classes
    int num_classes = 0;
    int coprime_classes[64];
    for (int a = 1; a < b; a++) {
        int g = a, h = b;
        while (h) { int t = h; h = g % h; g = t; }
        if (g == 1) coprime_classes[num_classes++] = a;
    }

    // Running sums
    double F_raw = 0.0;
    double F_S = 0.0;

    // Per-class
    double class_S_sum[64] = {0};
    long class_count[64] = {0};
    double F_centered = 0.0;

    // S histogram
    int S_hist[200] = {0};

    long prime_count = 0;

    printf("%-10s %-12s %-10s %-10s %-12s %-12s\n",
           "primes", "p_max", "F_raw", "F_S", "F_cent", "F_c/llp");

    for (long p = b + 1; p <= max_p; p++) {
        if (!is_prime(p) || p % b == 0) continue;
        prime_count++;

        long g = power_mod(b, lag, p);
        long Q = (p - 1) / b;
        long R = (p - 1) % b;
        int S = compute_S(g, p, b);

        double denom = (double)(p - 1 - b);
        double qr_term = (denom > 0) ? (double)Q * R / denom : 0.0;
        double phi = (double)S - qr_term;

        int cls = -1;
        int a = (int)(p % b);
        for (int i = 0; i < num_classes; i++) {
            if (coprime_classes[i] == a) { cls = i; break; }
        }

        F_raw += phi / p;
        F_S += (double)S / p;

        class_S_sum[cls] += S;
        class_count[cls]++;
        double class_mean_S = class_S_sum[cls] / class_count[cls];
        F_centered += ((double)S - class_mean_S) / p;

        if (S + 100 >= 0 && S + 100 < 200) S_hist[S + 100]++;

        if (prime_count == 100 || prime_count == 500 ||
            prime_count == 1000 || prime_count == 2000 ||
            prime_count == 5000 || prime_count == 10000 ||
            prime_count == 20000 || prime_count == 50000 ||
            prime_count == 100000 || prime_count == 200000 ||
            prime_count == 500000 || prime_count == 664574) {
            double llp = log(log((double)p));
            printf("%-10ld %-12ld %-10.4f %-10.4f %-12.6f %-12.6f\n",
                   prime_count, p, F_raw, F_S, F_centered, F_centered / llp);
        }
    }

    printf("\n--- S value distribution ---\n");
    for (int i = 0; i < 200; i++) {
        if (S_hist[i] > 0)
            printf("S=%-4d  count=%-8d  frac=%.4f\n",
                   i - 100, S_hist[i], (double)S_hist[i] / prime_count);
    }

    printf("\n--- Per-class means ---\n");
    for (int i = 0; i < num_classes; i++) {
        int a = coprime_classes[i];
        printf("class %d (R=%d): mean_S = %.6f  count = %ld\n",
               a, (a - 1 + b) % b,
               class_count[i] > 0 ? class_S_sum[i] / class_count[i] : 0.0,
               class_count[i]);
    }

    printf("\nVerification: F_raw = %.6f\n", F_raw);

    return 0;
}
