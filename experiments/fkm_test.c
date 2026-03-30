// Test Step 3 of the proof architecture:
// Does sum_p e(k * b * (1 - b^ell)^{-1} / p) have square-root cancellation?
//
// If the FKM framework applies, then:
//   |sum_{p <= x} e(k * c_p / p)| << pi(x) * x^{-delta}
//
// We compute the partial sums and check if they grow slower than pi(x).

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define PI 3.14159265358979323846

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

long mod_inverse(long a, long p) {
    return power_mod(((a % p) + p) % p, p - 2, p);
}

int main() {
    int b = 10;
    int ell = 1;
    long max_p = 1000000;

    // c_p = b * (1 - b^ell)^{-1} mod p
    // For ell=1: c_p = b * (1 - b)^{-1} mod p = 10 * (-9)^{-1} mod p

    printf("FKM Step 3 Test: sum_p e(k * c_p / p)\n");
    printf("base=%d, lag=%d, primes to %ld\n\n", b, ell, max_p);

    int k_values[] = {1, 2, 3, 5, 7, 10};
    int nk = 6;

    printf("%-8s", "primes");
    for (int ki = 0; ki < nk; ki++)
        printf("  |S(k=%d)|/sqrt(pi)", k_values[ki]);
    printf("  pi(x)   sqrt(pi)\n");

    // Accumulators: real and imaginary parts for each k
    double re[6] = {0}, im[6] = {0};
    long prime_count = 0;

    for (long p = b + 2; p <= max_p; p++) {
        if (!is_prime(p) || p % b == 0) continue;
        prime_count++;

        // c = b * (1 - b^ell)^{-1} mod p
        long g = power_mod(b, ell, p);
        long one_minus_g = ((1 - g) % p + p) % p;
        if (one_minus_g == 0) continue;  // skip if b^ell = 1 mod p
        long c = (__int128)b * mod_inverse(one_minus_g, p) % p;

        for (int ki = 0; ki < nk; ki++) {
            int k = k_values[ki];
            double phase = 2.0 * PI * (double)k * (double)c / (double)p;
            re[ki] += cos(phase);
            im[ki] += sin(phase);
        }

        if (prime_count == 100 || prime_count == 500 ||
            prime_count == 1000 || prime_count == 2000 ||
            prime_count == 5000 || prime_count == 10000 ||
            prime_count == 20000 || prime_count == 50000 ||
            prime_count == 78498) {

            double sqrtpi = sqrt((double)prime_count);
            printf("%-8ld", prime_count);
            for (int ki = 0; ki < nk; ki++) {
                double mag = sqrt(re[ki]*re[ki] + im[ki]*im[ki]);
                printf("  %12.4f     ", mag / sqrtpi);
            }
            printf("  %-7ld %.1f\n", prime_count, sqrtpi);
        }
    }

    // Final summary
    printf("\nFinal magnitudes at %ld primes:\n", prime_count);
    printf("%-6s %-12s %-12s %-12s\n", "k", "|S(k)|", "sqrt(pi)", "|S|/sqrt(pi)");
    double sqrtpi = sqrt((double)prime_count);
    for (int ki = 0; ki < nk; ki++) {
        int k = k_values[ki];
        double mag = sqrt(re[ki]*re[ki] + im[ki]*im[ki]);
        printf("%-6d %-12.4f %-12.4f %-12.4f\n", k, mag, sqrtpi, mag / sqrtpi);
    }

    printf("\nIf |S(k)|/sqrt(pi) is BOUNDED: square-root cancellation holds.\n");
    printf("If |S(k)|/sqrt(pi) GROWS: cancellation is weaker than sqrt.\n");

    return 0;
}
