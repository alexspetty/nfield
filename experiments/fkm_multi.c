// FKM resonance test across bases
// Prediction: k resonates (no cancellation) iff k shares a factor with b-1

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

int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

void test_base(int b, long max_p) {
    int ell = 1;
    int max_k = 12;

    printf("\n=== BASE %d (b-1=%d) ===\n", b, b - 1);
    printf("Prediction: resonance at k with gcd(k, %d) > 1\n", b - 1);

    double re[20] = {0}, im[20] = {0};
    long prime_count = 0;

    for (long p = b + 2; p <= max_p; p++) {
        if (!is_prime(p) || p % b == 0) continue;
        prime_count++;

        long g = power_mod(b, ell, p);
        long one_minus_g = ((1 - g) % p + p) % p;
        if (one_minus_g == 0) continue;
        long c = (__int128)b * power_mod(one_minus_g, p - 2, p) % p;

        for (int k = 1; k <= max_k; k++) {
            double phase = 2.0 * PI * (double)k * (double)c / (double)p;
            re[k] += cos(phase);
            im[k] += sin(phase);
        }
    }

    double sqrtpi = sqrt((double)prime_count);
    printf("  %ld primes, sqrt(pi) = %.1f\n\n", prime_count, sqrtpi);
    printf("  %-4s %-10s %-12s %-8s %-10s\n",
           "k", "|S(k)|", "|S|/sqrt(pi)", "gcd", "status");

    for (int k = 1; k <= max_k; k++) {
        double mag = sqrt(re[k]*re[k] + im[k]*im[k]);
        double ratio = mag / sqrtpi;
        int g = gcd(k, b - 1);
        const char *status;
        if (g > 1 && ratio > 2.0)
            status = "RESONANCE (predicted)";
        else if (g > 1 && ratio <= 2.0)
            status = "gcd>1 but bounded?";
        else if (g == 1 && ratio > 2.0)
            status = "UNEXPECTED RESONANCE";
        else
            status = "cancels";

        printf("  %-4d %-10.2f %-12.4f %-8d %s\n",
               k, mag, ratio, g, status);
    }
}

int main() {
    test_base(3, 200000);
    test_base(7, 500000);
    test_base(10, 1000000);
    test_base(12, 500000);
    test_base(5, 200000);
    return 0;
}
