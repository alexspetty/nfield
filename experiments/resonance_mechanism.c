// Verify: resonant Fourier modes = class mean bias
//
// For base 10: the resonant modes are k = 3, 6, 9, ...
// The exponential sum e(kc/p) should have a class-dependent
// nonzero average that exactly accounts for the S class mean.
//
// Specifically: for each class R, compute the average of
// e(kc/p) over primes in that class. This should be a
// constant that, when multiplied by the Fourier coefficient
// and summed over resonant k, gives S_bar(R).

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

int main() {
    int b = 10;
    long max_p = 1000000;

    printf("Resonance mechanism: base %d, primes to %ld\n\n", b, max_p);

    // Coprime classes
    int classes[] = {1, 3, 7, 9};  // p mod 10
    int R_vals[] = {0, 2, 6, 8};   // (p-1) mod 10
    int nc = 4;

    // For each class, compute:
    // 1. Mean of S
    // 2. Mean of e(kc/p) for k = 1..12
    double S_sum[4] = {0};
    double ek_re[4][13] = {{0}};  // [class][k]
    double ek_im[4][13] = {{0}};
    long count[4] = {0};

    for (long p = b + 2; p <= max_p; p++) {
        if (!is_prime(p) || p % b == 0) continue;

        int a = (int)(p % b);
        int cls = -1;
        for (int i = 0; i < nc; i++)
            if (classes[i] == a) { cls = i; break; }
        if (cls < 0) continue;

        // Collision count
        long g = power_mod(b, 1, p);
        int C = 0;
        for (long r = 1; r < p; r++) {
            int d_r = (int)((long long)b * r / p);
            long gr = (__int128)g * r % p;
            int d_gr = (int)((long long)b * gr / p);
            if (d_r == d_gr) C++;
        }
        int Q = (int)((p - 1) / b);
        int S = C - Q;
        S_sum[cls] += S;

        // Collision parameter
        long one_minus_g = ((1 - g) % p + p) % p;
        long c = (__int128)b * power_mod(one_minus_g, p - 2, p) % p;

        // Exponential sums
        for (int k = 1; k <= 12; k++) {
            double phase = 2.0 * PI * (double)k * (double)c / (double)p;
            ek_re[cls][k] += cos(phase);
            ek_im[cls][k] += sin(phase);
        }

        count[cls]++;
    }

    // Print class means
    printf("Per-class mean of S:\n");
    for (int i = 0; i < nc; i++) {
        printf("  class %d (R=%d): S_bar = %.6f  (n=%ld)\n",
               classes[i], R_vals[i], S_sum[i] / count[i], count[i]);
    }

    // Print per-class average of e(kc/p) for each k
    printf("\nPer-class average of e(kc/p):\n");
    printf("%-4s", "k");
    for (int i = 0; i < nc; i++)
        printf("  R=%-2d (re)    R=%-2d (im) ", R_vals[i], R_vals[i]);
    printf("  gcd(k,%d)\n", b - 1);

    for (int k = 1; k <= 12; k++) {
        printf("%-4d", k);
        for (int i = 0; i < nc; i++) {
            double avg_re = ek_re[i][k] / count[i];
            double avg_im = ek_im[i][k] / count[i];
            printf("  %+8.5f     %+8.5f  ", avg_re, avg_im);
        }
        printf("  %d\n", gcd(k, b - 1));
    }

    // Show the magnitude of per-class averages
    printf("\nMagnitude |avg e(kc/p)| per class:\n");
    printf("%-4s  gcd", "k");
    for (int i = 0; i < nc; i++)
        printf("    R=%-2d   ", R_vals[i]);
    printf("\n");

    for (int k = 1; k <= 12; k++) {
        printf("%-4d  %-3d", k, gcd(k, b - 1));
        for (int i = 0; i < nc; i++) {
            double avg_re = ek_re[i][k] / count[i];
            double avg_im = ek_im[i][k] / count[i];
            double mag = sqrt(avg_re*avg_re + avg_im*avg_im);
            printf("  %8.5f  ", mag);
        }
        printf("\n");
    }

    return 0;
}
