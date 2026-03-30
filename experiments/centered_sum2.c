// Centered fluctuation sum - optimized version
// Uses direct S computation via sawtooth comparison

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
    long result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) result = (__int128)result * base % mod;
        base = (__int128)base * base % mod;
        exp >>= 1;
    }
    return result;
}

// Compute S directly via the sawtooth form
// S = sum_{m=1}^{Q} sgn( ((mc/p)) - ((mb/p)) )
// where ((x)) = {x} - 1/2, c = b*g mod p
int compute_S(long g, long p, int b) {
    long c = (__int128)b * g % p;
    long Q = (p - 1) / b;
    int S = 0;

    for (long m = 1; m <= Q; m++) {
        // ((mc/p)) = (mc mod p)/p - 0.5
        // ((mb/p)) = (mb mod p)/p - 0.5 = (mb mod p)/p - 0.5
        // But mb < p*b, and mb mod p... actually mb might be > p
        // We need mc mod p and mb mod p
        long mc_mod_p = (__int128)m * c % p;
        long mb_mod_p = (__int128)m * b % p;
        // sgn(mc_mod_p/p - 0.5 - (mb_mod_p/p - 0.5))
        // = sgn(mc_mod_p - mb_mod_p)  (since dividing by p preserves sign)
        if (mc_mod_p > mb_mod_p) S++;
        else if (mc_mod_p < mb_mod_p) S--;
        // if equal, sgn = 0 (shouldn't happen for prime p)
    }
    return S;
}

// Also compute C directly for verification
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
    long max_p = 1000000;

    if (argc > 1) max_p = atol(argv[1]);
    if (argc > 2) b = atoi(argv[2]);
    if (argc > 3) lag = atoi(argv[3]);

    printf("Centered fluctuation sum: base %d, lag %d, primes to %ld\n\n", b, lag, max_p);

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
    double F_QR = 0.0;

    // Per-class running sums for online mean
    double class_S_sum[64] = {0};
    long class_count[64] = {0};
    double F_centered = 0.0;

    // For the RETROSPECTIVE centered sum (subtract final class mean)
    // we need to store all (S, p, class) values
    // But that's memory-intensive. Instead, compute both:
    // F_centered_online: subtract running mean (causal)
    // and we'll note the trend

    long prime_count = 0;

    printf("%-10s %-12s %-10s %-10s %-10s %-12s %-12s\n",
           "primes", "p_max", "F_raw", "F_S", "F_QR", "F_cent", "F_c/llp");

    for (long p = b + 1; p <= max_p; p++) {
        if (!is_prime(p)) continue;
        if (p % b == 0) continue;

        prime_count++;

        long g = power_mod(b, lag, p);
        long Q = (p - 1) / b;
        long R = (p - 1) % b;
        int S = compute_S(g, p, b);

        // Raw phi = S - QR/(p-1-b)
        double denom = (double)(p - 1 - b);
        double qr_term = (denom > 0) ? (double)Q * R / denom : 0.0;
        double phi = (double)S - qr_term;

        // Which class?
        int cls = -1;
        int a = (int)(p % b);
        for (int i = 0; i < num_classes; i++) {
            if (coprime_classes[i] == a) { cls = i; break; }
        }

        // Accumulate raw sums
        F_raw += phi / p;
        F_S += (double)S / p;
        F_QR += qr_term / p;

        // Per-class online mean
        class_S_sum[cls] += S;
        class_count[cls]++;
        double class_mean_S = class_S_sum[cls] / class_count[cls];

        // Centered: subtract per-class running mean of S
        double S_centered = S - class_mean_S;
        F_centered += S_centered / p;

        // Print at logarithmic intervals
        if (prime_count == 100 || prime_count == 500 ||
            prime_count == 1000 || prime_count == 2000 ||
            prime_count == 5000 || prime_count == 10000 ||
            prime_count == 20000 || prime_count == 50000 ||
            prime_count == 78498 ||  // primes below 10^6
            prime_count % 100000 == 0) {
            double llp = log(log((double)p));
            printf("%-10ld %-12ld %-10.4f %-10.4f %-10.4f %-12.6f %-12.6f\n",
                   prime_count, p, F_raw, F_S, F_QR, F_centered, F_centered / llp);
        }
    }

    printf("\n--- Per-class final means ---\n");
    for (int i = 0; i < num_classes; i++) {
        int a = coprime_classes[i];
        int R = (a - 1 + b) % b;
        if (class_count[i] > 0) {
            printf("class %d (R=%d): mean_S = %.6f  count = %ld\n",
                   a, R, class_S_sum[i] / class_count[i], class_count[i]);
        }
    }

    // Verify: F_raw should equal F_S - F_QR
    printf("\nVerification: F_S - F_QR = %.6f, F_raw = %.6f\n", F_S - F_QR, F_raw);

    return 0;
}
