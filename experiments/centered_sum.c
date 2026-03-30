// Compute the centered fluctuation sum: subtract per-class mean bias
// and test whether the centered sum converges at s=1
//
// Also: study the distribution of S values and their Fourier structure

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

// Collision count C(g) for multiplier g at prime p in base b
int collision_count(long g, long p, int b) {
    int count = 0;
    for (long r = 1; r < p; r++) {
        int d_r = (long)((long long)b * r / p);  // floor(br/p)
        long gr = (__int128)g * r % p;
        int d_gr = (long)((long long)b * gr / p);
        if (d_r == d_gr) count++;
    }
    return count;
}

// Mean collision count (exact rational)
double mean_collision(long p, int b) {
    long Q = (p - 1) / b;
    long R = (p - 1) % b;
    // C_bar = Q(b(Q-1) + 2R) / (b(Q-1) + R)
    // denominator = p - 1 - b
    double num = (double)Q * ((double)b * (Q - 1) + 2.0 * R);
    double den = (double)b * (Q - 1) + R;  // = p - 1 - b
    return num / den;
}

int main(int argc, char *argv[]) {
    int b = 10;
    int lag = 1;
    long max_p = 100000;  // default

    if (argc > 1) max_p = atol(argv[1]);
    if (argc > 2) b = atoi(argv[2]);
    if (argc > 3) lag = atoi(argv[3]);

    printf("Centered fluctuation sum: base %d, lag %d, primes to %ld\n\n", b, lag, max_p);

    // Per-class accumulators
    int num_classes = 0;
    int coprime_classes[64];
    for (int a = 1; a < b; a++) {
        // check gcd(a, b) == 1
        int g = a, h = b;
        while (h) { int t = h; h = g % h; g = t; }
        if (g == 1) coprime_classes[num_classes++] = a;
    }

    // Running sums
    double F_raw = 0.0;        // raw fluctuation sum
    double F_S = 0.0;          // sum of S/p (integer part only)
    double F_QR = 0.0;         // sum of QR/((p-1-b)p) (spectral correction)

    // Per-class running sums and counts for online mean
    double class_S_sum[64] = {0};
    long class_count[64] = {0};
    double F_centered = 0.0;   // sum of (S - class_mean_S) / p

    // S value histogram
    int S_hist[100] = {0};  // index = S + 50

    // Milestone tracking
    long milestones[] = {100, 500, 1000, 2000, 5000, 10000, 50000, 100000,
                         500000, 1000000, 5000000, 10000000};
    int nm = sizeof(milestones) / sizeof(milestones[0]);
    int mi = 0;

    long prime_count = 0;

    printf("%-10s %-10s %-10s %-12s %-12s %-12s %-12s\n",
           "primes", "p_max", "F_raw", "F_S", "F_QR", "F_centered", "F_c/loglogp");

    for (long p = b + 1; p <= max_p; p++) {
        if (!is_prime(p)) continue;
        if (p % b == 0) continue;  // skip primes dividing base

        prime_count++;

        long g = power_mod(b, lag, p);  // b^lag mod p
        int C = collision_count(g, p, b);
        long Q = (p - 1) / b;
        long R = (p - 1) % b;
        int S = C - (int)Q;
        double cbar = mean_collision(p, b);
        double phi = (double)C - cbar;
        double qr_term = (double)Q * R / ((double)(p - 1 - b));

        // Which class?
        int cls = -1;
        int a = (int)(p % b);
        for (int i = 0; i < num_classes; i++) {
            if (coprime_classes[i] == a) { cls = i; break; }
        }

        // Accumulate
        F_raw += phi / p;
        F_S += (double)S / p;
        F_QR += qr_term / p;

        // Per-class tracking
        class_S_sum[cls] += S;
        class_count[cls]++;
        double class_mean_S = class_S_sum[cls] / class_count[cls];
        double S_centered = S - class_mean_S;
        F_centered += S_centered / p;

        // Histogram
        if (S + 50 >= 0 && S + 50 < 100) S_hist[S + 50]++;

        // Print at milestones
        if (mi < nm && prime_count >= milestones[mi]) {
            double llp = log(log(p));
            printf("%-10ld %-10ld %-10.4f %-12.4f %-12.4f %-12.6f %-12.6f\n",
                   prime_count, p, F_raw, F_S, F_QR, F_centered, F_centered / llp);
            mi++;
        }
    }

    // Final
    printf("\n--- S value distribution ---\n");
    printf("%-6s %-10s %-10s\n", "S", "count", "fraction");
    for (int i = 0; i < 100; i++) {
        if (S_hist[i] > 0) {
            printf("%-6d %-10d %-10.4f\n", i - 50, S_hist[i],
                   (double)S_hist[i] / prime_count);
        }
    }

    printf("\n--- Per-class means ---\n");
    printf("%-10s %-6s %-10s %-10s\n", "class", "R", "mean_S", "count");
    for (int i = 0; i < num_classes; i++) {
        int a = coprime_classes[i];
        int R = (a - 1 + b) % b;  // R = (p-1) mod b, but p ≡ a mod b so R = (a-1) mod b
        if (class_count[i] > 0) {
            printf("%-10d %-6d %-10.4f %-10ld\n",
                   a, R, class_S_sum[i] / class_count[i], class_count[i]);
        }
    }

    return 0;
}
