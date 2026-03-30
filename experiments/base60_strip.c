// Base 60: the Babylonian base in the critical strip
// b-1 = 59 (prime!), b^2 = 3600, phi(3600) = 960 characters
// Compute F°(s) at various s values

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

int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main() {
    int b = 60;
    long max_p = 50000;

    printf("BASE 60 (Babylonian): b-1 = 59 (prime)\n");
    printf("b^2 = %d, phi(b^2) = ", b*b);

    // compute phi(3600) = 3600 * (1-1/2) * (1-1/3) * (1-1/5) = 3600 * 1/2 * 2/3 * 4/5 = 960
    printf("960\n\n");

    // Count coprime classes
    int num_cls = 0;
    for (int a = 1; a < b; a++)
        if (gcd(a, b) == 1) num_cls++;
    printf("Coprime classes mod %d: %d (gate width = %d)\n\n", b, num_cls, b-1);

    // Compute S and class means
    #define MAXP 5000
    long primes[MAXP];
    int S_vals[MAXP];
    int R_vals[MAXP];
    long np = 0;

    fprintf(stderr, "Computing collisions for base 60...\n");

    for (long p = b + 2; p <= max_p && np < MAXP; p++) {
        if (!is_prime(p) || p % 2 == 0 || p % 3 == 0 || p % 5 == 0)
            continue;
        primes[np] = p;

        long g = power_mod(b, 1, p);
        int C = collision_count(g, p, b);
        int Q = (int)((p - 1) / b);
        S_vals[np] = C - Q;
        R_vals[np] = (int)((p - 1) % b);
        np++;

        if (np % 500 == 0) fprintf(stderr, "  %ld primes\n", np);
    }

    fprintf(stderr, "Done: %ld primes up to %ld\n", np, primes[np-1]);

    // Class means by R
    double cls_sum[64] = {0};
    long cls_count[64] = {0};
    for (long i = 0; i < np; i++) {
        int R = R_vals[i];
        cls_sum[R] += S_vals[i];
        cls_count[R]++;
    }
    double cls_mean[64];
    for (int R = 0; R < b; R++) {
        if (cls_count[R] > 0)
            cls_mean[R] = cls_sum[R] / cls_count[R];
    }

    // Grand mean
    double grand = 0;
    int gc = 0;
    for (int R = 0; R < b; R++) {
        if (cls_count[R] > 0) {
            grand += cls_mean[R];
            gc++;
        }
    }
    grand /= gc;
    printf("Grand mean: %.6f (expect -0.5)\n\n", grand);

    // F°(s) at various s
    double s_list[] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    int ns = 6;
    double F[6] = {0};
    double F_half[6] = {0};
    long half = np / 2;

    for (long i = 0; i < np; i++) {
        double S_cent = S_vals[i] - cls_mean[R_vals[i]];
        double lp = log((double)primes[i]);

        for (int si = 0; si < ns; si++) {
            double term = S_cent * exp(-s_list[si] * lp);
            F[si] += term;
            if (i < half) F_half[si] += term;
        }
    }

    printf("F°(s) for base 60 (%ld primes, p_max = %ld):\n", np, primes[np-1]);
    printf("%-8s %-12s %-12s %-12s\n", "s", "F°(s)", "F°(half)", "drift");
    for (int si = 0; si < ns; si++) {
        double drift = fabs(F[si] - F_half[si]);
        printf("%-8.2f %-+12.4f %-+12.4f %-12.4f%s\n",
               s_list[si], F[si], F_half[si], drift,
               drift < 0.05 ? "  stable" : drift < 0.2 ? "  borderline" : "  drifting");
    }

    return 0;
}
