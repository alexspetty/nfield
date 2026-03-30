#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#endif

int is_prime(long long n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (long long i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

long long mod_pow(long long base, long long exp, long long mod) {
    long long result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) result = result * base % mod;
        exp >>= 1;
        base = base * base % mod;
    }
    return result;
}

int main(int argc, char **argv) {
    int b = 10;
    long long max_p = argc > 1 ? atoll(argv[1]) : 1000000;
    int ell = 1;
    
    /* Collect primes */
    int cap = max_p / 4;
    long long *primes = malloc(cap * sizeof(long long));
    int np = 0;
    for (long long p = 12; p <= max_p; p++) {
        if (is_prime(p) && p % 2 != 0 && p % 5 != 0 && p > b + 1) {
            if (np >= cap) break;
            primes[np++] = p;
        }
    }
    
    printf("Testing F(1, ell=%d) with %d primes up to %lld\n", ell, np, primes[np-1]);
    
    /* Compute phi for each prime in parallel */
    double *phi_over_p = calloc(np, sizeof(double));
    
    #pragma omp parallel for schedule(dynamic, 100)
    for (int i = 0; i < np; i++) {
        long long p = primes[i];
        int Q = (p - 1) / b;
        int R = (p - 1) % b;
        
        /* c = -10/9 mod p = -10 * 9^{-1} mod p */
        long long inv9 = mod_pow(9, p - 2, p);
        long long c = ((-10 * inv9) % p + p) % p;
        
        /* C/2 = #{m : mc mod p > mb} */
        int C_half = 0;
        for (int m = 1; m <= Q; m++) {
            long long mc_mod = ((long long)m * c) % p;
            if (mc_mod > (long long)m * b)
                C_half++;
        }
        int C = 2 * C_half;
        int S = C - Q;
        
        int denom = b * (Q - 1) + R;
        double C_bar = (denom > 0) ? (double)Q * (b * (Q - 1) + 2 * R) / denom : 0;
        double phi = C - C_bar;
        
        phi_over_p[i] = phi / p;
    }
    
    /* Running sum with checkpoints */
    double running = 0;
    int checkpoints[] = {100, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000, np};
    int ncp = 10;
    int ci = 0;
    
    printf("%7s %10s %12s %14s %12s\n", "N", "p", "F", "F/loglogp", "increment");
    double prev = 0;
    
    for (int i = 0; i < np; i++) {
        running += phi_over_p[i];
        if (ci < ncp && i + 1 >= checkpoints[ci]) {
            double llp = log(log(primes[i]));
            printf("%7d %10lld %12.4f %14.4f %12.4f\n",
                   i + 1, primes[i], running, running / llp, running - prev);
            prev = running;
            ci++;
        }
    }
    
    free(primes);
    free(phi_over_p);
    return 0;
}
