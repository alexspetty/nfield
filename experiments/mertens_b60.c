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
    long long r = 1; base %= mod;
    while (exp > 0) {
        if (exp & 1) r = r * base % mod;
        exp >>= 1; base = base * base % mod;
    }
    return r;
}

int main(int argc, char **argv) {
    int b = 60;
    long long max_p = argc > 1 ? atoll(argv[1]) : 10000000;
    int ell = 1;
    
    int cap = max_p / 3;
    long long *primes = malloc(cap * sizeof(long long));
    int np = 0;
    for (long long p = b + 2; p <= max_p && np < cap; p++) {
        if (!is_prime(p)) continue;
        if (p == 2 || p == 3 || p == 5) continue;
        if (np < cap) primes[np++] = p;
    }
    
    printf("base=%d, %d primes to %lld, ell=%d\n", b, np, primes[np-1], ell);
    
    double *phi_p = calloc(np, sizeof(double));
    
    #pragma omp parallel for schedule(dynamic, 100)
    for (int i = 0; i < np; i++) {
        long long p = primes[i];
        int Q = (p - 1) / b;
        int R = (p - 1) % b;
        
        long long bell = mod_pow(b, ell, p);
        long long omg = (1 - bell % p + p) % p;
        if (omg == 0) { phi_p[i] = 0; continue; }
        long long inv = mod_pow(omg, p - 2, p);
        long long c = (long long)b * inv % p;
        
        int C_half = 0;
        for (int m = 1; m <= Q; m++) {
            long long mc_mod = ((long long)m * c) % p;
            if (mc_mod > (long long)m * b) C_half++;
        }
        int C = 2 * C_half;
        int denom = b * (Q - 1) + R;
        double C_bar = (denom > 0) ? (double)Q * (b*(Q-1) + 2*R) / denom : 0;
        phi_p[i] = (C - C_bar) / p;
    }
    
    double running = 0;
    int checks[] = {1000, 5000, 10000, 50000, 100000, 200000, 500000, np};
    int nch = 8, ci = 0;
    
    printf("%7s %10s %12s %14s\n", "N", "p", "F", "F/loglogp");
    
    for (int i = 0; i < np; i++) {
        running += phi_p[i];
        if (ci < nch && i + 1 >= checks[ci]) {
            double llp = log(log(primes[i]));
            printf("%7d %10lld %12.6f %14.6f\n",
                   i+1, primes[i], running, running/llp);
            ci++;
        }
    }
    
    free(primes); free(phi_p);
    return 0;
}
