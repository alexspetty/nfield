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
    int b = argc > 1 ? atoi(argv[1]) : 10;
    long long max_p = argc > 2 ? atoll(argv[2]) : 5000000;
    
    /* Collect primes coprime to b */
    int cap = max_p / 3;
    long long *primes = malloc(cap * sizeof(long long));
    int np = 0;
    for (long long p = b + 2; p <= max_p && np < cap; p++) {
        if (!is_prime(p)) continue;
        int dominated = 0;
        /* skip primes dividing b */
        long long bb = b;
        for (long long f = 2; f <= bb; f++) {
            if (bb % f == 0 && p == f) { dominated = 1; break; }
            while (bb % f == 0) bb /= f;
        }
        if (!dominated) primes[np++] = p;
    }
    
    printf("base=%d, %d primes to %lld\n\n", b, np, primes[np-1]);
    
    /* For each lag ell = 1..5, compute F and F/sum(1/p) */
    for (int ell = 1; ell <= 5; ell++) {
        double F = 0, sum_inv_p = 0;
        
        int checks[] = {1000, 5000, 10000, 50000, 100000, np};
        int nch = 6, ci = 0;
        
        if (ell == 1)
            printf("%5s %8s %10s %10s %12s %12s\n",
                   "ell", "N", "p", "F", "F/sum1p", "F/loglogp");
        
        for (int i = 0; i < np; i++) {
            long long p = primes[i];
            int Q = (p - 1) / b;
            int R = (p - 1) % b;
            
            long long bell = mod_pow(b, ell, p);
            long long omg = (1 - bell % p + p) % p;
            if (omg == 0) { sum_inv_p += 1.0/p; continue; }
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
            
            F += (C - C_bar) / p;
            sum_inv_p += 1.0 / p;
            
            if (ci < nch && i + 1 >= checks[ci]) {
                double llp = log(log(p));
                printf("%5d %8d %10lld %10.4f %12.6f %12.6f\n",
                       ell, i+1, p, F, F/sum_inv_p, F/llp);
                ci++;
            }
        }
        printf("\n");
    }
    
    free(primes);
    return 0;
}
