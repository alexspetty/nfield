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

int main() {
    int bases[] = {3, 6, 7, 10, 12};
    int nbases = 5;
    long long max_p = 2000000;
    int ell = 1;
    
    for (int bi = 0; bi < nbases; bi++) {
        int b = bases[bi];
        
        int cap = max_p / 4;
        long long *primes = malloc(cap * sizeof(long long));
        int np = 0;
        for (long long p = b + 2; p <= max_p; p++) {
            if (is_prime(p) && p % b != 0) {
                int dominated = 0;
                for (int f = 2; f * f <= b; f++)
                    if (b % f == 0 && p % f == 0) { dominated = 1; break; }
                if (!dominated && np < cap) primes[np++] = p;
            }
        }
        
        double *phi_p = calloc(np, sizeof(double));
        
        #pragma omp parallel for schedule(dynamic, 100)
        for (int i = 0; i < np; i++) {
            long long p = primes[i];
            int Q = (p - 1) / b;
            int R = (p - 1) % b;
            
            long long bell = mod_pow(b, ell, p);
            long long inv = mod_pow((1 - bell % p + p) % p, p - 2, p);
            long long c = (long long)b * inv % p;
            
            int C_half = 0;
            for (int m = 1; m <= Q; m++) {
                long long mc_mod = ((long long)m * c) % p;
                if (mc_mod > (long long)m * b) C_half++;
            }
            int C = 2 * C_half;
            int S = C - Q;
            
            int denom = b * (Q - 1) + R;
            double C_bar = (denom > 0) ? (double)Q * (b * (Q - 1) + 2 * R) / denom : 0;
            phi_p[i] = (C - C_bar) / p;
        }
        
        double running = 0;
        for (int i = 0; i < np; i++) running += phi_p[i];
        
        double llp = log(log(primes[np-1]));
        printf("base %2d: %6d primes to %7lld, F = %8.4f, F/loglogp = %8.5f, 2/3 = %8.5f\n",
               b, np, primes[np-1], running, running/llp, -2.0/3);
        
        free(primes);
        free(phi_p);
    }
    return 0;
}
