// Verify sawtooth S computation against direct collision count
#include <stdio.h>
#include <stdlib.h>

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

int collision_count_direct(long g, long p, int b) {
    int count = 0;
    for (long r = 1; r < p; r++) {
        int d_r = (int)((long long)b * r / p);
        long gr = (__int128)g * r % p;
        int d_gr = (int)((long long)b * gr / p);
        if (d_r == d_gr) count++;
    }
    return count;
}

int compute_S_sawtooth(long g, long p, int b) {
    long c = (__int128)b * g % p;
    long Q = (p - 1) / b;
    int S = 0;
    for (long m = 1; m <= Q; m++) {
        long mc_mod_p = (__int128)m * c % p;
        long mb_mod_p = (__int128)m * b % p;
        if (mc_mod_p > mb_mod_p) S++;
        else if (mc_mod_p < mb_mod_p) S--;
    }
    return S;
}

int main() {
    int b = 10;
    int lag = 1;
    int mismatches = 0;

    printf("%-8s %-6s %-6s %-8s %-8s %-8s %-6s\n",
           "p", "Q", "R", "C_dir", "S_saw", "C_saw", "match");

    for (long p = b + 1; p < 1000; p++) {
        if (!is_prime(p)) continue;
        if (p % b == 0) continue;

        long g = power_mod(b, lag, p);
        long Q = (p - 1) / b;
        long R = (p - 1) % b;
        int C_direct = collision_count_direct(g, p, b);
        int S_saw = compute_S_sawtooth(g, p, b);
        int C_saw = (int)Q + S_saw;
        int match = (C_direct == C_saw);
        if (!match) mismatches++;

        printf("%-8ld %-6ld %-6ld %-8d %-8d %-8d %-6s\n",
               p, Q, R, C_direct, S_saw, C_saw, match ? "OK" : "FAIL");
    }

    printf("\nTotal mismatches: %d\n", mismatches);
    return 0;
}
