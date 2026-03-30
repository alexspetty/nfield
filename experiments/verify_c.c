// Test different collision parameter definitions
#include <stdio.h>

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

long mod_inv(long a, long p) {
    return power_mod(((a % p) + p) % p, p - 2, p);
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

int compute_S(long c, long p, int b) {
    long Q = (p - 1) / b;
    int S = 0;
    for (long m = 1; m <= Q; m++) {
        long mc = (__int128)m * c % p;
        long mb = (__int128)m * b % p;
        if (mc > mb) S++;
        else if (mc < mb) S--;
    }
    return S;
}

int main() {
    int b = 10;
    int lag = 1;
    int ok1 = 0, ok2 = 0, ok3 = 0, total = 0;

    printf("%-6s %-4s %-6s %-6s %-6s %-6s %-6s\n",
           "p", "Q", "C_dir", "c=bg", "c=b/(1-g)", "c=g", "S_true");

    for (long p = b + 1; p < 500; p++) {
        if (!is_prime(p) || p % b == 0) continue;
        total++;

        long g = power_mod(b, lag, p);
        long Q = (p - 1) / b;
        int C_dir = collision_count_direct(g, p, b);
        int S_true = C_dir - (int)Q;

        // c1 = b*g mod p
        long c1 = (__int128)b * g % p;
        int S1 = compute_S(c1, p, b);

        // c2 = b * (1 - g)^{-1} mod p
        long one_minus_g = ((1 - g) % p + p) % p;
        long inv_1mg = mod_inv(one_minus_g, p);
        long c2 = (__int128)b * inv_1mg % p;
        int S2 = compute_S(c2, p, b);

        // c3 = g
        int S3 = compute_S(g, p, b);

        if (S1 == S_true) ok1++;
        if (S2 == S_true) ok2++;
        if (S3 == S_true) ok3++;

        printf("%-6ld %-4ld %-6d %-6d %-6d %-6d %-6d\n",
               p, Q, C_dir, S1, S2, S3, S_true);
    }

    printf("\nMatches: c=bg: %d/%d  c=b/(1-g): %d/%d  c=g: %d/%d\n",
           ok1, total, ok2, total, ok3, total);

    return 0;
}
