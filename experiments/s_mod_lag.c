// Does S at lag ell depend on p mod b^(ell+1)?
#include <stdio.h>
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

void test_lag(int b, int lag, long max_p) {
    long modulus_try[] = {(long)b*b, (long)b*b*b, (long)b*b*b*b};
    // For lag 1: b^2. For lag 2: b^3? For lag 3: b^4?
    // Or maybe it's always b^(lag+1)?

    long mod = 1;
    for (int i = 0; i <= lag; i++) mod *= b;

    printf("\n=== BASE %d, LAG %d, testing p mod %ld ===\n", b, lag, mod);

    if (mod > 500) {
        printf("  modulus too large for small-prime test, skipping\n");
        return;
    }

    int s_first[1000];
    int s_seen[1000];
    int s_varies[1000];
    for (int i = 0; i < 1000; i++) { s_seen[i] = 0; s_varies[i] = 0; }

    for (long p = b + 2; p <= max_p; p++) {
        if (!is_prime(p) || p % b == 0) continue;

        long g = power_mod(b, lag, p);
        int C = collision_count(g, p, b);
        int Q = (int)((p - 1) / b);
        int S = C - Q;

        int cls = (int)(p % mod);
        if (!s_seen[cls]) {
            s_first[cls] = S;
            s_seen[cls] = 1;
        } else if (S != s_first[cls]) {
            s_varies[cls] = 1;
        }
    }

    int total = 0, varies = 0;
    for (int i = 0; i < (int)mod; i++) {
        if (s_seen[i]) {
            total++;
            if (s_varies[i]) varies++;
        }
    }

    printf("  %d classes seen, %d vary: %s\n", total, varies,
           varies == 0 ? "DETERMINED" : "NOT determined");

    // Also test smaller modulus b^lag
    long mod2 = 1;
    for (int i = 0; i < lag; i++) mod2 *= b;

    if (mod2 > 1 && mod2 < mod) {
        for (int i = 0; i < 1000; i++) { s_seen[i] = 0; s_varies[i] = 0; }

        for (long p = b + 2; p <= max_p; p++) {
            if (!is_prime(p) || p % b == 0) continue;

            long g = power_mod(b, lag, p);
            int C = collision_count(g, p, b);
            int Q = (int)((p - 1) / b);
            int S = C - Q;

            int cls = (int)(p % mod2);
            if (!s_seen[cls]) {
                s_first[cls] = S;
                s_seen[cls] = 1;
            } else if (S != s_first[cls]) {
                s_varies[cls] = 1;
            }
        }

        total = 0; varies = 0;
        for (int i = 0; i < (int)mod2; i++) {
            if (s_seen[i]) { total++; if (s_varies[i]) varies++; }
        }
        printf("  (smaller mod %ld: %d classes, %d vary: %s)\n",
               mod2, total, varies, varies == 0 ? "DETERMINED" : "NOT determined");
    }
}

int main() {
    long max_p = 10000;

    test_lag(3, 1, max_p);   // expect mod 9 = 3^2
    test_lag(3, 2, max_p);   // expect mod 27 = 3^3?
    test_lag(3, 3, max_p);   // expect mod 81 = 3^4?

    test_lag(10, 1, max_p);  // expect mod 100 = 10^2
    test_lag(10, 2, max_p);  // expect mod 1000? too big? test mod 100

    test_lag(5, 1, max_p);   // mod 25
    test_lag(5, 2, max_p);   // mod 125
    test_lag(5, 3, max_p);   // mod 625? too big

    return 0;
}
