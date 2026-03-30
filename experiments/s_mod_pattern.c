// Is S determined by p mod b^2?
// If so, the Centered Collision PNT reduces to Dirichlet's theorem.

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

void test_base(int b, long max_p) {
    int bsq = b * b;
    printf("\n=== BASE %d, checking S vs p mod %d ===\n", b, bsq);

    // For each residue class mod b^2, track S values
    int s_values[200][50];  // [class][index]
    int s_count[200] = {0};

    for (long p = b + 2; p <= max_p; p++) {
        if (!is_prime(p) || p % b == 0) continue;

        long g = power_mod(b, 1, p);
        int C = collision_count(g, p, b);
        int Q = (int)((p - 1) / b);
        int S = C - Q;

        int cls = (int)(p % bsq);
        if (s_count[cls] < 50)
            s_values[cls][s_count[cls]] = S;
        s_count[cls]++;
    }

    // Check if each class has a unique S value
    int determined = 1;
    int classes_seen = 0;

    printf("  %-8s %-8s %-6s %-30s\n", "p mod b²", "count", "unique?", "S values");

    for (int cls = 0; cls < bsq; cls++) {
        if (s_count[cls] == 0) continue;
        classes_seen++;

        // Check if all S values in this class are the same
        int all_same = 1;
        int first_S = s_values[cls][0];
        int n = s_count[cls] < 50 ? s_count[cls] : 50;
        for (int i = 1; i < n; i++) {
            if (s_values[cls][i] != first_S) {
                all_same = 0;
                break;
            }
        }

        if (!all_same) determined = 0;

        // Show first few S values
        printf("  %-8d %-8d %-6s ", cls, s_count[cls],
               all_same ? "YES" : "NO");
        for (int i = 0; i < (n < 8 ? n : 8); i++)
            printf("%d ", s_values[cls][i]);
        if (!all_same) printf(" <-- VARIES");
        printf("\n");
    }

    printf("\n  S determined by p mod %d? %s (%d classes)\n",
           bsq, determined ? "YES" : "NO", classes_seen);
}

int main() {
    test_base(3, 5000);
    test_base(5, 5000);
    test_base(7, 5000);
    test_base(10, 5000);
    return 0;
}
