/*
 * factor_via_derange.c - Factor n = pq using deranging multipliers.
 *
 * Algorithm:
 * 1. For random g coprime to n, compute C(g). If C(g) = 0, g is deranging.
 * 2. Compute c = b(1-g)^{-1} mod n.
 * 3. For u = 1,...,b-1: check if gcd(n, c-u) gives a factor.
 *
 * Question: how many g do we need to try before finding a deranging one?
 * The deranging density at n = pq is approximately (b-1)^2 / phi(n).
 *
 * Also: can we use C(g) > 0 (non-deranging) values to constrain
 * the factorization?
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

/* Compute C(g) at composite n */
int collision_count(int n, int b, int g) {
    int count = 0;
    for (int r = 1; r < n; r++) {
        int d1 = b * r / n;
        int gr = (int)((long long)g * r % n);
        int d2 = b * gr / n;
        if (d1 == d2) count++;
    }
    return count;
}

/* Extended GCD: returns gcd and sets x such that a*x + b*y = gcd */
int ext_gcd(int a, int b, int *x, int *y) {
    if (b == 0) { *x = 1; *y = 0; return a; }
    int x1, y1;
    int g = ext_gcd(b, a % b, &x1, &y1);
    *x = y1;
    *y = x1 - (a / b) * y1;
    return g;
}

int mod_inverse(int a, int n) {
    int x, y;
    int g = ext_gcd(a % n, n, &x, &y);
    if (g != 1) return -1;
    return ((x % n) + n) % n;
}

int main(void) {
    int b = 10;

    /* Test composites */
    int tests[][2] = {
        {101, 103}, {101, 127}, {103, 109},
        {127, 131}, {137, 139}, {149, 151},
        {157, 163}, {167, 173}, {179, 181},
        {191, 193}
    };
    int ntests = 10;

    printf("Factoring via deranging multipliers (base %d):\n\n", b);

    for (int ti = 0; ti < ntests; ti++) {
        int p = tests[ti][0], q = tests[ti][1];
        int n = p * q;

        /* Count deranging multipliers */
        int n_deranging = 0;
        int first_deranging = -1;

        for (int g = 2; g < n; g++) {
            if (gcd(g, n) != 1) continue;
            int C = collision_count(n, b, g);
            if (C == 0) {
                n_deranging++;
                if (first_deranging < 0) first_deranging = g;
            }
        }

        printf("n = %d = %d x %d: %d deranging out of %d units",
               n, p, q, n_deranging, (p-1)*(q-1));

        /* Try to factor using first deranging g */
        if (first_deranging > 0) {
            int g = first_deranging;
            /* c = b * (1-g)^{-1} mod n */
            int one_minus_g = ((1 - g) % n + n) % n;
            int inv = mod_inverse(one_minus_g, n);
            if (inv < 0) {
                printf(" (inverse failed)\n");
                continue;
            }
            int c = (int)((long long)b * inv % n);

            /* Try gcd(n, c-u) for u = 1,...,b-1 */
            int found = 0;
            for (int u = 1; u < b; u++) {
                int val = ((c - u) % n + n) % n;
                int f = gcd(n, val);
                if (f > 1 && f < n) {
                    printf(" -> FACTORED via g=%d, c=%d, u=%d: "
                           "gcd(n,%d)=%d, n/%d=%d\n",
                           g, c, u, val, f, f, n/f);
                    found = 1;
                    break;
                }
            }
            if (!found) printf(" (gcd failed)\n");
        } else {
            printf(" (no deranging found)\n");
        }
    }

    /* Density analysis */
    printf("\nDeranging density:\n");
    printf("%10s %6s %8s %8s %8s\n",
           "n", "phi", "derang", "density", "(b-1)^2/phi");

    for (int ti = 0; ti < 5; ti++) {
        int p = tests[ti][0], q = tests[ti][1];
        int n = p * q;
        int phi = (p-1)*(q-1);

        int nd = 0;
        for (int g = 2; g < n; g++) {
            if (gcd(g, n) != 1) continue;
            if (collision_count(n, b, g) == 0) nd++;
        }

        printf("%10d %6d %8d %8.6f %8.6f\n",
               n, phi, nd, (double)nd/phi,
               (double)(b-1)*(b-1)/phi);
    }

    return 0;
}
