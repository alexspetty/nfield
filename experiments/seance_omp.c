/*
 * seance_omp.c - Collision correlation computation with OpenMP.
 *
 * For n = pq, compute the correlation excess at d ≡ 1 mod m
 * for candidate moduli m. Factor-aligned moduli show negative excess.
 *
 * gcc -O3 -fopenmp -o seance_omp seance_omp.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <omp.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

void test_composite(int n, int base, int *candidates, int ncand) {
    int phi_n = 0;
    for (int i = 1; i < n; i++)
        if (gcd(i, n) == 1) phi_n++;

    /* For each candidate modulus m, accumulate correlation at d≡1 vs others */
    long long *both_1 = calloc(ncand, sizeof(long long));
    long long *one_1 = calloc(ncand, sizeof(long long));
    long long *both_o = calloc(ncand, sizeof(long long));
    long long *one_o = calloc(ncand, sizeof(long long));

    #pragma omp parallel for schedule(dynamic)
    for (int d = 2; d < n; d++) {
        if (gcd(d, n) != 1) continue;

        long long *local_b1 = calloc(ncand, sizeof(long long));
        long long *local_o1 = calloc(ncand, sizeof(long long));
        long long *local_bo = calloc(ncand, sizeof(long long));
        long long *local_oo = calloc(ncand, sizeof(long long));

        for (int r = 1; r < n; r++) {
            if (gcd(r, n) != 1) continue;
            int d_r = base * r / n;

            for (int g = 2; g < n; g++) {
                if (gcd(g, n) != 1) continue;
                int gd = (int)((long long)g * d % n);
                if (gcd(gd, n) != 1) continue;

                int gr = (int)((long long)g * r % n);
                int x1 = (d_r == base * gr / n);
                if (!x1) continue;

                int gdr = (int)((long long)gd * r % n);
                int x2 = (d_r == base * gdr / n);

                for (int ci = 0; ci < ncand; ci++) {
                    int m = candidates[ci];
                    int k = d % m;
                    if (k == 1) {
                        local_o1[ci]++;
                        if (x2) local_b1[ci]++;
                    } else if (k != 0) {
                        local_oo[ci]++;
                        if (x2) local_bo[ci]++;
                    }
                }
            }
        }

        #pragma omp critical
        {
            for (int ci = 0; ci < ncand; ci++) {
                both_1[ci] += local_b1[ci];
                one_1[ci] += local_o1[ci];
                both_o[ci] += local_bo[ci];
                one_o[ci] += local_oo[ci];
            }
        }

        free(local_b1); free(local_o1);
        free(local_bo); free(local_oo);
    }

    printf("n = %d:\n", n);
    for (int ci = 0; ci < ncand; ci++) {
        int m = candidates[ci];
        double c1 = one_1[ci] > 0 ? (double)both_1[ci] / one_1[ci] : 0;
        double co = one_o[ci] > 0 ? (double)both_o[ci] / one_o[ci] : 0;
        double excess = c1 - co;
        int is_factor = (n % m == 0);
        printf("  mod %3d: d=1 %.5f  bg %.5f  excess %+.5f %s\n",
               m, c1, co, excess, is_factor ? " ** FACTOR **" : "");
    }
    printf("\n");

    free(both_1); free(one_1);
    free(both_o); free(one_o);
}

int main(void) {
    int base = 10;

    /* Test larger composites */
    int cands1[] = {23, 29, 31, 37, 41, 43};
    printf("=== 23 x 29 = 667 ===\n");
    test_composite(667, base, cands1, 6);

    int cands2[] = {29, 31, 37, 41, 43, 47};
    printf("=== 31 x 37 = 1147 ===\n");
    test_composite(1147, base, cands2, 6);

    int cands3[] = {37, 41, 43, 47, 53, 59};
    printf("=== 41 x 43 = 1763 ===\n");
    test_composite(1763, base, cands3, 6);

    return 0;
}
