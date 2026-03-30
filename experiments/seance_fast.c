/*
 * seance_fast.c - Sampled collision correlation for larger composites.
 *
 * Instead of exhaustive triple loop, SAMPLE random (r, g, d) triples
 * and accumulate correlation statistics by d mod m.
 *
 * gcc -O3 -fopenmp -o seance_fast seance_fast.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = b; b = a % b; a = t; }
    return a;
}

/* Fast collision check */
static inline int collides(long long r, long long g, long long n, int base) {
    long long gr = g * r % n;
    return (int)(base * r / n) == (int)(base * gr / n);
}

void test_sampled(long long n, int base, int *cands, int ncand,
                  int n_r, int n_g, int n_d) {
    /* For each candidate m, accumulate:
     * - P(collision at g AND at gd | collision at g) for d ≡ 1 mod m
     * - same for d ≢ 0,1 mod m (background)
     */
    long long *both_1 = calloc(ncand, sizeof(long long));
    long long *one_1 = calloc(ncand, sizeof(long long));
    long long *both_o = calloc(ncand, sizeof(long long));
    long long *one_o = calloc(ncand, sizeof(long long));

    srand(42);

    #pragma omp parallel
    {
        unsigned int seed = 42 + omp_get_thread_num() * 1000;
        long long *lb1 = calloc(ncand, sizeof(long long));
        long long *lo1 = calloc(ncand, sizeof(long long));
        long long *lbo = calloc(ncand, sizeof(long long));
        long long *loo = calloc(ncand, sizeof(long long));

        #pragma omp for schedule(dynamic)
        for (int ir = 0; ir < n_r; ir++) {
            /* Pick random r coprime to n */
            long long r;
            do { r = (long long)(rand_r(&seed) % (n-1)) + 1; }
            while (gcdll(r, n) != 1);

            for (int ig = 0; ig < n_g; ig++) {
                /* Pick random g coprime to n */
                long long g;
                do { g = (long long)(rand_r(&seed) % (n-2)) + 2; }
                while (gcdll(g, n) != 1);

                if (!collides(r, g, n, base)) continue;

                for (int id = 0; id < n_d; id++) {
                    /* Pick random d coprime to n, d > 1 */
                    long long d;
                    do { d = (long long)(rand_r(&seed) % (n-2)) + 2; }
                    while (gcdll(d, n) != 1);

                    long long gd = g * d % n;
                    if (gcdll(gd, n) != 1) continue;

                    int x2 = collides(r, gd, n, base);

                    for (int ci = 0; ci < ncand; ci++) {
                        int m = cands[ci];
                        int k = (int)(d % m);
                        if (k == 1) {
                            lo1[ci]++;
                            if (x2) lb1[ci]++;
                        } else if (k != 0) {
                            loo[ci]++;
                            if (x2) lbo[ci]++;
                        }
                    }
                }
            }
        }

        #pragma omp critical
        {
            for (int ci = 0; ci < ncand; ci++) {
                both_1[ci] += lb1[ci];
                one_1[ci] += lo1[ci];
                both_o[ci] += lbo[ci];
                one_o[ci] += loo[ci];
            }
        }

        free(lb1); free(lo1); free(lbo); free(loo);
    }

    printf("n = %lld (samples: %d r x %d g x %d d):\n",
           n, n_r, n_g, n_d);
    for (int ci = 0; ci < ncand; ci++) {
        int m = cands[ci];
        double c1 = one_1[ci] > 0 ? (double)both_1[ci] / one_1[ci] : 0;
        double co = one_o[ci] > 0 ? (double)both_o[ci] / one_o[ci] : 0;
        double excess = c1 - co;
        int is_factor = (n % m == 0);
        printf("  mod %4d: d=1 %.5f  bg %.5f  excess %+.5f %s\n",
               m, c1, co, excess, is_factor ? " ** FACTOR **" : "");
    }
    printf("\n");

    free(both_1); free(one_1);
    free(both_o); free(one_o);
}

int main(void) {
    int base = 10;

    /* Medium composites */
    {
        long long n = 59LL * 67;  /* 3953 */
        int cands[] = {53, 59, 61, 67, 71, 73};
        test_sampled(n, base, cands, 6, 500, 200, 200);
    }
    {
        long long n = 101LL * 103;  /* 10403 */
        int cands[] = {97, 101, 103, 107, 109, 113};
        test_sampled(n, base, cands, 6, 500, 200, 200);
    }
    {
        long long n = 199LL * 211;  /* 41989 */
        int cands[] = {191, 193, 197, 199, 211, 223};
        test_sampled(n, base, cands, 6, 1000, 300, 300);
    }
    {
        long long n = 503LL * 509;  /* 256027 */
        int cands[] = {499, 503, 509, 521, 523, 541};
        test_sampled(n, base, cands, 6, 2000, 500, 500);
    }
    {
        long long n = 1009LL * 1013;  /* 1022117 */
        int cands[] = {997, 1009, 1013, 1019, 1021, 1031};
        test_sampled(n, base, cands, 6, 3000, 500, 500);
    }

    return 0;
}
