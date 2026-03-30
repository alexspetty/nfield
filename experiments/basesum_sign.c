/*
 * basesum_sign.c - Sign structure of the base sum.
 *
 * For each prime p, compute R(p) = Σ_b w(b) S_1(p, b) across bases.
 * R(p) depends on p through its residue in each base's group.
 *
 * Instead of decomposing over characters of a single base,
 * we directly compute:
 *   F_R(s) = Σ_p R(p) / p^s
 * and ask: how does this relate to the per-base F°(s)?
 *
 * More precisely: for each base b, F°_b(s) = Σ ĉ_b(χ) P(s,χ_b).
 * The base sum is F_R(s) = Σ_b w(b) F°_b(s) = Σ_b w(b) Σ_χ ĉ_b(χ) P(s,χ).
 *
 * The sign structure of the base sum is: for each (base, character)
 * pair, what is the sign of w(b) * Re(ĉ_b(χ) * P(s,χ))?
 *
 * Simpler first: just compute the base-summed F_R(s) directly
 * and check if it converges better/worse than individual bases.
 * Then decompose.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000

static int is_prime(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    /* Bases to sum over */
    int bases[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31};
    int n_bases = sizeof(bases) / sizeof(bases[0]);
    double s_vals[] = {1.0, 0.8, 0.6, 0.5};
    int n_s = 4;

    /* For each base, build S table (lag 1) */
    /* S_b[a] for a = p mod b^2 */
    typedef struct {
        int b, m;
        int S[1024]; /* max m = 31^2 = 961 */
        int has[1024];
        double cls_mean[32];
        double w; /* weight */
    } base_info;

    base_info B[10];
    for (int bi = 0; bi < n_bases; bi++) {
        int b = bases[bi];
        int m = b * b;
        B[bi].b = b;
        B[bi].m = m;
        B[bi].w = 1.0 / (b * b); /* weight = 1/b^2 */
        memset(B[bi].has, 0, sizeof(int) * m);

        for (int p = m + 1; p < 80000; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            if (B[bi].has[a]) continue;
            int C = 0;
            for (int r = 1; r < p; r++) {
                int d1 = (int)((long long)b * r / p);
                long long br = (long long)b * r % p;
                int d2 = (int)((long long)b * br / p);
                if (d1 == d2) C++;
            }
            B[bi].S[a] = C - (p - 1) / b;
            B[bi].has[a] = 1;
        }

        /* Class means */
        double cls_sum[32] = {0};
        int cls_cnt[32] = {0};
        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1 || !B[bi].has[a]) continue;
            int R = (a - 1) % b;
            cls_sum[R] += B[bi].S[a];
            cls_cnt[R]++;
        }
        for (int R = 0; R < b; R++)
            B[bi].cls_mean[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;
    }

    /* Now scan primes and accumulate:
     * For each prime p:
     *   R(p) = Σ_b w(b) * S°_b(p)
     * where S°_b(p) = S_b(p mod b^2) - class_mean_b
     *
     * Accumulate F_R(s) = Σ_p R(p) / p^s
     * Also accumulate individual F°_b(s) for comparison
     */

    double F_R[4] = {0};           /* base sum */
    double F_ind[10][4];           /* individual bases */
    memset(F_ind, 0, sizeof(F_ind));

    /* Also track: per-prime R(p) split by p mod 3 */
    double R_class1[4] = {0}, R_class2[4] = {0};
    int cnt1 = 0, cnt2 = 0;

    int count = 0;
    for (int p = 1000; p < MAX_PRIME; p++) {
        if (!is_prime(p)) continue;

        /* Compute R(p) = Σ_b w(b) S°_b(p) */
        double Rp = 0;
        int valid = 0;

        for (int bi = 0; bi < n_bases; bi++) {
            int b = B[bi].b;
            if (gcd(p, b) != 1) continue;
            int m = B[bi].m;
            if (p <= m) continue;
            int a = p % m;
            if (!B[bi].has[a]) continue;

            double sc = B[bi].S[a] - B[bi].cls_mean[(a - 1) % b];
            Rp += B[bi].w * sc;
            valid++;

            for (int si = 0; si < n_s; si++)
                F_ind[bi][si] += sc * pow((double)p, -s_vals[si]);
        }

        if (valid < 5) continue; /* need enough bases */
        count++;

        for (int si = 0; si < n_s; si++) {
            double w = pow((double)p, -s_vals[si]);
            F_R[si] += Rp * w;

            if (p % 3 == 1) R_class1[si] += Rp * w;
            else if (p % 3 == 2) R_class2[si] += Rp * w;
        }
        if (p % 3 == 1) cnt1++;
        else if (p % 3 == 2) cnt2++;
    }

    printf("Base sum F_R(s) over %d bases, %d primes:\n\n", n_bases, count);
    printf("%5s %10s %10s %10s %10s\n", "s", "F_R", "class1", "class2", "ratio");
    for (int si = 0; si < n_s; si++) {
        double ratio = fabs(R_class2[si]) > 1e-10 ?
            R_class1[si] / R_class2[si] : 0;
        printf("%5.1f %+10.4f %+10.4f %+10.4f %10.4f\n",
               s_vals[si], F_R[si], R_class1[si], R_class2[si], ratio);
    }

    printf("\nIndividual F°_b(s) at s=0.5:\n");
    for (int bi = 0; bi < n_bases; bi++)
        printf("  base %2d: %+.4f\n", bases[bi], F_ind[bi][3]);

    printf("\nBase sum vs individual sum at s=0.5:\n");
    double ind_sum = 0;
    for (int bi = 0; bi < n_bases; bi++)
        ind_sum += B[bi].w * F_ind[bi][3];
    printf("  F_R(0.5) = %+.4f\n", F_R[3]);
    printf("  Σ w(b)*F°_b(0.5) = %+.4f\n", ind_sum);

    /* Convergence comparison: how stable is F_R vs individual? */
    printf("\nConvergence profile:\n");
    printf("%5s %10s", "s", "F_R");
    for (int bi = 0; bi < n_bases; bi += 3)
        printf(" %8s%d", "F°_b=", bases[bi]);
    printf("\n");
    for (int si = 0; si < n_s; si++) {
        printf("%5.1f %+10.4f", s_vals[si], F_R[si]);
        for (int bi = 0; bi < n_bases; bi += 3)
            printf(" %+10.4f", F_ind[bi][si]);
        printf("\n");
    }

    return 0;
}
