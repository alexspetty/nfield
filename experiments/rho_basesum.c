/*
 * rho_basesum.c - Repulsion ratio via base-summed collision deviation.
 *
 * Instead of measuring rho at each base independently,
 * aggregate S° across bases for each prime, then decompose
 * the aggregate over characters of a REFERENCE base and
 * measure the overlap.
 *
 * Also: compute the weighted average of rho across bases
 * using the base sum weights.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 3000000
#define N_BASES 11

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
    int bases[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    double weights[N_BASES];
    double total_weight = 0;

    /* Build S tables for all bases */
    typedef struct {
        int b, m;
        int S[2000]; /* max m = 37^2 = 1369 */
        int has[2000];
        double mean_R[40];
    } base_data;

    base_data BD[N_BASES];

    for (int bi = 0; bi < N_BASES; bi++) {
        int b = bases[bi];
        int m = b * b;
        BD[bi].b = b;
        BD[bi].m = m;
        weights[bi] = 1.0 / (b * b);
        total_weight += weights[bi];

        memset(BD[bi].has, 0, sizeof(int) * m);

        for (int p = m + 1; p < 80000; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            if (BD[bi].has[a]) continue;
            int C = 0;
            for (int r = 1; r < p; r++) {
                int d1 = (int)((long long)b * r / p);
                long long br = (long long)b * r % p;
                int d2 = (int)((long long)b * br / p);
                if (d1 == d2) C++;
            }
            BD[bi].S[a] = C - (p - 1) / b;
            BD[bi].has[a] = 1;
        }

        double cls_sum[b];
        int cls_cnt[b];
        memset(cls_sum, 0, sizeof(double) * b);
        memset(cls_cnt, 0, sizeof(int) * b);
        for (int a = 1; a < m; a++) {
            if (gcd(a, m) != 1 || !BD[bi].has[a]) continue;
            cls_sum[(a-1)%b] += BD[bi].S[a];
            cls_cnt[(a-1)%b]++;
        }
        for (int R = 0; R < b; R++)
            BD[bi].mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;
    }

    /* For a reference base (say b=13), compute:
     * R(p) = sum_b w(b) S°(p, b)  for each prime p
     * Then decompose R(p) over characters of b=13
     * and measure overlap with P(s, chi) */

    int ref = 4; /* index of base 13 */
    int b_ref = bases[ref];
    int m_ref = b_ref * b_ref;
    int units[m_ref], n_units = 0;
    for (int a = 1; a < m_ref; a++)
        if (gcd(a, m_ref) == 1) units[n_units++] = a;

    /* Primitive root mod m_ref */
    int g = -1;
    for (int c = 2; c < m_ref; c++) {
        if (gcd(c, m_ref) != 1) continue;
        int v = 1, o = 0;
        do { v = (int)((long long)v * c % m_ref); o++; } while (v != 1);
        if (o == n_units) { g = c; break; }
    }

    int dlog[m_ref];
    memset(dlog, -1, sizeof(int) * m_ref);
    { int v = 1; for (int k = 0; k < n_units; k++) { dlog[v] = k; v = (int)((long long)v * g % m_ref); } }

    int dl_m1 = dlog[m_ref - 1];
    int odd_j[500], n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 500; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    printf("Reference base: %d, n_odd = %d\n\n", b_ref, n_odd);

    /* Accumulate R_hat(chi) and P(s, chi) over primes */
    /* R_hat(chi) = (1/phi) sum_p R(p) conj(chi(p)) / p^s */
    /* But R(p) is different for each prime, so we accumulate directly */

    double s = 0.5;
    double R_hat_re[500], R_hat_im[500];
    double P_re[500], P_im[500];
    memset(R_hat_re, 0, sizeof(double) * n_odd);
    memset(R_hat_im, 0, sizeof(double) * n_odd);
    memset(P_re, 0, sizeof(double) * n_odd);
    memset(P_im, 0, sizeof(double) * n_odd);

    /* Also: single-base S° hat for comparison */
    double S_hat_re[500], S_hat_im[500];
    memset(S_hat_re, 0, sizeof(double) * n_odd);
    memset(S_hat_im, 0, sizeof(double) * n_odd);

    int count = 0;
    for (int p = m_ref + 1; p < MAX_PRIME; p++) {
        if (!is_prime(p)) continue;

        int a_ref = p % m_ref;
        if (dlog[a_ref] < 0) continue;
        if (gcd(p, b_ref) != 1) continue;

        count++;

        /* Compute R(p) = sum w(b) S°(p, b) */
        double Rp = 0;
        for (int bi = 0; bi < N_BASES; bi++) {
            int b = BD[bi].b;
            if (gcd(p, b) != 1) continue;
            int m = BD[bi].m;
            if (p <= m) continue;
            int a = p % m;
            if (!BD[bi].has[a]) continue;
            double sc = BD[bi].S[a] - BD[bi].mean_R[(a-1) % b];
            Rp += weights[bi] * sc;
        }

        /* S° at reference base only */
        double Sp = 0;
        { int a = p % m_ref;
          if (BD[ref].has[a])
              Sp = BD[ref].S[a] - BD[ref].mean_R[(a-1) % b_ref]; }

        double w = pow((double)p, -s);

        for (int c = 0; c < n_odd; c++) {
            double angle = 2 * M_PI * odd_j[c] * dlog[a_ref] / (double)n_units;
            double cos_a = cos(angle), sin_a = sin(angle);

            /* P(s, chi) */
            P_re[c] += cos_a * w;
            P_im[c] += sin_a * w;

            /* R_hat: weighted by R(p) */
            R_hat_re[c] += Rp * cos_a * w;
            R_hat_im[c] += Rp * sin_a * w;

            /* S_hat: weighted by S°(p) at ref base */
            S_hat_re[c] += Sp * cos_a * w;
            S_hat_im[c] += Sp * sin_a * w;
        }
    }

    printf("Primes used: %d\n\n", count);

    /* Compute overlaps */
    /* 1. Single-base overlap (S° vs P at ref base) */
    double sh_mag2[500], P_mag2[500], R_mag2[500];
    double total_sh = 0, total_P = 0, total_R = 0;

    for (int c = 0; c < n_odd; c++) {
        sh_mag2[c] = S_hat_re[c]*S_hat_re[c] + S_hat_im[c]*S_hat_im[c];
        P_mag2[c] = P_re[c]*P_re[c] + P_im[c]*P_im[c];
        R_mag2[c] = R_hat_re[c]*R_hat_re[c] + R_hat_im[c]*R_hat_im[c];
        total_sh += sh_mag2[c];
        total_P += P_mag2[c];
        total_R += R_mag2[c];
    }

    double overlap_single = 0, overlap_basesum = 0;
    for (int c = 0; c < n_odd; c++) {
        if (total_sh > 0 && total_P > 0)
            overlap_single += (sh_mag2[c]/total_sh) * (P_mag2[c]/total_P);
        if (total_R > 0 && total_P > 0)
            overlap_basesum += (R_mag2[c]/total_R) * (P_mag2[c]/total_P);
    }

    double rho_single = n_odd * overlap_single;
    double rho_basesum = n_odd * overlap_basesum;

    printf("Single-base (b=%d): rho = %.4f\n", b_ref, rho_single);
    printf("Base-summed:        rho = %.4f\n", rho_basesum);
    printf("1/phi = %.4f\n", (sqrt(5.0)-1)/2);
    printf("3/5   = %.4f\n", 0.6);

    /* Also: weighted average of per-base rho */
    printf("\n=== Weighted average approach ===\n");

    /* We already have per-base rho from the overlap_rate computation.
     * Just report the reference base result and the base-sum result. */

    printf("\nThe base sum gives rho = %.4f\n", rho_basesum);
    printf("If base-summing sharpens the estimate, this is the\n");
    printf("value to compare against 1/phi and 3/5.\n");

    return 0;
}
