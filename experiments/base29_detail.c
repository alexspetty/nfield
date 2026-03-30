/*
 * base29_detail.c - Why is base 29 the exception?
 * The largest coefficient has negative product. What character is it?
 * What's special about the collision structure at base 29?
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
    int b = 29;
    int m = b * b; /* 841 */

    int units[m], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    printf("Base %d, m=%d, phi=%d\n", b, m, n_units);
    printf("m mod 3 = %d\n", m % 3);
    printf("m mod 7 = %d\n", m % 7);
    printf("29 mod 3 = %d, 29 mod 7 = %d\n\n", 29 % 3, 29 % 7);

    /* Find primitive root */
    int g = -1;
    for (int cand = 2; cand < m; cand++) {
        if (gcd(cand, m) != 1) continue;
        int val = 1, ord = 0;
        do { val = (int)((long long)val * cand % m); ord++; } while (val != 1);
        if (ord == n_units) { g = cand; break; }
    }
    printf("Primitive root: %d\n\n", g);

    int dlog[m];
    memset(dlog, -1, sizeof(int) * m);
    { int val = 1; for (int k = 0; k < n_units; k++) { dlog[val] = k; val = (int)((long long)val * g % m); } }

    /* Build S table */
    int S[m], has_S[m];
    memset(has_S, 0, sizeof(int) * m);
    for (int p = m + 1; p < 80000; p++) {
        if (!is_prime(p) || gcd(p, b) != 1) continue;
        int a = p % m;
        if (has_S[a]) continue;
        int C = 0;
        for (int r = 1; r < p; r++) {
            int d1 = (int)((long long)b * r / p);
            long long br = (long long)b * r % p;
            int d2 = (int)((long long)b * br / p);
            if (d1 == d2) C++;
        }
        S[a] = C - (p - 1) / b;
        has_S[a] = 1;
    }

    /* Center */
    double cls_sum[b];
    int cls_cnt[b];
    memset(cls_sum, 0, sizeof(double) * b);
    memset(cls_cnt, 0, sizeof(int) * b);
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (!has_S[a]) continue;
        cls_sum[(a-1)%b] += S[a];
        cls_cnt[(a-1)%b]++;
    }
    double mean_R[b];
    for (int R = 0; R < b; R++)
        mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

    double Sc[m];
    int has_Sc[m];
    memset(has_Sc, 0, sizeof(int) * m);
    for (int i = 0; i < n_units; i++) {
        int a = units[i];
        if (!has_S[a]) continue;
        Sc[a] = S[a] - mean_R[(a-1)%b];
        has_Sc[a] = 1;
    }

    int dl_m1 = dlog[m - 1];

    /* Compute all odd characters, their coefficients and products */
    typedef struct {
        int j;
        double sh_re, sh_im, sh_mag;
        double P_re, P_im;
        double prod_re;
        int order;
    } entry_t;

    entry_t entries[n_units];
    int n_odd = 0;

    for (int j = 0; j < n_units; j++) {
        long long test = 2LL * j * dl_m1;
        if ((int)(test % (2 * n_units)) != n_units) continue;

        double sh_re = 0, sh_im = 0;
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_Sc[a]) continue;
            double angle = -2 * M_PI * j * dlog[a] / (double)n_units;
            sh_re += Sc[a] * cos(angle);
            sh_im += Sc[a] * sin(angle);
        }
        sh_re /= n_units;
        sh_im /= n_units;

        double P_re = 0, P_im = 0;
        for (int p = m + 1; p < MAX_PRIME; p++) {
            if (!is_prime(p) || gcd(p, b) != 1) continue;
            int a = p % m;
            if (dlog[a] < 0) continue;
            double angle = 2 * M_PI * j * dlog[a] / (double)n_units;
            double w = 1.0 / sqrt((double)p);
            P_re += cos(angle) * w;
            P_im += sin(angle) * w;
        }

        /* Order of character: smallest k > 0 with j*k = 0 mod phi */
        int order = n_units / gcd(j, n_units);

        double prod_re = sh_re * P_re - sh_im * P_im;
        entries[n_odd].j = j;
        entries[n_odd].sh_re = sh_re;
        entries[n_odd].sh_im = sh_im;
        entries[n_odd].sh_mag = sqrt(sh_re*sh_re + sh_im*sh_im);
        entries[n_odd].P_re = P_re;
        entries[n_odd].P_im = P_im;
        entries[n_odd].prod_re = prod_re;
        entries[n_odd].order = order;
        n_odd++;
    }

    /* Sort by |s_hat| descending */
    for (int i = 0; i < n_odd - 1; i++)
        for (int k = i + 1; k < n_odd; k++)
            if (entries[k].sh_mag > entries[i].sh_mag) {
                entry_t tmp = entries[i];
                entries[i] = entries[k];
                entries[k] = tmp;
            }

    printf("Odd characters: %d\n\n", n_odd);
    printf("Top 10 by |s_hat|:\n");
    printf("%5s %5s %8s %8s %10s %5s\n",
           "rank", "order", "|sh|", "|P|", "Re(sh*P)", "sign");

    double net = 0;
    int n_pos = 0, n_neg = 0;
    for (int i = 0; i < n_odd; i++) {
        net += entries[i].prod_re;
        if (entries[i].prod_re >= -1e-10) n_pos++;
        else n_neg++;
    }

    for (int i = 0; i < 10 && i < n_odd; i++) {
        char sign = entries[i].prod_re >= -1e-10 ? '+' : '-';
        double P_mag = sqrt(entries[i].P_re*entries[i].P_re +
                           entries[i].P_im*entries[i].P_im);
        printf("%5d %5d %8.4f %8.4f %+10.4f %5c\n",
               i+1, entries[i].order, entries[i].sh_mag,
               P_mag, entries[i].prod_re, sign);
    }

    printf("\nTotal: %d+, %d-, net=%+.4f\n", n_pos, n_neg, net);

    /* What order is the largest negative character? */
    printf("\nLargest negative character: j=%d, order=%d\n",
           entries[0].j, entries[0].order);

    /* Check: is the order related to 29-1=28? */
    printf("29-1 = 28 = 4 * 7\n");
    printf("phi(29^2) = 29*28 = %d\n", n_units);

    /* Compare with nearby primes */
    printf("\n=== Comparison: bases near 29 ===\n");
    int nearby[] = {23, 29, 31, 37};
    for (int ni = 0; ni < 4; ni++) {
        int bb = nearby[ni];
        if (!is_prime(bb)) continue;
        int mm = bb * bb;
        int uu[mm], nu = 0;
        for (int a = 1; a < mm; a++)
            if (gcd(a, mm) == 1) uu[nu++] = a;

        /* primitive root */
        int gg = -1;
        for (int c = 2; c < mm; c++) {
            if (gcd(c, mm) != 1) continue;
            int v = 1, o = 0;
            do { v = (int)((long long)v * c % mm); o++; } while (v != 1);
            if (o == nu) { gg = c; break; }
        }
        if (gg < 0) continue;

        printf("\nBase %d: 29 mod %d = %d, %d mod 3 = %d\n",
               bb, bb, 29 % bb, bb, bb % 3);
    }

    return 0;
}
