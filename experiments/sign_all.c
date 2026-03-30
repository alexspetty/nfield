/*
 * sign_all.c - Sign structure of collision transform across all bases.
 *
 * For each base b (prime and composite), compute:
 * - S table via finite determination (p mod b^2)
 * - Center by spectral class
 * - Compute DFT coefficients s_hat(chi) for odd characters
 * - Compute P(s, chi) = sum_p chi(p)/p^s at s = 0.5
 * - Count positive vs negative Re(s_hat * P)
 *
 * Uses direct DFT (no primitive root needed).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_M 1024  /* max b^2 for b <= 31 */
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
    printf("%5s %6s %4s %4s %4s %4s %6s %9s\n",
           "base", "type", "phi", "odd", "pos", "neg", "%pos", "net");

    for (int b = 3; b <= 31; b++) {
        int m = b * b;

        /* Build unit list */
        int units[MAX_M], n_units = 0;
        for (int a = 1; a < m; a++)
            if (gcd(a, m) == 1) units[n_units++] = a;

        /* Build S table */
        int S[MAX_M];
        int has_S[MAX_M];
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

        /* Class means */
        double cls_sum[32] = {0};
        int cls_cnt[32] = {0};
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_S[a]) continue;
            int R = (a - 1) % b;
            cls_sum[R] += S[a];
            cls_cnt[R]++;
        }
        double mean_R[32];
        for (int R = 0; R < b; R++)
            mean_R[R] = cls_cnt[R] > 0 ? cls_sum[R] / cls_cnt[R] : 0;

        /* Centered S */
        double Sc[MAX_M];
        int has_Sc[MAX_M];
        memset(has_Sc, 0, sizeof(int) * m);
        for (int i = 0; i < n_units; i++) {
            int a = units[i];
            if (!has_S[a]) continue;
            Sc[a] = S[a] - mean_R[(a - 1) % b];
            has_Sc[a] = 1;
        }

        /*
         * Direct DFT over the unit group.
         * Character chi_k(a) = exp(2*pi*i * k * index(a) / phi)
         * where index(a) is computed via the unit list ordering.
         *
         * But the unit group may not be cyclic. Instead, use the
         * general DFT: for each pair of units (a, k), the character
         * value is determined by the group structure.
         *
         * Simpler approach: just compute s_hat for each "character"
         * defined by mapping a -> exp(2*pi*i * f(a) / n) for all
         * group homomorphisms f: (Z/mZ)* -> C*.
         *
         * Simplest: enumerate characters by their values on a
         * generating set. For each unit a, chi(a) depends on the
         * discrete logs. But without primitive root this is hard.
         *
         * PRACTICAL APPROACH: Use the reflection identity directly.
         * We only need to know which Fourier modes are odd and
         * their inner products with S°.
         *
         * EVEN SIMPLER: Direct sum over all units.
         * For chi indexed by unit k: chi_k(a) = exp(2*pi*i * dlog / phi).
         * If no primitive root exists, use ALL unit-indexed "characters"
         * and filter for actual characters using orthogonality.
         *
         * SIMPLEST: Just compute sum_a S°(a) * exp(-2*pi*i*j*a/m) / phi
         * for j = 0..m-1. This gives Fourier coefficients on Z/mZ,
         * restricted to units. Not exactly Dirichlet characters, but
         * gives the right answer for the sign count because the
         * Dirichlet characters are a subset of these and the odd
         * ones are exactly those with chi(-1) = -1.
         */

        /* Actually, let's just do it properly for cyclic groups
         * and handle non-cyclic as a special case.
         * For prime b: m = b^2 always has a primitive root.
         * For composite b: skip for now, handle base 10 separately. */

        /* Find primitive root */
        int g = -1;
        for (int cand = 2; cand < m; cand++) {
            if (gcd(cand, m) != 1) continue;
            int val = 1, ord = 0;
            do {
                val = (int)((long long)val * cand % m);
                ord++;
            } while (val != 1);
            if (ord == n_units) { g = cand; break; }
        }

        if (g < 0) {
            /* Non-cyclic: use additive Fourier as approximation */
            /* Count odd modes: those j where exp(-2*pi*i*j*(m-1)/m) = -1
             * i.e., j*(m-1)/m = 1/2 + integer, i.e., 2*j*(m-1) = m*(2k+1)
             * This is messy. Just report that we can't handle it. */

            /* Actually for non-cyclic, use DFT on the additive group
             * and check oddness. This gives a superset but the sign
             * pattern should be similar. */

            int n_odd = 0, n_pos = 0, n_neg = 0;
            double net = 0;

            for (int j = 1; j < m; j++) {
                if (gcd(j, m) != 1) continue; /* skip non-units */

                /* Check oddness: chi_j(m-1) = exp(2*pi*i*j*(m-1)/m) */
                double angle_m1 = 2 * M_PI * j * (m - 1.0) / m;
                double re_m1 = cos(angle_m1);
                if (fabs(re_m1 - (-1)) > 0.01) continue; /* not odd */
                n_odd++;

                /* s_hat_j = (1/phi) sum_a Sc(a) * exp(-2*pi*i*j*a/m) */
                double sh_re = 0, sh_im = 0;
                for (int i = 0; i < n_units; i++) {
                    int a = units[i];
                    if (!has_Sc[a]) continue;
                    double angle = -2 * M_PI * j * a / (double)m;
                    sh_re += Sc[a] * cos(angle);
                    sh_im += Sc[a] * sin(angle);
                }
                sh_re /= n_units;
                sh_im /= n_units;

                /* P_j(0.5) = sum_p exp(2*pi*i*j*p/m) / sqrt(p) */
                /* Wait, this is the additive character, not Dirichlet.
                 * For Dirichlet chars, chi(p) depends on p mod m.
                 * For additive chars, e(jp/m) depends on p mod m too.
                 * But they're different objects. The additive chars
                 * are NOT Dirichlet characters.
                 *
                 * For non-cyclic groups, we need the actual Dirichlet
                 * characters. Let's just skip non-cyclic for now. */
                break;
            }

            printf("%5d %6s %4d %4s %4s %4s %6s %9s\n",
                   b, is_prime(b) ? "prime" : "comp",
                   n_units, "?", "?", "?", "?", "?");
            continue;
        }

        /* Cyclic group: build dlog table */
        int dlog[MAX_M];
        memset(dlog, -1, sizeof(int) * m);
        {
            int val = 1;
            for (int k = 0; k < n_units; k++) {
                dlog[val] = k;
                val = (int)((long long)val * g % m);
            }
        }

        /* For each character j (0..phi-1):
         * chi_j(a) = exp(2*pi*i * j * dlog[a] / phi)
         * Odd iff chi_j(m-1) = -1
         * i.e., exp(2*pi*i * j * dlog[m-1] / phi) = -1
         * i.e., j * dlog[m-1] / phi = 1/2 + integer
         * i.e., 2 * j * dlog[m-1] = phi * (2k+1)
         */
        int dl_m1 = dlog[m - 1]; /* dlog of -1 */

        int n_odd = 0, n_pos = 0, n_neg = 0;
        double net = 0;

        for (int j = 0; j < n_units; j++) {
            /* Check oddness */
            long long test = 2LL * j * dl_m1;
            /* chi_j(-1) = exp(2*pi*i * j*dl_m1/phi)
             * = -1 iff j*dl_m1/phi = 1/2 mod 1
             * iff 2*j*dl_m1 = phi mod 2*phi
             * iff 2*j*dl_m1 % (2*phi) == phi */
            if ((int)(test % (2 * n_units)) != n_units) continue;
            n_odd++;

            /* Compute s_hat_j */
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

            /* Compute P_j(0.5) = sum_p chi_j(p) / sqrt(p) */
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

            /* Product */
            double prod_re = sh_re * P_re - sh_im * P_im;
            net += prod_re;
            if (prod_re >= -1e-10) n_pos++;
            else n_neg++;
        }

        double pct = n_odd > 0 ? 100.0 * n_pos / n_odd : 0;
        printf("%5d %6s %4d %4d %4d %4d %5.1f%% %+9.3f\n",
               b, is_prime(b) ? "prime" : "comp",
               n_units, n_odd, n_pos, n_neg, pct, net);
    }

    return 0;
}
