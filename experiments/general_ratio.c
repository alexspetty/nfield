/*
 * general_ratio.c - Why is |ps|/|B1| constant at base 5 but not at base 13?
 *
 * At base 5: {1,2,3,4} is complete mod 5.
 * At base 13: {1,...,12} is complete mod 13.
 *
 * Key question: for primitive chi mod b^2, is
 * |sum_{k=1}^{b-1} chi_bar(k)| / |B_{1,chi_bar}|
 * constant?
 *
 * The partial sum is: P = sum_{k=1}^{b-1} chi_bar(k)
 * The Bernoulli number is: B1 = (1/m) sum_{a coprime to m} a chi(a)
 *
 * For the partial sum P, note that {1,...,b-1} is a complete
 * set of nonzero residues mod b. For a character chi mod b^2,
 * define chi_0 = chi restricted to mod b (the "coarse" character).
 *
 * Then P = sum_{k=1}^{b-1} chi_bar(k) where chi_bar(k) depends
 * on k mod b^2, but k < b so k mod b^2 = k. And the character
 * value chi(k) for k coprime to b depends on k's discrete log
 * mod b^2.
 *
 * If chi has conductor b^2 (primitive), then chi restricted
 * to {1,...,b-1} does NOT simplify to a character mod b.
 * The values chi(1),...,chi(b-1) involve the full mod-b^2
 * structure.
 *
 * But there IS a decomposition: (Z/b^2Z)* = (Z/bZ)* x (1 + bZ/b^2Z)
 * for prime b. The second factor has order b. So chi = chi_1 x chi_2
 * where chi_1 is mod b and chi_2 is mod b (the "fine" part).
 *
 * For k in {1,...,b-1}: k is in (Z/bZ)* x {1} (the "coarse" part
 * with fine component = 1). So chi(k) = chi_1(k) * chi_2(1) = chi_1(k).
 *
 * WAIT: that means sum_{k=1}^{b-1} chi_bar(k) = sum_{k=1}^{b-1} chi_1_bar(k)
 * which depends ONLY on the coarse part chi_1!
 *
 * If chi_1 is non-trivial: sum = -1 (complete character sum minus chi(0)=0).
 * Wait, sum_{k=1}^{b-1} chi_1(k) = sum over all nonzero residues mod b.
 * For non-trivial chi_1: this sum = -chi_1(0) = 0... no.
 * sum_{k=0}^{b-1} chi_1(k) = 0 for non-trivial chi_1.
 * So sum_{k=1}^{b-1} chi_1(k) = -chi_1(0) = 0.
 *
 * But chi_1(0) = 0 (0 is not coprime to b).
 * So sum_{k=1}^{b-1} chi_1(k) = sum_{k=0}^{b-1} chi_1(k) - chi_1(0) = 0 - 0 = 0
 * for non-trivial chi_1.
 *
 * And for trivial chi_1: sum = b-1.
 *
 * So: P = sum chi_bar(k) depends only on chi_1 (the mod-b part).
 * P = 0 if chi_1 is non-trivial.
 * P = b-1 if chi_1 is trivial.
 *
 * This means: for primitive chi mod b^2 with non-trivial chi_1,
 * P = 0, so S_G = 0, so s_hat should be small.
 * For chi with trivial chi_1 (i.e., chi trivial on (Z/bZ)*),
 * P = b-1, so S_G = -2 chi_bar(b+1) (b-1).
 *
 * Let me verify this!
 */

#include <stdio.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    int bases[] = {5, 7, 13};

    for (int bi = 0; bi < 3; bi++) {
        int b = bases[bi];
        int m = b * b;

        int units[m], n_units = 0;
        for (int a = 1; a < m; a++)
            if (gcd(a, m) == 1) units[n_units++] = a;

        int g = -1;
        for (int c = 2; c < m; c++) {
            if (gcd(c, m) != 1) continue;
            int v = 1, o = 0;
            do { v=(int)((long long)v*c%m); o++; } while (v!=1);
            if (o == n_units) { g = c; break; }
        }

        int dlog[m];
        memset(dlog, -1, sizeof(int)*m);
        { int v=1; for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);} }

        int dl_m1 = dlog[m-1];

        printf("=== Base %d (m=%d, phi=%d, gen=%d) ===\n", b, m, n_units, g);
        printf("dlog(m-1) = %d, so odd chars have j*%d = %d mod %d\n\n",
               dl_m1, dl_m1, n_units, 2*n_units);

        /* For each odd character j, compute:
         * 1. chi(k) for k = 1,...,b-1 and their sum
         * 2. Whether chi is trivial on (Z/bZ)* embedded in (Z/b^2Z)*
         *
         * (Z/bZ)* embeds via k -> k (for 1 <= k <= b-1).
         * chi is trivial on this subgroup iff chi(k) = 1 for all k in {1,...,b-1}.
         * Equivalently: j * dlog(k) = 0 mod phi for all k coprime to b with k < b.
         */

        printf("%4s %10s %8s %8s\n", "j", "|ps|", "triv_b?", "chi1");

        for (int j = 0; j < n_units; j++) {
            long long t = 2LL * j * dl_m1;
            if ((int)(t % (2*n_units)) != n_units) continue;

            /* Partial sum */
            double ps_re = 0, ps_im = 0;
            for (int k = 1; k <= b-1; k++) {
                if (dlog[k] < 0) continue;
                double angle = -2*M_PI*j*dlog[k]/(double)n_units;
                ps_re += cos(angle);
                ps_im += sin(angle);
            }
            double ps_mag = sqrt(ps_re*ps_re + ps_im*ps_im);

            /* Check if chi is trivial on {1,...,b-1} */
            int trivial_on_b = 1;
            for (int k = 2; k <= b-1; k++) {
                if (dlog[k] < 0) continue;
                double angle = 2*M_PI*j*dlog[k]/(double)n_units;
                if (fabs(cos(angle) - 1.0) > 1e-8 || fabs(sin(angle)) > 1e-8) {
                    trivial_on_b = 0;
                    break;
                }
            }

            /* What is chi_1 (the mod-b part)? */
            /* chi_1(k) = chi(k) for k coprime to b, k < b */
            /* The order of chi_1 divides b-1 */

            printf("%4d %10.4f %8s\n", j, ps_mag,
                   trivial_on_b ? "YES" : "no");
        }
        printf("\n");
    }

    return 0;
}
