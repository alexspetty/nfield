/*
 * composite_tensor.c - Does the collision transform of pq
 * have tensor structure from p and q?
 *
 * For n = p*q (two distinct primes, both coprime to b):
 * - Compute S(a) for a coprime to n, a mod n
 * - Compute the collision transform over characters mod n
 * - Characters mod n = characters mod p x characters mod q (CRT)
 * - Check: does s_hat(chi_p x chi_q) factor as f(s_hat_p, s_hat_q)?
 *
 * Start with small examples: b=10, p=7, q=11, n=77.
 */

#include <stdio.h>
#include <string.h>
#include <math.h>

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

int main(void) {
    int b = 10;
    int p = 7, q = 11;
    int n = p * q;  /* 77 */
    int m = b * b;  /* 100 */

    printf("Composite n = %d = %d x %d, base %d\n\n", n, p, q, b);

    /* Compute S for each prime separately (at lag 1) */
    /* S depends on the prime mod b^2 = 100 */

    /* For prime p=7: compute collision count C(b mod p) */
    int C_p = 0;
    for (int r = 1; r < p; r++) {
        int d1 = b * r / p;
        int d2 = b * (b * r % p) / p;
        if (d1 == d2) C_p++;
    }
    int S_p = C_p - (p - 1) / b;
    printf("S(%d) = %d (a = %d mod %d)\n", p, S_p, p % m, m);

    /* For prime q=11 */
    int C_q = 0;
    for (int r = 1; r < q; r++) {
        int d1 = b * r / q;
        int d2 = b * (b * r % q) / q;
        if (d1 == d2) C_q++;
    }
    int S_q = C_q - (q - 1) / b;
    printf("S(%d) = %d (a = %d mod %d)\n", q, S_q, q % m, m);

    /* For composite n=77: compute collision count */
    int C_n = 0;
    for (int r = 1; r < n; r++) {
        if (gcd(r, n) != 1) continue;  /* only count coprime residues */
        int d1 = b * r / n;
        int gr = (long long)b * r % n;
        int d2 = b * gr / n;
        if (d1 == d2) C_n++;
    }
    /* Q for composite: floor((phi(n))/b) or floor((n-1)/b)? */
    /* Actually for composite, S = C - Q where Q = floor((n-1)/b) */
    /* But we should use all residues 1..n-1 for the collision count */

    /* Redo: C counts over ALL r in 1..n-1, not just coprime */
    C_n = 0;
    for (int r = 1; r < n; r++) {
        int d1 = b * r / n;
        int gr = (int)((long long)b * r % n);
        int d2 = b * gr / n;
        if (d1 == d2) C_n++;
    }
    int S_n = C_n - (n - 1) / b;
    printf("S(%d) = %d\n", n, S_n);

    /* Now: compute S(a) for all a coprime to m=100, where a = n' mod 100
     * for various primes n'. But for the COMPOSITE, we want the
     * collision transform of S viewed on (Z/nZ)* not (Z/mZ)*.
     *
     * Actually, the collision transform is on (Z/b^2 Z)*. Both primes
     * p and q live in (Z/100Z)* through their residue mod 100.
     *
     * For the COMPOSITE question: we want to look at the fractional
     * field of 1/n = 1/(pq) and see how its digit structure decomposes.
     *
     * Different approach: compute the collision count C(g) for the
     * composite n for MANY multipliers g, not just g=b.
     * Then compare with C_p(g) and C_q(g).
     */

    printf("\nCollision counts C(g) for various multipliers:\n");
    printf("%4s %6s %6s %6s %8s\n", "g", "C_n", "C_p", "C_q", "relation");

    for (int g = 2; g < n && g < 30; g++) {
        if (gcd(g, n) != 1) continue;

        /* C for composite n */
        int Cn = 0;
        for (int r = 1; r < n; r++) {
            int d1 = b * r / n;
            int gr = (int)((long long)g * r % n);
            int d2 = b * gr / n;
            if (d1 == d2) Cn++;
        }

        /* C for prime p */
        int Cp = 0;
        for (int r = 1; r < p; r++) {
            int d1 = b * r / p;
            int gr = (int)((long long)(g % p) * r % p);
            int d2 = b * gr / p;
            if (d1 == d2) Cp++;
        }

        /* C for prime q */
        int Cq = 0;
        for (int r = 1; r < q; r++) {
            int d1 = b * r / q;
            int gr = (int)((long long)(g % q) * r % q);
            int d2 = b * gr / q;
            if (d1 == d2) Cq++;
        }

        /* Check various relations */
        /* C_n = C_p * q + C_q * p - C_p * C_q? */
        /* or C_n = C_p + C_q? */
        /* or C_n = C_p * C_q / b? */
        int sum = Cp + Cq;
        int prod = Cp * Cq;
        int Qn = (n-1)/b;
        int Qp = (p-1)/b;
        int Qq = (q-1)/b;

        printf("%4d %6d %6d %6d   sum=%d prod=%d Qn=%d\n",
               g, Cn, Cp, Cq, sum, prod, Qn);
    }

    /* Check: is S_n related to S_p and S_q through CRT? */
    /* CRT: Z/77Z = Z/7Z x Z/11Z */
    /* The digit function floor(br/77) and floor(br/7), floor(br/11)
     * are related by: r mod 77 determines r mod 7 and r mod 11.
     * But floor(br/77) != floor(br/7) in general. The bin structures
     * are different. */

    printf("\nDigit comparison: floor(10r/77) vs floor(10r/7), floor(10r/11)\n");
    printf("%4s %6s %6s %6s\n", "r", "d_77", "d_7", "d_11");
    for (int r = 1; r <= 20; r++) {
        printf("%4d %6d %6d %6d\n", r,
               10*r/77, 10*(r%7)/7, 10*(r%11)/11);
    }

    return 0;
}
