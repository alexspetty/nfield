/* Why is base 5 exact? 
 * b=5, m=25, G = {0, 6, 12, 18, 24}, step = 6.
 * The good-slice sum has exactly 3 interior terms (k=1,2,3).
 *
 * Interior: chi_bar(7)-chi_bar(6), chi_bar(13)-chi_bar(12), chi_bar(19)-chi_bar(18)
 *
 * For m=25 (cyclic of order 20), let's see if these simplify.
 * 6 = b+1, 12 = 2(b+1), 18 = 3(b+1)
 * 7 = b+2, 13 = 2b+3, 19 = 3b+4
 *
 * Note: 25 - 6 = 19, 25 - 12 = 13, 25 - 18 = 7.
 * So the reflection pairs the interior points: 6<->19, 12<->13, 18<->7.
 * And n+1 values: 7<->20(=0, bad), 13<->12+1=13?, no...
 * Wait: the interior n values are 6,12,18 and n+1 are 7,13,19.
 * And 25-6=19, 25-12=13, 25-18=7.
 * So the n+1 values ARE the reflections of the n values!
 * 7 = 25 - 18, 13 = 25 - 12, 19 = 25 - 6.
 *
 * So chi_bar(n+1) = chi_bar(m - n') where n' is another good slice's n.
 * For odd chi: chi_bar(m-a) = chi_bar(-a) = chi_bar(-1) chi_bar(a) = -chi_bar(a).
 * So chi_bar(n+1_k) = -chi_bar(n_{b-1-k}).
 *
 * This means the S_G sum has a specific symmetry from the
 * reflection pairing of interior slices!
 */
#include <stdio.h>
int main(void) {
    int b = 5, m = 25;
    printf("Interior slice pairing for base %d:\n", b);
    for (int k = 1; k <= b-2; k++) {
        int n = k * (b+1);
        int n1 = n + 1;
        int refl_n = m - n;
        int refl_n1 = m - n1;
        printf("  k=%d: n=%d, n+1=%d, m-n=%d, m-(n+1)=%d\n",
               k, n, n1, refl_n, refl_n1);
    }
    
    printf("\nCheck: is n+1 of slice k = m - n of slice (b-1-k)?\n");
    for (int k = 1; k <= b-2; k++) {
        int n1 = k*(b+1) + 1;
        int other_n = (b-1-k) * (b+1);
        int m_other = m - other_n;
        printf("  k=%d: n+1=%d, m - n[%d]=%d, match=%s\n",
               k, n1, b-1-k, m_other,
               (n1 == m_other) ? "YES" : "NO");
    }
    
    /* General: k(b+1)+1 vs m - (b-1-k)(b+1) = m - (b-1)(b+1) + k(b+1) 
     * = m - b^2 + 1 + k(b+1) = 1 + k(b+1).
     * So YES: k(b+1)+1 = m - (b-1-k)(b+1) always! */
    printf("\nAlgebraic: k(b+1)+1 = b^2 - (b-1-k)(b+1) = b^2 - (b-1)(b+1) + k(b+1)\n");
    printf("         = b^2 - b^2 + 1 + k(b+1) = k(b+1) + 1. QED.\n");
    printf("\nSo n+1 for slice k equals m - n for slice (b-1-k).\n");
    printf("For odd chi: chi_bar(m-a) = -chi_bar(a).\n");
    printf("Therefore chi_bar(n+1_k) = -chi_bar(n_{b-1-k}).\n");
    
    return 0;
}
