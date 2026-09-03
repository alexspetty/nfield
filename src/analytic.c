/* Compatibility adapter for the historical `nfield analytic` command. */

#include <stdio.h>

#include "nfield.h"

void analytic_print(int base, int lag)
{
    printf("Legacy command: analytic\n");
    printf("Canonical object: periodic-zeta-factorization\n\n");
    printf("The compatibility command selects primitive odd character index 1\n");
    printf("and the real strip point s=1/2. For explicit character and complex\n");
    printf("parameters, use:\n\n");
    printf("  nfield periodic-zeta-factorization inspect %d %d 1 --sigma 0.5 --tau 0\n\n",
           base, lag);
    (void)periodic_zeta_factorization_inspect(
        base, lag, 1, 0.5L, 0.0L);
}
