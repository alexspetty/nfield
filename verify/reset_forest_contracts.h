#ifndef NFIELD_RESET_FOREST_CONTRACTS_H
#define NFIELD_RESET_FOREST_CONTRACTS_H

/* Execute the finite numerical contract panels. A nonzero json argument emits
 * one nfield.checks.v1 document. Return 0 when all checks pass, otherwise 1. */
int reset_forest_contracts_verify(int json);

#endif
