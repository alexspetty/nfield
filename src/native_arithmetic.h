#ifndef NFIELD_NATIVE_ARITHMETIC_H
#define NFIELD_NATIVE_ARITHMETIC_H
#include <gmp.h>
/* All array entries are initialized by the caller; coefficient zero is unused.
 * Exact tapered packet coefficients through 8*t; 2<=t<=128. Invalid input
 * preserves the output. The capacity must include index 8*t. Returns 1 on
 * success, 0 on failure. Entries beyond index 8*t are untouched. */
int native_packet_coefficients(mpq_t *out,unsigned capacity,unsigned t);
/* Returns -1 for an operation owned by the native projection interface. */
int native_arithmetic_command(int argc,char **argv);
void native_arithmetic_help(void);
#endif
