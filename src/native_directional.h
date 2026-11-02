#ifndef NFIELD_NATIVE_DIRECTIONAL_H
#define NFIELD_NATIVE_DIRECTIONAL_H
#include <stdio.h>
/* Numerical complete-period directional controls, 2<=first<last<=200,
 * base 2..10. Double precision solves; this is not an interval certificate. */
int native_directional_capture(unsigned first,unsigned last,unsigned base,FILE *out);
#endif
