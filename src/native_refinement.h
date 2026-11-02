#ifndef NFIELD_NATIVE_REFINEMENT_H
#define NFIELD_NATIVE_REFINEMENT_H

#include <stdio.h>

/* Finite native Hilbert-space diagnostics. 256-bit outward intervals,
 * complete infinite address weights, and the fixed origin T_4 d_3.
 * Supported frame range: 1 <= first < last <= 16.
 * Returns zero on success; no theorem about untested frames is asserted.
 * The caller owns the stream. No output is written on a failed calculation.
 */
/* Prescribed dyadic detector at N=2..100, using projections through 4N.
 * Complete native norm, outward intervals, no output on failure. */
int native_refinement_detector(unsigned N, FILE *out, int json);
/* Prescribed probes at N and 4N, N=2..8; signed response drift and Gram loss. */
int native_refinement_probe_transport(unsigned N, FILE *out, int json);
int native_refinement_trace(int first, int last, FILE *out, int json);
int native_refinement_collision4_calibration(FILE *out, int json);
int native_refinement_collision_families(int first, int last, FILE *out, int json);
int native_refinement_command(int argc, char **argv);
int native_refinement_verify(void);
void native_refinement_help(void);

#endif
