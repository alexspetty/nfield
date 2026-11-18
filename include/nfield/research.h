#ifndef NFIELD_PUBLIC_RESEARCH_H
#define NFIELD_PUBLIC_RESEARCH_H

/* Broad C99 research interfaces. Numeric types and return conventions follow
 * their module declarations; some legacy functions render to stdout or FILE.
 * Link with pkg-config --libs --static nfield-research. The core-only API and
 * its GMP-only dependency remain available through <nfield/nfield.h>. */
#include <nfield/nfield.h>
#include <nfield/research/arithmetic.h>
#include <nfield/research/native_arithmetic.h>
#include <nfield/research/native_directional.h>
#include <nfield/research/native_refinement.h>
#include <nfield/research/collision_sampling.h>
#include <nfield/research/collision_kernel_readout.h>
#include <nfield/research/collision_capacity_transition.h>
#include <nfield/research/collision_capacity_generation.h>
#include <nfield/research/boundary_spectrum.h>
#include <nfield/research/finite_character_core.h>
#include <nfield/research/primitive_odd_sector_core.h>
#include <nfield/research/collision_spectrum_core.h>
#include <nfield/research/collision_magnitude_moments.h>
#include <nfield/research/orbit_boundary_core.h>
#include <nfield/research/periodic_zeta_core.h>
#include <nfield/research/weighted_remainder_state.h>
#include <nfield/research/weighted_remainder_exact.h>
#include <nfield/research/weighted_remainder_floor.h>
#include <nfield/research/weighted_remainder_clock.h>
#include <nfield/research/weighted_remainder_weights.h>
#include <nfield/research/weighted_remainder_rows.h>
#include <nfield/research/weighted_remainder_increment.h>
#include <nfield/research/weighted_remainder_fourier.h>
#include <nfield/research/weighted_remainder_amplitude.h>
#include <nfield/research/weighted_remainder_constants.h>
#include <nfield/research/weighted_remainder_expansion.h>
#include <nfield/research/weighted_remainder_spectral.h>
#include <nfield/research/weighted_remainder_complex.h>
#include <nfield/research/weighted_remainder_character.h>
#include <nfield/research/weighted_remainder_cotangent.h>
#include <nfield/research/weighted_remainder_harmonic_root.h>
#include <nfield/research/weighted_remainder_small_amplitude.h>
#include <nfield/research/weighted_remainder_dirichlet.h>
#include <nfield/research/weighted_remainder_primitive.h>
#include <nfield/research/weighted_remainder_sawtooth.h>
#include <nfield/research/weighted_remainder_pairing.h>
#include <nfield/research/weighted_remainder_joint.h>
#include <nfield/research/weighted_remainder_cylinder.h>
#include <nfield/research/weighted_remainder_conductor.h>
#include <nfield/research/weighted_remainder_activation.h>
#include <nfield/research/weighted_remainder_alignment_local.h>
#include <nfield/research/weighted_remainder_alignment.h>
#include <nfield/research/weighted_remainder_alignment_growth.h>
#include <nfield/research/weighted_remainder_power.h>
#include <nfield/research/weighted_remainder_law.h>

#endif
