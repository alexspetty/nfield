/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteCapacityInverse
import NField.Alignment.CollisionResolutionCurrent
import NField.Alignment.AngularCoefficientInverse
import NField.Alignment.AngularGridFourier

/-!
# Finite Generation of Collision Capacity

This partial companion selects exact scalar-capacity differences and
finite divisor inversion, equality of capacity and positive-mass prefixes,
signed-current reconstruction, and recognition of the actual collision
mass by the von Mangoldt current. The current result retains the explicit
normalization at addresses zero and one, a nonzero second mass, and unit
total mass. It also applies to signed masses satisfying these hypotheses.

Supporting Fourier results give absolute inversion over multiples under
quadratic decay, interval coefficient decay with the derivative endpoint
jump retained, positive coefficient recovery, and exact complete-grid
orthogonality. The Fourier-series grid identity explicitly assumes absolute
summability. The interval recovery explicitly assumes two derivatives and
equal endpoint values.

## Coverage boundary

The capacity-to-mass clause of `thm:inverse` and the mass-recognition
clauses of `thm:current` are proved. Their full symmetric regular-kernel
claims are not formalized here: the endpoint regularization from the original
C3 kernel, recovery of the scalar endpoint term, and complete symmetric
angular reconstruction are not proved by these selections. These selections
formalize individual clauses of the named results. The other generating
and rigidity results, asymptotic controls and sensitivity examples are not
formalized here. Finite
computational examples are not all-scale theorems or Lean interval
certificates. This index does not claim whole-paper completion.
-/

namespace NField.Papers.FiniteGenerationOfCollisionCapacity

#check NField.Alignment.FiniteCapacityInverse.scaled_capacity_floor_sum
#check NField.Alignment.FiniteCapacityInverse.scaled_capacity_difference_pred
#check NField.Alignment.FiniteCapacityInverse.mass_from_capacity
#check NField.Alignment.FiniteCapacityInverse.capacity_prefix_determines_mass
#check NField.Alignment.FiniteCapacityInverse.mass_prefix_determines_capacity
#check NField.Alignment.FiniteCapacityInverse.capacity_prefix_iff_mass_prefix
#check NField.Alignment.FiniteCapacityInverse.all_capacities_iff_positive_masses
#check NField.Alignment.FiniteResolutionCurrent.current_coefficient_times_sequence
#check NField.Alignment.FiniteResolutionCurrent.current_div_address
#check NField.Alignment.FiniteResolutionCurrent.current_reconstruction_sum
#check NField.Alignment.FiniteResolutionCurrent.triangular_current_inverse
#check NField.Alignment.FiniteResolutionCurrent.signed_current_injective
#check NField.Alignment.ReciprocalResolutionCurrent.reciprocal_moebius_inverse
#check NField.Alignment.ReciprocalResolutionCurrent.reciprocal_inverse_apply
#check NField.Alignment.ReciprocalResolutionCurrent.reciprocal_current_coefficient
#check NField.Alignment.ReciprocalResolutionCurrent.reciprocal_current_eq_von_mangoldt
#check NField.Alignment.ReciprocalResolutionCurrent.reciprocal_current_prime_power
#check NField.Alignment.ReciprocalResolutionCurrent.reciprocal_current_zero_iff
#check NField.Alignment.ReciprocalResolutionCurrent.von_mangoldt_current_recognizes_reciprocal_sequence
#check NField.Alignment.FiniteResolutionMass.unprimitive_row_literal
#check NField.Alignment.FiniteResolutionMass.mass_from_unprimitive_row
#check NField.Alignment.FiniteResolutionMass.unprimitive_rows_determine_mass
#check NField.Alignment.FiniteResolutionMass.first_resolution_increment
#check NField.Alignment.FiniteResolutionMass.normalized_sequence_apply
#check NField.Alignment.FiniteResolutionMass.normalized_sequences_determine_mass_up_to_scale
#check NField.Alignment.FiniteResolutionMass.mass_current_injective
#check NField.Alignment.CollisionResolutionCurrent.collision_unprimitive_row
#check NField.Alignment.CollisionResolutionCurrent.collision_row_potential
#check NField.Alignment.CollisionResolutionCurrent.collision_resolution_increment
#check NField.Alignment.CollisionResolutionCurrent.collision_normalized_sequence
#check NField.Alignment.CollisionResolutionCurrent.collision_mass_current
#check NField.Alignment.CollisionResolutionCurrent.von_mangoldt_current_recognizes_collision_mass
#check NField.Alignment.CollisionResolutionCurrent.collision_mass_current_prime_power
#check NField.Alignment.SignedMultipleInverse.quadratic_decay_norm_summable
#check NField.Alignment.SignedMultipleInverse.inverse_series_norm_summable
#check NField.Alignment.SignedMultipleInverse.quadratic_decay_multiple_inverse
#check NField.Alignment.IntervalFourierDecay.twice_differentiated_coefficient
#check NField.Alignment.IntervalFourierDecay.cont_diff_two_coefficient_decay
#check NField.Alignment.AngularCoefficientInverse.positive_coefficient_quadratic_bound
#check NField.Alignment.AngularCoefficientInverse.positive_coefficients_norm_summable
#check NField.Alignment.AngularCoefficientInverse.coefficient_multiple_inverse
#check NField.Alignment.AngularCoefficientInverse.coefficient_inverse_absolutely_summable
#check NField.Alignment.AngularCoefficientInverse.multiple_readouts_determine_positive_coefficients
#check NField.Alignment.AngularGridFourier.grid_fourier_sum
#check NField.Alignment.AngularGridFourier.grid_fourier_mean
#check NField.Alignment.AngularGridFourier.grid_mean_fourier_series

end NField.Papers.FiniteGenerationOfCollisionCapacity
