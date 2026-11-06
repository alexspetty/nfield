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

## Coverage

Partial coverage formalizes individual capacity-inversion and
current-recognition clauses, with finite divisor and supporting Fourier
identities. The full symmetric regular-kernel inverse and current statements,
other generating and rigidity results, and asymptotic controls are not
formalized here.

## Scope and assumptions

Current recognition assumes zero mass at addresses zero and one, a nonzero
second mass, and total mass one; signed masses satisfying these conditions are
allowed. Multiple inversion assumes quadratic decay. The Fourier-series grid
identity assumes absolute summability. Interval recovery assumes two
derivatives and equal endpoint values, with the derivative endpoint jump
retained.

Only individual clauses of the inverse and current results are formalized. The
endpoint regularization from the original C3 kernel, scalar endpoint term and
full symmetric angular reconstruction are not formalized. The other generating
and rigidity results, asymptotic controls and sensitivity examples are also
not formalized. Finite computations are not all-scale theorems or certified
interval enclosures.
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
