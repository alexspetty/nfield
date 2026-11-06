/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryBoundarySource
import NField.Alignment.StationaryIncompleteCycles
import NField.Alignment.StationaryPeriodicSourceRates
import NField.Alignment.StationaryZetaConstants

/-!
# The Stationary-to-Diagonal Transition in Collision Capacity

This partial companion selects the precise cumulative-weight expansion,
the exact moving-diagonal identities, the full uniform tail comparison,
the periodic first and second moments, including bounded-variation weights
for the first moment, and the signed Bernoulli boundary term. These are the five named claims
`lem:weight`, `prop:exact`, `lem:tail`, `lem:periodic`, and `lem:boundary`.
All cutoffs, integer atoms, signs, and error terms retain their stated scope.

The supporting results evaluate both conditional sawtooth integrals,
the actual zeta derivatives in the centering constants, and the negative
logarithmic drift. Conditional integrals are limits of finite integrals;
they are not asserted to be absolutely integrable.

## Coverage boundary

Five of the paper's 22 named claims are covered here. The growing-cutoff
Gram estimate, centered empirical law and rates, capacity residual law,
unit-Haar prime law, growing-modulus prime estimates, frozen-cutoff
transition, and later exceptional-set and perturbation conclusions are
not formalized here. Fixed-modulus prime results do not supply the required uniform
prime estimates. The prime-square sampling defect and the sharper
unit-Haar questions remain open. Decimal approximations are not certified
interval enclosures. This index does not claim whole-paper completion.
-/

namespace NField.Papers.StationaryToDiagonalTransition

#check NField.Alignment.StationaryDiagonalDefinitions.psi_integer
#check NField.Alignment.StationaryWeightConstants.main_series_hasSum
#check NField.Alignment.StationaryZetaConstants.alpha_eq_reciprocal_zeta
#check NField.Alignment.StationaryZetaConstants.first_mobius_log_moment
#check NField.Alignment.StationaryZetaConstants.second_mobius_log_moment
#check NField.Alignment.StationaryCumulativeWeight.precise_cumulative_weight
#check NField.Alignment.StationaryCumulativeWeight.exists_precise_cumulative_weight_constant
#check NField.Alignment.StationaryExactDiagonal.diagonal_psi
#check NField.Alignment.StationaryExactDiagonal.diagonal_mobius
#check NField.Alignment.StationaryIncompleteCycles.centered_incomplete_cycle
#check NField.Alignment.StationaryIncompleteCycles.diagonal_total
#check NField.Alignment.StationaryIncompleteCycles.diagonal_total_nonpos
#check NField.Alignment.StationaryConditionalConstants.integralZero_tail_bound
#check NField.Alignment.StationaryConditionalConstants.integralOne_tail_bound
#check NField.Alignment.StationaryConditionalConstants.integralZero_tendsto
#check NField.Alignment.StationaryConditionalConstants.integralOne_tendsto
#check NField.Alignment.StationaryStirlingConstant.integralZero_evaluation
#check NField.Alignment.StationarySecondCenteringConstant.integralOne_eq_zeta_second_derivative
#check NField.Alignment.StationaryCenteringDefinitions.biasCoefficient_formula
#check NField.Alignment.StationaryCenteringDefinitions.biasCoefficient_negative
#check NField.Alignment.StationaryCenteringDefinitions.biasConstant_zeta_formula
#check NField.Alignment.StationaryReciprocalSubstitution.smooth_tail_eq_truncatedCentering
#check NField.Alignment.StationaryUniformTailSource.literal_tail_integral_bound
#check NField.Alignment.StationaryUniformTailSource.literal_centered_uniform_bound
#check NField.Alignment.StationaryUniformTailSource.exists_uniform_tail_constant
#check NField.Alignment.StationaryPeriodicSourceRates.periodic_first_source_rate
#check NField.Alignment.StationaryPeriodicSourceRates.periodic_second_source_rate
#check NField.Alignment.StationaryPeriodicSourceRates.weighted_periodic_first_source_rate
#check NField.Alignment.StationaryCenteredBoundary.truncatedCentering_boundary_identity
#check NField.Alignment.StationaryCenteredBoundary.smoothBoundary_eq_sourceBoundary
#check NField.Alignment.StationaryCenteredBoundary.sourceBoundary_error
#check NField.Alignment.StationaryBoundarySource.diagonal_boundary_error
#check NField.Alignment.StationaryBoundarySource.literal_bernoulli_boundary_bound
#check NField.Alignment.StationaryBoundarySource.exists_bernoulli_boundary_constant

end NField.Papers.StationaryToDiagonalTransition
