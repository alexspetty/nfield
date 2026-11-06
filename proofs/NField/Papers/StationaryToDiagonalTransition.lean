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

## Coverage

Five of the 22 named results are formalized: the cumulative-weight expansion,
moving-diagonal identities, uniform tail comparison, periodic first and second
moments, and signed Bernoulli boundary term. Bounded-variation weights are
covered for the first moment. The growing-modulus prime estimates and the
later transition laws are not formalized here.

## Scope and assumptions

The raw sawtooth retains its stated integer-atom values, cutoffs and endpoint
terms. The two conditional sawtooth integrals are limits of finite integrals;
absolute integrability is not asserted. Bounded-variation weighting is proved
for the first moment, not for the second moment.

The growing-cutoff Gram estimate, centered empirical law and rates, capacity
residual law, unit-Haar prime law, growing-modulus prime estimates,
frozen-cutoff transition and later exceptional-set and perturbation
conclusions are not formalized. Fixed-modulus prime results do not supply the
required uniform estimates. The prime-square sampling defect and sharper
unit-Haar questions remain open. Decimal approximations are not certified
interval enclosures.
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
