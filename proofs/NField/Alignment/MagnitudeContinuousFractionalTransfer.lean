/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperContinuousReduction
import NField.Alignment.MagnitudeShortFractionalTransfer

/-!
# Actual character moments reduced to a continuous Euler-product moment

The complete random-conditioning reduction, including the reverse grid
comparison and its negligible error, is transported to the actual character
averages. The full-character and primitive odd populations, conjugation,
and square-root normalization remain those of the manuscript. The critical
continuous low-moment saving is not assumed or proved by this reduction.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeContinuousFractionalTransfer
open scoped BigOperators
open Filter SpectralRepulsion CollisionCharacterStructure PrimeSquareMagnitudeFamily
  MagnitudeLMomentBound HarperConditioningFrequencies HarperConditioningDecay
  HarperContinuousReduction MagnitudeShortFractionalTransfer

theorem eventual_actual_character_continuous_reduction {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero (p^2)], p.Prime →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2*continuousMainTerm p+epsilon*targetScale ((p : ℝ)-1) := by
  filter_upwards [eventual_actual_character_reduction (show 0 < epsilon/2 by positivity),
    eventual_actual_random_continuous (show 0 < epsilon/4 by positivity)] with p hc hs
  intro _ hp
  have h := hc hp
  linarith

theorem eventual_normalized_continuous_reduction {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero p] [NeZero (p^2)], p.Prime → p ≠ 2 →
    uniformAverage (fun χ : PrimitiveOddFamily p => (shortMagnitude p χ)^(3/2 : ℝ)) ≤
      (6*continuousMainTerm p+epsilon*targetScale ((p : ℝ)-1))/(p : ℝ)^(3/4 : ℝ) := by
  filter_upwards [eventual_normalized_random_reduction (show 0 < epsilon/2 by positivity),
    eventual_actual_random_continuous (show 0 < epsilon/12 by positivity)] with p hc hs
  intro _ _ hp ho
  refine (hc hp ho).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end NField.Alignment.MagnitudeContinuousFractionalTransfer
