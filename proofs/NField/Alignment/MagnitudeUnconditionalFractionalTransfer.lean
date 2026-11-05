/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperUnconditioningScales
import NField.Alignment.MagnitudeShortFractionalTransfer

/-!
# The short fractional moment after removing sharp grid conditioning

The actual all-character and primitive odd averages are bounded by the
ordinary Euler-product grid moment, up to an arbitrarily small multiple of the
manuscript target. The actual family, conjugation and square-root
normalization are inherited from the proved character transfer. No unconditional Euler-product low-moment saving or whole short
fractional-moment bound is assumed or proved.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.MagnitudeUnconditionalFractionalTransfer

open scoped BigOperators
open Filter SpectralRepulsion CollisionCharacterStructure PrimeSquareMagnitudeFamily
  MagnitudeLMomentBound HarperConditioningFrequencies HarperConditioningDecay
  HarperUnconditioningScales MagnitudeShortFractionalTransfer

theorem eventual_actual_character_unconditional_reduction {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero (p^2)], p.Prime →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2*unconditionalMainTerm p+epsilon*targetScale ((p : ℝ)-1) := by
  filter_upwards [eventual_actual_character_reduction (show 0 < epsilon/2 by positivity),
    eventual_actual_random_unconditional (show 0 < epsilon/4 by positivity)] with p hc hs
  intro _ hp
  have h := hc hp
  linarith

theorem eventual_normalized_unconditional_reduction {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero p] [NeZero (p^2)], p.Prime → p ≠ 2 →
    uniformAverage (fun χ : PrimitiveOddFamily p => (shortMagnitude p χ)^(3/2 : ℝ)) ≤
      (6*unconditionalMainTerm p+epsilon*targetScale ((p : ℝ)-1))/(p : ℝ)^(3/4 : ℝ) := by
  filter_upwards [eventual_normalized_random_reduction (show 0 < epsilon/2 by positivity),
    eventual_actual_random_unconditional (show 0 < epsilon/12 by positivity)] with p hc hs
  intro _ _ hp ho
  refine (hc hp ho).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end NField.Alignment.MagnitudeUnconditionalFractionalTransfer
