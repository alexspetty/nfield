/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperConditioningFrequencies
import NField.Alignment.MagnitudeLMomentBound

/-!
# The actual primitive odd short fractional moment

Positivity and the exact family population give the printed factor 2p/(p-1).
Conjugation and the square-root normalization are retained. Combining this
with the actual character reduction leaves a concrete random conditioning
sum and a proved negligible error; no bound on that random sum is asserted.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.MagnitudeShortFractionalTransfer

open scoped BigOperators
open Filter SpectralRepulsion CollisionCharacterStructure PrimeSquareMagnitudeFamily
  MagnitudeLMomentBound HarperConditioningFrequencies HarperConditioningDecay
  FiniteMagnitudeDecorrelation

theorem shortSum_norm_eq (p : ℕ) (χ : PrimitiveOddFamily p) :
    ‖shortSum p χ‖ = ‖∑ n ∈ Finset.Icc 1 (p-1), χ.val (n : ZMod (p^2))‖ := by
  unfold shortSum
  rw [← star_sum, norm_star]

theorem shortMagnitude_three_halves (p : ℕ) (χ : PrimitiveOddFamily p) :
    (shortMagnitude p χ)^(3/2 : ℝ) =
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ.val (n : ZMod (p^2))‖^(3/2 : ℝ) /
        (p : ℝ)^(3/4 : ℝ) := by
  rw [shortMagnitude, Real.div_rpow (norm_nonneg _) (Real.sqrt_nonneg _),
    shortSum_norm_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg p)]
  norm_num

theorem primitive_short_moment_restriction {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily p =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ.val (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      (2*(p : ℝ)/((p : ℝ)-1)) * uniformAverage (fun χ : Character (p^2) =>
        ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) :=
  primitive_family_average_le hp hpodd
    (fun χ => ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ))
    (fun _ => by positivity)

theorem normalized_fractional_restriction {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily p => (shortMagnitude p χ)^(3/2 : ℝ)) ≤
      ((2*(p : ℝ)/((p : ℝ)-1)) * uniformAverage (fun χ : Character (p^2) =>
        ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ))) / (p : ℝ)^(3/4 : ℝ) := by
  have he : uniformAverage (fun χ : PrimitiveOddFamily p => (shortMagnitude p χ)^(3/2 : ℝ)) =
      uniformAverage (fun χ : PrimitiveOddFamily p =>
        ‖∑ n ∈ Finset.Icc 1 (p-1), χ.val (n : ZMod (p^2))‖^(3/2 : ℝ)) / (p : ℝ)^(3/4 : ℝ) := by
    simp_rw [shortMagnitude_three_halves]
    unfold uniformAverage
    rw [← Finset.sum_div]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right (primitive_short_moment_restriction hp hpodd) (by positivity)

theorem eventual_normalized_random_reduction {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero p] [NeZero (p^2)], p.Prime → p ≠ 2 →
    uniformAverage (fun χ : PrimitiveOddFamily p => (shortMagnitude p χ)^(3/2 : ℝ)) ≤
      (6 * actualRandomConditioning p + epsilon * targetScale ((p : ℝ)-1)) / (p : ℝ)^(3/4 : ℝ) := by
  filter_upwards [eventual_actual_character_reduction (show 0 < epsilon/3 by positivity)] with p hp
  intro _ _ hprime hodd
  have hc := hp hprime
  have hfull : 0 ≤ uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) :=
    average_nonneg (fun _ => by positivity)
  have hf := mul_le_mul_of_nonneg_right (primitive_family_factor_le_three hprime hodd) hfull
  refine (normalized_fractional_restriction hprime hodd).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end NField.Alignment.MagnitudeShortFractionalTransfer
