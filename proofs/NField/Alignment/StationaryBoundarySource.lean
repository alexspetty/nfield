/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryCenteredBoundary
import NField.Alignment.StationaryUniformTailSource

/-! # The full printed Bernoulli boundary lemma -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryBoundarySource
open StationaryDiagonalDefinitions StationaryCenteringDefinitions StationaryCenteredBoundary
  StationaryCumulativeWeight StationaryUniformTail StationaryUniformTailSource
  StationaryReciprocalSubstitution CollisionRemainderDynamics

def boundarySourceConstant : ℝ := 16 * weightErrorConstant + 2 + boundaryErrorConstant

theorem boundaryErrorConstant_nonneg : 0 ≤ boundaryErrorConstant := by
  unfold boundaryErrorConstant
  positivity

/-- Title: `The centered diagonal has the exact signed Bernoulli boundary and three controlled errors`. -/
theorem diagonal_boundary_error {M n : ℕ} (hM : 2 ≤ M) (hMn : M ≤ n) :
    |centeredDiagonal n - finiteAge collisionWeight M n - sourceBoundary M n| ≤
      2 * weightErrorConstant * n * Real.log (2 * (n : ℝ)) ^ 2 / M ^ 2 +
        2 * Real.log (2 * (M : ℝ)) / M +
          boundaryErrorConstant * M ^ 2 * Real.log (2 * (M : ℝ)) / n ^ 2 := by
  have hd := diagonal_smooth_tail_error hM hMn
  have hc := sourceBoundary_error (by omega : 1 ≤ M) hMn
  have hs : smoothTail M n = StationaryCenteringTail.truncatedCentering n ((n : ℝ) / M) :=
    smooth_tail_eq_truncatedCentering (by omega) hMn
  rw [← hs] at hc
  have he : centeredDiagonal n - finiteAge collisionWeight M n - sourceBoundary M n =
      (diagonal n - finiteAge collisionWeight M n - smoothTail M n) +
        (smoothTail M n - (biasCoefficient * Real.log n + biasConstant) - sourceBoundary M n) := by
    unfold centeredDiagonal
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hd hc)

/-- Title: `The Bernoulli boundary lemma holds on every dyadic interval at its printed scale`. -/
theorem literal_bernoulli_boundary_bound {M X n : ℕ} (hM : 2 ≤ M) (hMX : M ≤ X)
    (hXn : X < n) (hnX : n ≤ 2 * X) :
    |centeredDiagonal n - finiteAge collisionWeight M n - sourceBoundary M n| ≤
      16 * weightErrorConstant * X * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
        2 * Real.log (2 * (M : ℝ)) / M +
          boundaryErrorConstant * M ^ 2 * Real.log (2 * (M : ℝ)) / X ^ 2 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXnR : (X : ℝ) ≤ n := by exact_mod_cast hXn.le
  have hlM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hlast : boundaryErrorConstant * M ^ 2 * Real.log (2 * (M : ℝ)) / n ^ 2 ≤
      boundaryErrorConstant * M ^ 2 * Real.log (2 * (M : ℝ)) / X ^ 2 :=
    div_le_div_of_nonneg_left (by positivity [boundaryErrorConstant_nonneg]) (pow_pos hXR 2)
      (pow_le_pow_left₀ hXR.le hXnR 2)
  exact (diagonal_boundary_error hM (hMX.trans hXn.le)).trans
    (add_le_add (add_le_add (dyadic_first_error_bound (by omega) (by omega) hnX) le_rfl) hlast)

/-- Title: `One absolute constant proves the full Bernoulli boundary statement`. -/
theorem exists_bernoulli_boundary_constant : ∃ C : ℝ, 0 < C ∧
    ∀ M X n : ℕ, 2 ≤ M → M ≤ X → X < n → n ≤ 2 * X →
      |centeredDiagonal n - finiteAge collisionWeight M n - sourceBoundary M n| ≤
        C * ((X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
          Real.log (2 * (M : ℝ)) / M + (M : ℝ) ^ 2 * Real.log (2 * (M : ℝ)) / X ^ 2) := by
  have hC : 0 < boundarySourceConstant := by
    unfold boundarySourceConstant
    linarith [weightErrorConstant_pos, boundaryErrorConstant_nonneg]
  refine ⟨boundarySourceConstant, hC, ?_⟩
  intro M X n hM hMX hXn hnX
  have hA : 16 * weightErrorConstant ≤ boundarySourceConstant := by
    unfold boundarySourceConstant
    linarith [boundaryErrorConstant_nonneg]
  have hB : (2 : ℝ) ≤ boundarySourceConstant := by
    unfold boundarySourceConstant
    linarith [weightErrorConstant_pos, boundaryErrorConstant_nonneg]
  have hD : boundaryErrorConstant ≤ boundarySourceConstant := by
    unfold boundarySourceConstant
    linarith [weightErrorConstant_pos]
  have hlM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  calc
    _ ≤ 16 * weightErrorConstant * X * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
        2 * Real.log (2 * (M : ℝ)) / M +
          boundaryErrorConstant * M ^ 2 * Real.log (2 * (M : ℝ)) / X ^ 2 :=
      literal_bernoulli_boundary_bound hM hMX hXn hnX
    _ = (16 * weightErrorConstant) * ((X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2) +
        2 * (Real.log (2 * (M : ℝ)) / M) +
          boundaryErrorConstant * ((M : ℝ) ^ 2 * Real.log (2 * (M : ℝ)) / X ^ 2) := by ring
    _ ≤ boundarySourceConstant * ((X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2) +
        boundarySourceConstant * (Real.log (2 * (M : ℝ)) / M) +
          boundarySourceConstant * ((M : ℝ) ^ 2 * Real.log (2 * (M : ℝ)) / X ^ 2) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hA (by positivity))
        (mul_le_mul_of_nonneg_right hB (by positivity)))
        (mul_le_mul_of_nonneg_right hD (by positivity))
    _ = _ := by ring

end NField.Alignment.StationaryBoundarySource
