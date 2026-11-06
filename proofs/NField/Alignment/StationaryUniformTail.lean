/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryReciprocalSubstitution
import NField.Alignment.StationaryDiagonalTailMass

/-! # The uniform diagonal tail comparison at its full integer scope -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryUniformTail
open scoped BigOperators
open StationaryDiagonalDefinitions StationaryCenteringDefinitions StationaryCenteringTail
  StationaryCumulativeWeight StationaryDiscreteTailComparison StationaryReciprocalSubstitution
  StationaryDiagonalTailMass CollisionRemainderDynamics

def smoothTail (M n : ℕ) : ℝ := (2 / 3 : ℝ) *
  ∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t)

/-- Title: `The diagonal tail is its exact smooth integral with a uniform absolute error`. -/
theorem diagonal_smooth_tail_error {M n : ℕ} (hM : 2 ≤ M) (hMn : M ≤ n) :
    |diagonal n - finiteAge collisionWeight M n - smoothTail M n| ≤
      2 * weightErrorConstant * n * Real.log (2 * (n : ℝ)) ^ 2 / M ^ 2 +
        2 * Real.log (2 * (M : ℝ)) / M := by
  have hd := discrete_smooth_tail_error hM hMn
  have hm0 := weightPrefix_tail_nonneg hMn
  have hm := weightPrefix_tail_bound (by omega : 1 ≤ M) hMn
  rw [diagonal_cutoff_tail hMn]
  unfold smoothTail
  have he : (2 / 3 : ℝ) * (∑ k ∈ Finset.Ioc M n, coefficient k * psi ((n : ℝ) / k)) +
      (weightPrefix n - weightPrefix M) / 3 -
      (2 / 3 : ℝ) * (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t)) =
      (2 / 3 : ℝ) * ((∑ k ∈ Finset.Ioc M n, coefficient k * psi ((n : ℝ) / k)) -
        (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t))) +
          (weightPrefix n - weightPrefix M) / 3 := by ring
  rw [he]
  calc
    _ ≤ |(2 / 3 : ℝ) * ((∑ k ∈ Finset.Ioc M n, coefficient k * psi ((n : ℝ) / k)) -
        (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t)))| +
          |(weightPrefix n - weightPrefix M) / 3| := abs_add_le _ _
    _ = (2 / 3 : ℝ) * |(∑ k ∈ Finset.Ioc M n, coefficient k * psi ((n : ℝ) / k)) -
        (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t))| +
          (weightPrefix n - weightPrefix M) / 3 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
        abs_of_nonneg (div_nonneg hm0 (by norm_num))]
    _ ≤ (2 / 3 : ℝ) * (3 * weightErrorConstant * n * Real.log (2 * (n : ℝ)) ^ 2 / M ^ 2) +
        (6 * Real.log (2 * (M : ℝ)) / M) / 3 := by gcongr
    _ = _ := by ring

/-- Title: `Centering the diagonal leaves the exact three uniform cutoff errors`. -/
theorem centered_diagonal_tail_error {M n : ℕ} (hM : 2 ≤ M) (hMn : M ≤ n) :
    |centeredDiagonal n - finiteAge collisionWeight M n| ≤
      2 * weightErrorConstant * n * Real.log (2 * (n : ℝ)) ^ 2 / M ^ 2 +
        2 * centeringErrorConstant * M * Real.log (2 * (n : ℝ)) / n +
          2 * Real.log (2 * (M : ℝ)) / M := by
  have hd := diagonal_smooth_tail_error hM hMn
  have hc := smooth_tail_centering_error (by omega : 1 ≤ M) hMn
  have he : centeredDiagonal n - finiteAge collisionWeight M n =
      (diagonal n - finiteAge collisionWeight M n - smoothTail M n) +
        (smoothTail M n - (biasCoefficient * Real.log n + biasConstant)) := by
    unfold centeredDiagonal
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by dsimp only [smoothTail] at hd hc ⊢; linarith)

end NField.Alignment.StationaryUniformTail
