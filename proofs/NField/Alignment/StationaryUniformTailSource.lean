/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryUniformTail

/-! # The literal dyadic source bounds for the uniform tail comparison -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryUniformTailSource
open StationaryDiagonalDefinitions StationaryCenteringDefinitions StationaryCenteringTail
  StationaryCumulativeWeight StationaryUniformTail CollisionRemainderDynamics

def uniformTailConstant : ℝ := 16 * weightErrorConstant + 4 * centeringErrorConstant + 2

theorem centeringErrorConstant_nonneg : 0 ≤ centeringErrorConstant := by
  unfold centeringErrorConstant
  positivity

theorem dyadic_log_bound {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) (hnX : n ≤ 2 * X) :
    Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (2 * (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnXR : (n : ℝ) ≤ 2 * X := by exact_mod_cast hnX
  calc
    _ ≤ Real.log ((2 * (X : ℝ)) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num

theorem dyadic_first_error_bound {M X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) (hnX : n ≤ 2 * X) :
    2 * weightErrorConstant * n * Real.log (2 * (n : ℝ)) ^ 2 / M ^ 2 ≤
      16 * weightErrorConstant * X * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 := by
  have hnXR : (n : ℝ) ≤ 2 * X := by exact_mod_cast hnX
  have hln : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * n by omega))
  have hs := pow_le_pow_left₀ hln (dyadic_log_bound hX hn hnX) 2
  have hh := mul_le_mul hnXR hs (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * X)
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * weightErrorConstant by positivity [weightErrorConstant_pos])
  apply div_le_div_of_nonneg_right _ (sq_nonneg (M : ℝ))
  convert! hh' using 1 <;> ring

theorem dyadic_second_error_bound {M X n : ℕ} (hX : 1 ≤ X) (hXn : X ≤ n) (hnX : n ≤ 2 * X) :
    2 * centeringErrorConstant * M * Real.log (2 * (n : ℝ)) / n ≤
      4 * centeringErrorConstant * M * Real.log (2 * (X : ℝ)) / X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXnR : (X : ℝ) ≤ n := by exact_mod_cast hXn
  have hnR : (0 : ℝ) < n := hXR.trans_le hXnR
  have hlog := dyadic_log_bound hX (hX.trans hXn) hnX
  have hlX : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * X by omega))
  have hratio : Real.log (2 * (n : ℝ)) / n ≤ (2 * Real.log (2 * (X : ℝ))) / X := by
    calc
      _ ≤ (2 * Real.log (2 * (X : ℝ))) / n := div_le_div_of_nonneg_right hlog hnR.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hXR hXnR
  have hh := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ 2 * centeringErrorConstant * M by positivity [centeringErrorConstant_nonneg])
  convert! hh using 1 <;> ring

/-- Title: `The smooth tail comparison holds uniformly on every source dyadic interval`. -/
theorem literal_tail_integral_bound {M X n : ℕ} (hM : 2 ≤ M) (hMX : M ≤ X)
    (hXn : X < n) (hnX : n ≤ 2 * X) :
    |diagonal n - finiteAge collisionWeight M n - smoothTail M n| ≤
      16 * weightErrorConstant * X * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
        2 * Real.log (2 * (M : ℝ)) / M := by
  have hMn : M ≤ n := hMX.trans hXn.le
  exact (diagonal_smooth_tail_error hM hMn).trans (add_le_add
    (dyadic_first_error_bound (by omega) (by omega) hnX) le_rfl)

/-- Title: `The centered diagonal satisfies all three printed uniform error terms`. -/
theorem literal_centered_uniform_bound {M X n : ℕ} (hM : 2 ≤ M) (hMX : M ≤ X)
    (hXn : X < n) (hnX : n ≤ 2 * X) :
    |centeredDiagonal n - finiteAge collisionWeight M n| ≤
      16 * weightErrorConstant * X * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
        4 * centeringErrorConstant * M * Real.log (2 * (X : ℝ)) / X +
          2 * Real.log (2 * (M : ℝ)) / M := by
  exact (centered_diagonal_tail_error hM (hMX.trans hXn.le)).trans
    (add_le_add (add_le_add (dyadic_first_error_bound (by omega) (by omega) hnX)
      (dyadic_second_error_bound (by omega) hXn.le hnX)) le_rfl)

/-- Title: `One absolute constant controls the full source uniform-tail lemma`. -/
theorem exists_uniform_tail_constant : ∃ C : ℝ, 0 < C ∧
    ∀ M X n : ℕ, 2 ≤ M → M ≤ X → X < n → n ≤ 2 * X →
      |centeredDiagonal n - finiteAge collisionWeight M n| ≤
        C * ((X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
          (M : ℝ) * Real.log (2 * (X : ℝ)) / X + Real.log (2 * (M : ℝ)) / M) := by
  have hC : 0 < uniformTailConstant := by
    unfold uniformTailConstant
    linarith [weightErrorConstant_pos, centeringErrorConstant_nonneg]
  refine ⟨uniformTailConstant, hC, ?_⟩
  intro M X n hM hMX hXn hnX
  have hA : 16 * weightErrorConstant ≤ uniformTailConstant := by
    unfold uniformTailConstant
    linarith [centeringErrorConstant_nonneg]
  have hB : 4 * centeringErrorConstant ≤ uniformTailConstant := by
    unfold uniformTailConstant
    linarith [weightErrorConstant_pos]
  have hD : (2 : ℝ) ≤ uniformTailConstant := by
    unfold uniformTailConstant
    linarith [weightErrorConstant_pos, centeringErrorConstant_nonneg]
  have hlM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hlX : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * X by omega))
  calc
    _ ≤ 16 * weightErrorConstant * X * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2 +
        4 * centeringErrorConstant * M * Real.log (2 * (X : ℝ)) / X +
          2 * Real.log (2 * (M : ℝ)) / M := literal_centered_uniform_bound hM hMX hXn hnX
    _ = (16 * weightErrorConstant) * ((X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2) +
        (4 * centeringErrorConstant) * ((M : ℝ) * Real.log (2 * (X : ℝ)) / X) +
          2 * (Real.log (2 * (M : ℝ)) / M) := by ring
    _ ≤ uniformTailConstant * ((X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 / M ^ 2) +
        uniformTailConstant * ((M : ℝ) * Real.log (2 * (X : ℝ)) / X) +
          uniformTailConstant * (Real.log (2 * (M : ℝ)) / M) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hA (by positivity))
        (mul_le_mul_of_nonneg_right hB (by positivity)))
        (mul_le_mul_of_nonneg_right hD (by positivity))
    _ = _ := by ring

end NField.Alignment.StationaryUniformTailSource
