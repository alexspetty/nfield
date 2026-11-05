/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralActualRelabeling
import Mathlib.Algebra.Order.Floor.Ring

/-! # Literal floor and unscaled-variance displays -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SpectralPaperDetails
open scoped BigOperators
open SpectralRepulsion

theorem nested_floor_division (x : ℝ) (b : ℕ) :
    ⌊(⌊x⌋ : ℝ) / b⌋ = ⌊x / b⌋ := by
  rw [Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_intCast]

theorem uniformVariance_scale {Ω : Type*} [Fintype Ω] (c : ℝ) (z : Ω → ℝ) :
    uniformVariance (fun ω => c * z ω) = c ^ 2 * uniformVariance z := by
  unfold uniformVariance
  rw [uniformAverage_mul_left]
  have h (ω : Ω) : (c * z ω - c * uniformAverage z) ^ 2 =
      c ^ 2 * (z ω - uniformAverage z) ^ 2 := by ring
  simp_rw [h]
  exact uniformAverage_mul_left _ _

theorem unscaled_permutation_variance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hk : 1 < Fintype.card ι) :
    uniformVariance (fun π : Equiv.Perm ι => ∑ i, x i * y (π i)) =
      1 / (Fintype.card ι - 1 : ℝ) *
        (∑ r, (centeredMass x r) ^ 2) * (∑ r, (centeredMass y r) ^ 2) := by
  let S := fun π : Equiv.Perm ι => ∑ i, x i * y (π i)
  let k : ℝ := Fintype.card ι
  have hk0 : k ≠ 0 := by dsimp [k]; exact_mod_cast Fintype.card_ne_zero
  have hv := uniformVariance_scale k S
  change uniformVariance (fun π : Equiv.Perm ι =>
    relabelingStatistic x y (fun σ i => σ i) π) = k ^ 2 * uniformVariance S at hv
  rw [permutation_relabeling_variance x y hx hy hk] at hv
  change uniformVariance S = _
  calc
    uniformVariance S = (k ^ 2)⁻¹ * (k ^ 2 * uniformVariance S) := by field_simp
    _ = _ := by rw [← hv]; dsimp [k]; field_simp

end NField.Alignment.SpectralPaperDetails
