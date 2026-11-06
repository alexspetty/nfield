/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
# Exact Fourier extraction by complete rational grids

The finite orthogonality calculation uses Mathlib's primitive additive character
of `ZMod q`. The series identity assumes absolute Fourier summability; the
regularity criterion is supplied separately by the interval decay results.
-/

noncomputable section

namespace NField.Alignment.AngularGridFourier

open scoped BigOperators Real

def gridPoint {q : ℕ} (a : ZMod q) : AddCircle (1 : ℝ) :=
  ((a.val : ℝ) / q : ℝ)

def gridMean (q : ℕ) [NeZero q] (f : AddCircle (1 : ℝ) → ℂ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, f (gridPoint a)

theorem grid_fourier_character {q : ℕ} [NeZero q] (n : ℤ) (a : ZMod q) :
    fourier n (gridPoint a) = ZMod.stdAddChar ((n : ZMod q) * a) := by
  have hcast : ((n * (a.val : ℤ) : ℤ) : ZMod q) = (n : ZMod q) * a := by
    simp
  rw [← hcast, ZMod.stdAddChar_coe, gridPoint, fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Title: `Complete rational grids annihilate the nondivisible Fourier frequencies`. -/
theorem grid_fourier_sum {q : ℕ} [NeZero q] (n : ℤ) :
    ∑ a : ZMod q, fourier n (gridPoint a) = if (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  simp_rw [grid_fourier_character]
  by_cases h : (n : ZMod q) = 0
  · have hd : (q : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n q).mp h
    simp [h, hd, ZMod.card]
  · have hd : ¬ (q : ℤ) ∣ n := by
      simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd n q] using h
    rw [if_neg hd]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

/-- Title: `Complete rational grids select the divisible Fourier frequencies`. -/
theorem grid_fourier_mean {q : ℕ} [NeZero q] (n : ℤ) :
    gridMean q (fourier n) = if (q : ℤ) ∣ n then 1 else 0 := by
  rw [gridMean, grid_fourier_sum]
  split_ifs
  · exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne q))
  · exact mul_zero _

/-- Title: `Absolute Fourier series can be averaged over complete rational grids`. -/
theorem grid_mean_fourier_series {q : ℕ} [NeZero q]
    (f : C(AddCircle (1 : ℝ), ℂ)) (hf : Summable (fourierCoeff f)) :
    gridMean q f = ∑' n : ℤ, if (q : ℤ) ∣ n then fourierCoeff f n else 0 := by
  have hs (a : ZMod q) := has_pointwise_sum_fourier_series_of_summable hf (gridPoint a)
  have hsum := hasSum_sum (s := Finset.univ) (fun a _ => hs a)
  have hmean := hsum.mul_left (q : ℂ)⁻¹
  have heq : (fun n : ℤ => (q : ℂ)⁻¹ *
      ∑ a : ZMod q, fourierCoeff f n • fourier n (gridPoint a)) =
      (fun n : ℤ => if (q : ℤ) ∣ n then fourierCoeff f n else 0) := by
    funext n
    simp only [smul_eq_mul, ← Finset.mul_sum, grid_fourier_sum]
    split_ifs
    · field_simp [show (q : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne q)]
    · simp
  rw [heq] at hmean
  exact hmean.tsum_eq.symm

end NField.Alignment.AngularGridFourier
