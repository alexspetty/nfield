/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryRealHarmonicProducts
import NField.Alignment.StationaryWeightConstants

/-! # Exact finite Möbius expansion and the summed harmonic remainder -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryFiniteCumulative
open scoped BigOperators
open StationaryDiagonalDefinitions StationaryHarmonicProducts StationaryRealHarmonicProducts
  StationaryWeightConstants CollisionStationaryAgeAsymptotic MobiusReciprocalSquare

def finiteMain (t : ℝ) : ℝ := ∑ d ∈ Finset.Icc 1 ⌊t⌋₊,
  mobiusReciprocalSquare d * harmonicMain (t / d)

/-- Title: `The cumulative weight has its exact real-cutoff harmonic product expansion`. -/
theorem cumulative_weight_mobius (t : ℝ) :
    cumulativeWeight t = ∑ d ∈ Finset.Icc 1 ⌊t⌋₊,
      mobiusReciprocalSquare d *
        (((harmonic ⌊t / d⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊t / d⌋₊) / 2) := by
  rw [cumulativeWeight_firstMoment, firstMoment_moebius, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.floor_div_natCast]
  ring

theorem finite_main_term_error {t : ℝ} (ht : 1 ≤ t) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 ⌊t⌋₊) :
    |mobiusReciprocalSquare d *
      ((((harmonic ⌊t / d⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊t / d⌋₊) / 2) - harmonicMain (t / d))| ≤
      (6 / t) * (1 + Real.log t) / d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hd0 : (0 : ℝ) < d := by linarith
  have ht0 : 0 < t := by linarith
  have hdt : (d : ℝ) ≤ t := (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d : ℝ) ≤ ⌊t⌋₊).trans (Nat.floor_le ht0.le)
  have hu : 1 ≤ t / d := (le_div_iff₀ hd0).mpr (by linarith)
  have hul : Real.log (t / d) ≤ Real.log t := Real.log_le_log (div_pos ht0 hd0)
    (div_le_self ht0.le hd1)
  have hm : |mobiusReciprocalSquare d| ≤ 1 / (d : ℝ) ^ 2 := by
    unfold mobiusReciprocalSquare
    simp only [abs_div, abs_pow, abs_of_nonneg hd0.le]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [abs_mul]
  calc
    _ ≤ (1 / (d : ℝ) ^ 2) * (6 * (1 + Real.log (t / d)) / (t / d)) :=
      mul_le_mul hm (harmonic_product_real_error hu) (abs_nonneg _) (by positivity)
    _ = (6 / t) * (1 + Real.log (t / d)) / d := by field_simp
    _ ≤ _ := by gcongr

/-- Title: `The summed harmonic-product error has the precise inverse-linear scale`. -/
theorem cumulative_finite_main_error {t : ℝ} (ht : 1 ≤ t) :
    |cumulativeWeight t - finiteMain t| ≤ 6 * (1 + Real.log t) ^ 2 / t := by
  rw [cumulative_weight_mobius, finiteMain, ← Finset.sum_sub_distrib]
  have he : (∑ d ∈ Finset.Icc 1 ⌊t⌋₊,
      (mobiusReciprocalSquare d * (((harmonic ⌊t / d⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊t / d⌋₊) / 2) -
        mobiusReciprocalSquare d * harmonicMain (t / d))) =
      ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, mobiusReciprocalSquare d *
        ((((harmonic ⌊t / d⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊t / d⌋₊) / 2) - harmonicMain (t / d)) := by
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊t⌋₊,
        |mobiusReciprocalSquare d *
          ((((harmonic ⌊t / d⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊t / d⌋₊) / 2) - harmonicMain (t / d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, (6 / t) * (1 + Real.log t) / d :=
      Finset.sum_le_sum (fun d hd => finite_main_term_error ht hd)
    _ = (6 / t) * (1 + Real.log t) * (harmonic ⌊t⌋₊ : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (6 / t) * (1 + Real.log t) * (1 + Real.log t) := by
      exact mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log t ht)
        (mul_nonneg (by positivity) (by linarith [Real.log_nonneg ht]))
    _ = _ := by ring

end NField.Alignment.StationaryFiniteCumulative
