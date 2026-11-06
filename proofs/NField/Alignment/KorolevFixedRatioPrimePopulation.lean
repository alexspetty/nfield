/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimePopulation

/-! # Actual prime populations in fixed-ratio intervals -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevFixedRatioPrimePopulation
open KorolevPrimeIntervals

/-- A logarithmic increment has a lower bound at its upper endpoint. -/
theorem log_increment_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha), inv_div] at h
  simpa only [sub_div, div_self (ne_of_gt hb)] using h

/-- Fixed logarithmic width supplies a population bound for actual coprime primes. -/
theorem coprime_population_lower {m : ℕ} (hm : 0 < m) {u v A : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) (hA : 0 < A)
    (herror : 8 * errorConstant ≤ A)
    (hwidth : Real.log v = Real.log u + A) (hsize : A ≤ Real.log u)
    (hmod : 8 * Real.log m ≤ A * u) :
    u * A / (4 * Real.log v) ≤
      (((intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlv : 0 < Real.log v := by linarith
  have hlogs : Real.log u ≤ Real.log v := by linarith
  have hdouble : Real.log v ≤ 2 * Real.log u := by linarith
  have hmass := log_increment_lower hlu hlogs
  have hinc : A / Real.log v ≤ Real.log (Real.log v) - Real.log (Real.log u) := by
    convert hmass using 1 <;> rw [hwidth] <;> ring
  have hE : 0 ≤ errorConstant := errorConstant_pos.le
  have herr : 2 * errorConstant / Real.log u ≤ A / (2 * Real.log v) := by
    apply (div_le_div_iff₀ hlu (by positivity : 0 < 2 * Real.log v)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdouble hE,
      mul_le_mul_of_nonneg_right herror hlu.le]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hremove : Real.log m / (u * Real.log u) ≤ A / (4 * Real.log v) := by
    apply (div_le_div_iff₀ (mul_pos hu0 hlu) (by positivity : 0 < 4 * Real.log v)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdouble hlm,
      mul_le_mul_of_nonneg_right hmod hlu.le]
  have hremaining : A / (4 * Real.log v) ≤
      Real.log (Real.log v) - Real.log (Real.log u) -
        2 * errorConstant / Real.log u - Real.log m / (u * Real.log u) := by
    have hfractions : A / Real.log v =
        A / (2 * Real.log v) + A / (4 * Real.log v) + A / (4 * Real.log v) := by
      field_simp
      <;> ring
    linarith
  calc
    u * A / (4 * Real.log v) = u * (A / (4 * Real.log v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hremaining hu0.le
    _ ≤ _ := KorolevPrimePopulation.coprime_population_lower hm hu huv

end NField.Alignment.KorolevFixedRatioPrimePopulation
