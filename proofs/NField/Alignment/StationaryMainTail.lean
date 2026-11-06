/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryFiniteCumulative
import NField.Alignment.StationaryRatioKernel

/-! # The inverse-linear cost of extending the Möbius main polynomial -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryMainTail
open scoped BigOperators
open StationaryHarmonicProducts StationaryWeightConstants StationaryFiniteCumulative
  StationaryRatioKernel MobiusReciprocalSquare

def mainTailConstant : ℝ := 1 + |Real.eulerMascheroniConstant| +
  |(Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2|

theorem mainTailConstant_ge_one : 1 ≤ mainTailConstant := by
  unfold mainTailConstant
  linarith [abs_nonneg Real.eulerMascheroniConstant,
    abs_nonneg ((Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2)]

theorem harmonic_main_negative_log_bound {u : ℝ} (hu : u ≤ 0) :
    |u ^ 2 / 2 + Real.eulerMascheroniConstant * u +
      (Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| ≤
      mainTailConstant * (1 - u) ^ 2 := by
  have h1 : |u ^ 2 / 2 + Real.eulerMascheroniConstant * u +
      (Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| ≤
      u ^ 2 / 2 + |Real.eulerMascheroniConstant| * (-u) +
        |(Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| := by
    calc
      _ ≤ |u ^ 2 / 2 + Real.eulerMascheroniConstant * u| +
          |(Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| := abs_add_le _ _
      _ ≤ |u ^ 2 / 2| + |Real.eulerMascheroniConstant * u| +
          |(Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| := by
        gcongr
        exact abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg (by positivity : 0 ≤ u ^ 2 / 2), abs_mul, abs_of_nonpos hu]
  apply h1.trans
  have hg := abs_nonneg Real.eulerMascheroniConstant
  have hc := abs_nonneg ((Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2)
  have hsq := sq_nonneg u
  have hgu : 0 ≤ |Real.eulerMascheroniConstant| * u ^ 2 := mul_nonneg hg hsq
  have hcu : 0 ≤ |(Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| * u ^ 2 := mul_nonneg hc hsq
  have hgu' : 0 ≤ |Real.eulerMascheroniConstant| * (-u) := mul_nonneg hg (neg_nonneg.mpr hu)
  have hcu' : 0 ≤ |(Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2| * (-u) := mul_nonneg hc (neg_nonneg.mpr hu)
  unfold mainTailConstant
  nlinarith

theorem main_tail_term_bound {t : ℝ} (ht : 1 ≤ t) {d : ℕ} (hd : t < d) :
    |mobiusReciprocalSquare d * harmonicMain (t / d)| ≤
      mainTailConstant * ratioKernel ⌊t⌋₊ d := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := lt_trans ht0 hd
  have hM : (1 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hM0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast hM
  have hMle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
  have hu : Real.log (t / d) ≤ 0 := Real.log_nonpos (div_nonneg ht0.le hd0.le)
    ((div_le_one hd0).mpr hd.le)
  have hb := harmonic_main_negative_log_bound hu
  have hm : |mobiusReciprocalSquare d| ≤ 1 / (d : ℝ) ^ 2 := by
    unfold mobiusReciprocalSquare
    simp only [abs_div, abs_pow, abs_of_nonneg hd0.le]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hlog : 1 - Real.log (t / d) ≤ 1 + Real.log d - Real.log (⌊t⌋₊ : ℝ) := by
    rw [Real.log_div ht0.ne' hd0.ne']
    linarith [Real.log_le_log hM0 hMle]
  have hsquare : (1 - Real.log (t / d)) ^ 2 ≤
      (1 + Real.log d - Real.log (⌊t⌋₊ : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (by linarith) hlog 2
  rw [abs_mul]
  calc
    _ ≤ (1 / (d : ℝ) ^ 2) * (mainTailConstant * (1 - Real.log (t / d)) ^ 2) :=
      mul_le_mul hm hb (abs_nonneg _) (by positivity)
    _ ≤ (1 / (d : ℝ) ^ 2) * (mainTailConstant *
        (1 + Real.log d - Real.log (⌊t⌋₊ : ℝ)) ^ 2) := by
      gcongr
      exact le_trans (by norm_num) mainTailConstant_ge_one
    _ = _ := by unfold ratioKernel; ring

theorem main_tail_identity {t : ℝ} (ht : 0 < t) :
    cumulativeMain t - finiteMain t =
      ∑' j : ℕ, mobiusReciprocalSquare (j + ⌊t⌋₊ + 1) *
        harmonicMain (t / (j + ⌊t⌋₊ + 1 : ℕ)) := by
  let f : ℕ → ℝ := fun d => mobiusReciprocalSquare d * harmonicMain (t / d)
  have hs := (main_series_hasSum ht).summable.sum_add_tsum_nat_add (⌊t⌋₊ + 1)
  have hrange : (∑ d ∈ Finset.range (⌊t⌋₊ + 1), f d) = finiteMain t := by
    symm
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢
      omega
    · intro d hdRange hdIcc
      have hd0 : d = 0 := by
        simp only [Finset.mem_range] at hdRange
        simp only [Finset.mem_Icc, not_and_or, not_le] at hdIcc
        omega
      subst d
      simp [f, mobiusReciprocalSquare]
  change (∑ d ∈ Finset.range (⌊t⌋₊ + 1), f d) + _ = _ at hs
  rw [hrange, (main_series_hasSum ht).tsum_eq] at hs
  rw [← hs, add_sub_cancel_left]
  apply tsum_congr
  intro j
  simp [f, Nat.add_assoc]

/-- Title: `Extending the Möbius main polynomial costs only an inverse-linear remainder`. -/
theorem main_tail_bound {t : ℝ} (ht : 1 ≤ t) :
    |cumulativeMain t - finiteMain t| ≤ 10 * mainTailConstant / t := by
  have ht0 : 0 < t := by linarith
  have hM : (1 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hM0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast hM
  have hM2 : t ≤ 2 * (⌊t⌋₊ : ℝ) := by
    have hfl := Nat.lt_floor_add_one t
    have h1 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hM
    linarith
  let f : ℕ → ℝ := fun d => mobiusReciprocalSquare d * harmonicMain (t / d)
  have hsum : Summable (fun j => f (j + ⌊t⌋₊ + 1)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (f := f) (⌊t⌋₊ + 1)).mpr
      (main_series_hasSum ht0).summable
  have hb : ∀ j : ℕ, |f (j + ⌊t⌋₊ + 1)| ≤
      mainTailConstant * ratioKernel ⌊t⌋₊ (j + ⌊t⌋₊ + 1 : ℕ) := by
    intro j
    apply main_tail_term_bound ht
    have hfl := Nat.lt_floor_add_one t
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [main_tail_identity ht0]
  calc
    _ ≤ ∑' j : ℕ, |f (j + ⌊t⌋₊ + 1)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' j : ℕ, mainTailConstant * ratioKernel ⌊t⌋₊ (j + ⌊t⌋₊ + 1 : ℕ) :=
      hsum.abs.tsum_le_tsum hb ((ratio_kernel_tail_summable hM).mul_left mainTailConstant)
    _ = mainTailConstant * ∑' j : ℕ, ratioKernel ⌊t⌋₊ (j + ⌊t⌋₊ + 1 : ℕ) := tsum_mul_left
    _ ≤ mainTailConstant * (5 / (⌊t⌋₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left (ratio_kernel_tail_bound hM) (by linarith [mainTailConstant_ge_one])
    _ ≤ 10 * mainTailConstant / t := by
      have hi : 1 / (⌊t⌋₊ : ℝ) ≤ 2 / t := by
        apply (div_le_div_iff₀ hM0 ht0).mpr
        simpa using hM2
      have hc : 0 ≤ 5 * mainTailConstant := by linarith [mainTailConstant_ge_one]
      have hh := mul_le_mul_of_nonneg_left hi hc
      calc
        _ = (5 * mainTailConstant) * (1 / (⌊t⌋₊ : ℝ)) := by ring
        _ ≤ (5 * mainTailConstant) * (2 / t) := hh
        _ = _ := by ring

end NField.Alignment.StationaryMainTail
