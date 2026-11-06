/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryHarmonicProducts

/-! # The precise harmonic-product expansion at every real cutoff -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryRealHarmonicProducts
open StationaryHarmonicProducts CollisionStationaryAgeAsymptotic

theorem floor_log_error {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ Real.log u - Real.log (⌊u⌋₊ : ℝ) ∧
      Real.log u - Real.log (⌊u⌋₊ : ℝ) ≤ 2 / u := by
  have hn : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by simpa using hu)
  have hnR : (1 : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < ⌊u⌋₊ := by linarith
  have hu0 : 0 < u := by linarith
  have hlo := Nat.floor_le hu0.le
  have hhi := Nat.lt_floor_add_one u
  have hlog := Real.log_le_log hn0 hlo
  constructor
  · linarith
  · have hratio := Real.log_le_sub_one_of_pos (div_pos hu0 hn0)
    rw [Real.log_div hu0.ne' hn0.ne'] at hratio
    have hsmall : u / (⌊u⌋₊ : ℝ) - 1 ≤ 1 / (⌊u⌋₊ : ℝ) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hn0).mpr
      have he : (1 / (⌊u⌋₊ : ℝ) + 1) * (⌊u⌋₊ : ℝ) = 1 + (⌊u⌋₊ : ℝ) := by field_simp
      rw [he]
      linarith
    have hscale : 1 / (⌊u⌋₊ : ℝ) ≤ 2 / u := by
      apply (div_le_div_iff₀ hn0 hu0).mpr
      linarith
    linarith

theorem harmonic_main_floor_error {u : ℝ} (hu : 1 ≤ u) :
    |harmonicMain (⌊u⌋₊ : ℝ) - harmonicMain u| ≤ 2 * (1 + Real.log u) / u := by
  have hn : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by simpa using hu)
  have hnR : (1 : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast hn
  have hl := Real.log_nonneg hu
  have hln := Real.log_nonneg hnR
  have hd := floor_log_error hu
  have hg0 : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hg1 : Real.eulerMascheroniConstant ≤ 1 := by linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have he : harmonicMain u - harmonicMain (⌊u⌋₊ : ℝ) =
      (Real.log u - Real.log (⌊u⌋₊ : ℝ)) *
        ((Real.log u + Real.log (⌊u⌋₊ : ℝ)) / 2 + Real.eulerMascheroniConstant) := by
    unfold harmonicMain
    ring
  have hf0 : 0 ≤ (Real.log u + Real.log (⌊u⌋₊ : ℝ)) / 2 + Real.eulerMascheroniConstant := by positivity
  have hf : (Real.log u + Real.log (⌊u⌋₊ : ℝ)) / 2 + Real.eulerMascheroniConstant ≤ 1 + Real.log u := by linarith
  rw [abs_sub_comm, he, abs_of_nonneg (mul_nonneg hd.1 hf0)]
  have hm := mul_le_mul hd.2 hf hf0 (by positivity : 0 ≤ 2 / u)
  calc
    _ ≤ (2 / u) * (1 + Real.log u) := hm
    _ = _ := by ring

/-- Title: `The harmonic-product constant and error hold at arbitrary real cutoffs`. -/
theorem harmonic_product_real_error {u : ℝ} (hu : 1 ≤ u) :
    |((harmonic ⌊u⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊u⌋₊) / 2 - harmonicMain u| ≤
      6 * (1 + Real.log u) / u := by
  have hn : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by simpa using hu)
  have hnR : (1 : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < ⌊u⌋₊ := by linarith
  have hu0 : 0 < u := by linarith
  have hl := Real.log_nonneg hu
  have hln := Real.log_nonneg hnR
  have hmono := Real.log_le_log hn0 (Nat.floor_le hu0.le)
  have hscale : 1 / (⌊u⌋₊ : ℝ) ≤ 2 / u := by
    apply (div_le_div_iff₀ hn0 hu0).mpr
    linarith [Nat.lt_floor_add_one u]
  have hb := harmonic_product_natural_error hn
  have hcoarse : 2 * (1 + Real.log (⌊u⌋₊ : ℝ)) / (⌊u⌋₊ : ℝ) ≤
      4 * (1 + Real.log u) / u := by
    calc
      _ = (2 * (1 + Real.log (⌊u⌋₊ : ℝ))) * (1 / (⌊u⌋₊ : ℝ)) := by ring
      _ ≤ (2 * (1 + Real.log u)) * (2 / u) := by gcongr
      _ = _ := by ring
  have htriangle := abs_sub_le (((harmonic ⌊u⌋₊ : ℝ) ^ 2 - harmonicSquareSum ⌊u⌋₊) / 2)
    (harmonicMain (⌊u⌋₊ : ℝ)) (harmonicMain u)
  have hf := harmonic_main_floor_error hu
  calc
    _ ≤ 4 * (1 + Real.log u) / u + 2 * (1 + Real.log u) / u :=
      htriangle.trans (add_le_add (hb.trans hcoarse) hf)
    _ = _ := by ring

end NField.Alignment.StationaryRealHarmonicProducts
