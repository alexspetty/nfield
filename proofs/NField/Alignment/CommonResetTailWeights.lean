/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetFrequencies
import NField.Alignment.CommonResetShiftedDeterminants
import NField.Alignment.DedekindAbelRemainder
import NField.Alignment.InverseChordMonotonicity

/-! # Actual decreasing cotangent and cosecant tail weights -/

noncomputable section

namespace NField.Alignment.CommonResetTailWeights

open scoped BigOperators
open CommonResetFourier CommonResetSineEndpoint DedekindCarrierFourierBound SpectralPower

def halfAngle (t a : ℕ) : ℝ := Real.pi*(a : ℝ)/(t : ℝ)

theorem halfAngle_bounds {t a : ℕ} (ha : 0 < a) (hat : 2*a < t) :
    0 < halfAngle t a ∧ halfAngle t a < Real.pi/2 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · exact div_pos (mul_pos Real.pi_pos haR) htR
  · apply (div_lt_iff₀ htR).mpr
    have hh : 2*(a : ℝ) < t := by exact_mod_cast hat
    nlinarith [mul_lt_mul_of_pos_left hh Real.pi_pos]

theorem half_sine_lower {t a : ℕ} (ha : 0 < a) (hat : 2*a < t) :
    (2*(a : ℝ)/(t : ℝ)) ≤ Real.sin (halfAngle t a) := by
  have hangle := halfAngle_bounds ha hat
  have hh := Real.mul_le_sin hangle.1.le hangle.2.le
  have he : 2/Real.pi*halfAngle t a = 2*(a : ℝ)/(t : ℝ) := by
    unfold halfAngle
    field_simp
  rwa [he] at hh

def trigonometricWeight (cot : Bool) (t a : ℕ) : ℝ :=
  if cot then Real.cot (halfAngle t a) else (Real.sin (halfAngle t a))⁻¹

theorem trigonometricWeight_nonneg (cot : Bool) {t a : ℕ}
    (ha : 0 < a) (hat : 2*a < t) : 0 ≤ trigonometricWeight cot t a := by
  have hangle := halfAngle_bounds ha hat
  have hs := Real.sin_pos_of_pos_of_lt_pi hangle.1 (hangle.2.trans (by linarith [Real.pi_pos]))
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hangle.2⟩
  cases cot <;> simp only [trigonometricWeight, Bool.false_eq_true, ite_false, ite_true]
  · exact inv_nonneg.mpr hs.le
  · rw [Real.cot_eq_cos_div_sin]
    exact div_nonneg hc.le hs.le

theorem trigonometricWeight_le (cot : Bool) {t a : ℕ}
    (ha : 0 < a) (hat : 2*a < t) :
    trigonometricWeight cot t a ≤ (t : ℝ)/(2*(a : ℝ)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hs := half_sine_lower ha hat
  have hspos : 0 < Real.sin (halfAngle t a) := lt_of_lt_of_le (by positivity) hs
  have hi : (Real.sin (halfAngle t a))⁻¹ ≤ (t : ℝ)/(2*(a : ℝ)) := by
    calc
      _ ≤ (2*(a : ℝ)/(t : ℝ))⁻¹ := inv_anti₀ (by positivity) hs
      _ = _ := by field_simp
  cases cot <;> simp only [trigonometricWeight, Bool.false_eq_true, ite_false, ite_true]
  · exact hi
  · rw [Real.cot_eq_cos_div_sin]
    exact (div_le_div_of_nonneg_right (Real.cos_le_one _) hspos.le).trans
      (by simpa only [one_div] using hi)

theorem trigonometricWeight_antitone (cot : Bool) {t a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbt : 2*b < t) :
    trigonometricWeight cot t b ≤ trigonometricWeight cot t a := by
  have haangle := halfAngle_bounds ha (by omega : 2*a < t)
  have hbangle := halfAngle_bounds (by omega : 0 < b) hbt
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have habangle : halfAngle t a ≤ halfAngle t b := by
    apply div_le_div_of_nonneg_right _ htR.le
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hab) Real.pi_pos.le
  cases cot <;> simp only [trigonometricWeight, Bool.false_eq_true, ite_false, ite_true]
  · apply inv_anti₀
    · exact Real.sin_pos_of_pos_of_lt_pi haangle.1 (by linarith [Real.pi_pos])
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hbangle.2.le habangle
  · simp only [Real.cot_eq_cos_div_sin]
    have hh := InverseChordMonotonicity.cot_ratio_antitone
      ((a : ℝ)/(t : ℝ)) ((b : ℝ)/(t : ℝ))
      (div_pos (by exact_mod_cast ha) htR)
      ((div_lt_one htR).mpr (by exact_mod_cast (show b < t by omega)))
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hab) htR.le)
    simpa only [halfAngle, mul_div_assoc] using hh

def truncatedWeight (cot : Bool) (t start n : ℕ) : ℝ :=
  if 2*(start+n) < t then trigonometricWeight cot t (start+n) else 0

theorem truncatedWeight_nonneg (cot : Bool) (t start : ℕ) (hs : 0 < start) (n : ℕ) :
    0 ≤ truncatedWeight cot t start n := by
  unfold truncatedWeight
  split_ifs with h
  · exact trigonometricWeight_nonneg cot (by omega) h
  · exact le_rfl

theorem truncatedWeight_antitone (cot : Bool) (t start : ℕ) (hs : 0 < start) :
    Antitone (truncatedWeight cot t start) := by
  intro a b hab
  unfold truncatedWeight
  by_cases hb : 2*(start+b) < t
  · have ha : 2*(start+a) < t := by omega
    rw [if_pos hb, if_pos ha]
    exact trigonometricWeight_antitone cot (by omega) (by omega) hb
  · rw [if_neg hb]
    split_ifs with ha
    · exact trigonometricWeight_nonneg cot (by omega) ha
    · exact le_rfl

theorem character_prefix_norm {t : ℕ} [NeZero t] (x : ZMod t) (hx : x ≠ 0)
    (start length : ℕ) :
    ‖∑ a ∈ Finset.range length, ZMod.stdAddChar (x*((start+a : ℕ) : ZMod t))‖ ≤
      (t : ℝ)/(2*|(x.valMinAbs : ℝ)|) := by
  have he : (∑ a ∈ Finset.range length, ZMod.stdAddChar (x*((start+a : ℕ) : ZMod t))) =
      ZMod.stdAddChar (x*(start : ZMod t))*intervalFourier t length (-x) := by
    unfold intervalFourier
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Nat.cast_add, mul_add, AddChar.map_add_eq_mul]
    congr 1
    congr 1
    ring
  rw [he, norm_mul, AddChar.norm_apply, one_mul]
  have hb := norm_intervalFourier_le_circular (NeZero.pos t) (length := length) (neg_ne_zero.mpr hx)
  have hd : (DedekindFourierMoment.circularDistance t (-x).val : ℝ) = |(x.valMinAbs : ℝ)| := by
    rw [DedekindFourierMoment.circularDistance, ← ZMod.valMinAbs_natAbs_eq_min,
      ZMod.natAbs_valMinAbs_neg]
    simpa only [Int.cast_abs, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs x.valMinAbs)
  rwa [hd] at hb

/-- Title: `A whole cotangent or cosecant tail has the actual reciprocal-chord bound`. -/
theorem trigonometric_tail_bound (cot : Bool) {t : ℕ} [NeZero t]
    (start length : ℕ) (hs : 0 < start) (x : ZMod t) (hx : x ≠ 0) :
    ‖∑ a ∈ Finset.range length, (truncatedWeight cot t start a : ℂ)*
      ZMod.stdAddChar (x*((start+a : ℕ) : ZMod t))‖ ≤
      (t : ℝ)^2/(2*(start : ℝ)*|(x.valMinAbs : ℝ)|) := by
  have hb := DedekindAbelRemainder.norm_antitone_weighted_sum_le
    (truncatedWeight cot t start) (fun a => ZMod.stdAddChar (x*((start+a : ℕ) : ZMod t)))
    (truncatedWeight_nonneg cot t start hs) (truncatedWeight_antitone cot t start hs)
    ((t : ℝ)/(2*|(x.valMinAbs : ℝ)|)) (by positivity)
    (fun n => character_prefix_norm x hx start n) (s := 0) (t := length)
  simp only [← Finset.range_eq_Ico, Complex.real_smul] at hb
  have hw : truncatedWeight cot t start 0 ≤ (t : ℝ)/(2*(start : ℝ)) := by
    unfold truncatedWeight
    simp only [Nat.add_zero]
    split_ifs with h
    · exact trigonometricWeight_le cot hs h
    · positivity
  calc
    _ ≤ 2*truncatedWeight cot t start 0*((t : ℝ)/(2*|(x.valMinAbs : ℝ)|)) := hb
    _ ≤ 2*((t : ℝ)/(2*(start : ℝ)))*((t : ℝ)/(2*|(x.valMinAbs : ℝ)|)) := by gcongr
    _ = _ := by ring

end NField.Alignment.CommonResetTailWeights
