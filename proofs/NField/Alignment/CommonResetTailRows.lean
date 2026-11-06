/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTailWeights

/-! # Complete linear-frequency tails of the actual source -/

noncomputable section

namespace NField.Alignment.CommonResetTailRows

open scoped BigOperators
open CommonResetFourier CommonResetHalfFrequencies CommonResetSineEndpoint
open CommonResetTrigonometric CommonResetFrequencies CommonResetTailWeights
open CommonResetDeterminants DedekindInverseResidueTransform

theorem sinePrefix_abs_bound {t : ℕ} [NeZero t] (N : ℕ) (j : ZMod t)
    (hj : j ∈ lowerResidues t) :
    |sinePrefix N j| ≤ (t : ℝ)/(2*(j.val : ℝ)) := by
  have hjd := (Finset.mem_filter.mp hj).2
  have ha := halfAngle_bounds hjd.1 hjd.2
  have hs : 0 < Real.sin (halfAngle t j.val) :=
    Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos])
  change 0 < Real.sin (Real.pi*(j.val : ℝ)/(t : ℝ)) at hs
  rw [sinePrefix_closed N j hj, abs_div, abs_of_nonneg hs.le]
  have hnum : |Real.sin (Real.pi*(j.val : ℝ)*(N : ℝ)/(t : ℝ))*
      Real.sin (Real.pi*(j.val : ℝ)*((N : ℝ)+1)/(t : ℝ))| ≤ 1 := by
    rw [abs_mul]
    calc
      _ ≤ (1 : ℝ)*1 := mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc
    _ ≤ 1/Real.sin (halfAngle t j.val) := div_le_div_of_nonneg_right hnum hs.le
    _ ≤ _ := by simpa only [trigonometricWeight, Bool.false_eq_true, ite_false, one_div]
      using trigonometricWeight_le false hjd.1 hjd.2

theorem linear_coefficient_bound {t : ℕ} [NeZero t] (N : ℕ) (u : (ZMod t)ˣ)
    (j : ZMod t) (hu : u ∈ lowerUnits t) (hj : j ∈ lowerResidues t) :
    |(4/(t : ℝ)^2)*cotangentResidue u.val*sinePrefix N j| ≤
      1/((u.val.val : ℝ)*(j.val : ℝ)) := by
  have hud := (Finset.mem_filter.mp hu).2
  have hjd := (Finset.mem_filter.mp hj).2
  have hcot0 : 0 ≤ cotangentResidue u.val :=
    trigonometricWeight_nonneg true hud.1 hud.2
  have hcot : cotangentResidue u.val ≤ (t : ℝ)/(2*(u.val.val : ℝ)) :=
    trigonometricWeight_le true hud.1 hud.2
  have hs := sinePrefix_abs_bound N j hj
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4/(t : ℝ)^2),
    abs_of_nonneg hcot0]
  calc
    _ ≤ (4/(t : ℝ)^2)*((t : ℝ)/(2*(u.val.val : ℝ)))*((t : ℝ)/(2*(j.val : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcot (by positivity)
      · exact hs
      · exact abs_nonneg _
      · positivity
    _ = _ := by
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
      field_simp
      norm_num

def linearTail {t : ℕ} [NeZero t] (N q : ℕ) (u : (ZMod t)ˣ) (j : ZMod t)
    (start length : ℕ) : ℝ :=
  ∑ a ∈ Finset.range length, if 2*(start+a) < t then
    frequencyTerm N q u ((start+a : ℕ) : ZMod t) j else 0

theorem linearTail_im {t : ℕ} [NeZero t] (N q : ℕ) (u : (ZMod t)ˣ) (j : ZMod t)
    (start length : ℕ) (hs : 0 < start) :
    linearTail N q u j start length =
      ((4/(t : ℝ)^2)*cotangentResidue u.val*sinePrefix N j)*
        (∑ a ∈ Finset.range length, (truncatedWeight true t start a : ℂ)*
          ZMod.stdAddChar ((j*(q : ZMod t)*(↑(u⁻¹) : ZMod t))*
            ((start+a : ℕ) : ZMod t))).im := by
  rw [Complex.im_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 2*(start+a) < t
  · have halt : start+a < t := by omega
    have hphase : j*((q : ZMod t)*((start+a : ℕ) : ZMod t)*(↑(u⁻¹) : ZMod t)) =
        (j*(q : ZMod t)*(↑(u⁻¹) : ZMod t))*((start+a : ℕ) : ZMod t) := by ring
    simp only [if_pos ha, frequencyTerm, truncatedWeight, trigonometricWeight, ite_true,
      cotangentResidue, ZMod.val_natCast, Nat.mod_eq_of_lt halt, halfAngle,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      characterSine, hphase]
    ring
  · simp only [if_neg ha, truncatedWeight, Complex.ofReal_zero, zero_mul, Complex.zero_im,
      mul_zero]

/-- Title: `The entire retained linear-frequency tail obeys its determinant bound`. -/
theorem linear_tail_bound {t : ℕ} [NeZero t] (N q : ℕ) (u : (ZMod t)ˣ)
    (j : ZMod t) (hu : u ∈ lowerUnits t) (hj : j ∈ lowerResidues t)
    (start length : ℕ) (hs : 0 < start)
    (hx : j*(q : ZMod t)*(↑(u⁻¹) : ZMod t) ≠ 0) :
    |linearTail N q u j start length| ≤
      (t : ℝ)^2/(2*(start : ℝ)*(u.val.val : ℝ)*(j.val : ℝ)*
        |((j*(q : ZMod t)*(↑(u⁻¹) : ZMod t)).valMinAbs : ℝ)|) := by
  rw [linearTail_im N q u j start length hs, abs_mul]
  have ht := trigonometric_tail_bound true start length hs
    (j*(q : ZMod t)*(↑(u⁻¹) : ZMod t)) hx
  have hIm := (Complex.abs_im_le_norm _).trans ht
  calc
    _ ≤ (1/((u.val.val : ℝ)*(j.val : ℝ)))*
        ((t : ℝ)^2/(2*(start : ℝ)*|((j*(q : ZMod t)*(↑(u⁻¹) : ZMod t)).valMinAbs : ℝ)|)) := by
      apply mul_le_mul (linear_coefficient_bound N u j hu hj) hIm (abs_nonneg _)
      positivity
    _ = _ := by ring

/-- Title: `The linear-tail phase has the actual prime-square centered residue`. -/
theorem linear_phase_center {t : ℕ} [NeZero t] (p : ℕ) (u : (ZMod t)ˣ) (j : ZMod t) :
    (j*((p^2 : ℕ) : ZMod t)*(↑(u⁻¹) : ZMod t)).valMinAbs =
      centeredCarrier p j.val u.val.val t := by
  unfold centeredCarrier
  rw [Nat.cast_mul, Nat.cast_mul, inverseResidue_of_unit, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]
  congr 1
  ring

end NField.Alignment.CommonResetTailRows
