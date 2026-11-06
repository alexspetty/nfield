/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTailWeights

/-! # All three linked endpoint phases -/

noncomputable section

namespace NField.Alignment.CommonResetEndpointPhases

open scoped BigOperators
open CommonResetTailWeights CommonResetSineEndpoint CommonResetTrigonometric
open CommonResetShiftedDeterminants

theorem three_sine_phases (N θ φ : ℝ) :
    4*(Real.sin (N*θ)*Real.sin ((N+1)*θ)/Real.sin θ)*Real.sin φ =
      2*Real.cot θ*Real.sin φ-
        (Real.sin θ)⁻¹*(Real.sin (φ+(2*N+1)*θ)+Real.sin (φ-(2*N+1)*θ)) := by
  have hc : Real.cos θ-Real.cos ((2*N+1)*θ) =
      2*Real.sin (N*θ)*Real.sin ((N+1)*θ) := by
    calc
      _ = Real.cos ((N+1)*θ-N*θ)-Real.cos (N*θ+(N+1)*θ) := by
        congr 1 <;> congr 1 <;> ring
      _ = _ := by rw [Real.cos_sub, Real.cos_add]; ring
  calc
    _ = 2*(2*Real.sin (N*θ)*Real.sin ((N+1)*θ))/Real.sin θ*Real.sin φ := by ring
    _ = 2*(Real.cos θ-Real.cos ((2*N+1)*θ))/Real.sin θ*Real.sin φ := by rw [hc]
    _ = _ := by rw [Real.cot_eq_cos_div_sin, Real.sin_add, Real.sin_sub]; ring

theorem characterSine_int_nat {t : ℕ} [NeZero t] (n : ℤ) (a : ℕ) :
    characterSine ((n : ZMod t)*(a : ZMod t)) =
      Real.sin (2*Real.pi*(n : ℝ)*(a : ℝ)/(t : ℝ)) := by
  have he : ZMod.stdAddChar ((n : ZMod t)*(a : ZMod t)) =
      Complex.exp (Complex.ofReal (2*Real.pi*(n : ℝ)*(a : ℝ)/(t : ℝ))*Complex.I) := by
    rw [show (a : ZMod t) = ((a : ℤ) : ZMod t) by simp, ← Int.cast_mul,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  unfold characterSine
  rw [he, Complex.exp_ofReal_mul_I_im]

/-- Title: `The shifted phases keep the doubled modulus and the literal p minus one-half endpoint`. -/
theorem endpoint_phase_sine {t : ℕ} (ht : 0 < t) (p v u j : ℕ) (η : ℤ) :
    letI : NeZero (2*t) := ⟨by omega⟩
    characterSine ((twiceEndpointPhase p v u t η : ZMod (2*t))*(j : ZMod (2*t))) =
      Real.sin (2*Real.pi*(j : ℝ)*(p : ℝ)^2*(v : ℝ)*
        (DedekindInverseResidueTransform.inverseResidue u t : ℝ)/(t : ℝ)+
          (η : ℝ)*(2*(p : ℝ)-1)*halfAngle t j) := by
  letI : NeZero (2*t) := ⟨by omega⟩
  rw [characterSine_int_nat]
  congr 1
  unfold twiceEndpointPhase halfAngle
  push_cast
  ring

/-- Title: `A complete endpoint phase tail is controlled at its actual doubled period`. -/
theorem trigonometric_tail_bound_period (cot : Bool) (t : ℕ) {m : ℕ} [NeZero m]
    (start length : ℕ) (hs : 0 < start) (x : ZMod m) (hx : x ≠ 0) :
    ‖∑ a ∈ Finset.range length, (truncatedWeight cot t start a : ℂ)*
      ZMod.stdAddChar (x*((start+a : ℕ) : ZMod m))‖ ≤
      (t : ℝ)*(m : ℝ)/(2*(start : ℝ)*|(x.valMinAbs : ℝ)|) := by
  have hb := DedekindAbelRemainder.norm_antitone_weighted_sum_le
    (truncatedWeight cot t start) (fun a => ZMod.stdAddChar (x*((start+a : ℕ) : ZMod m)))
    (truncatedWeight_nonneg cot t start hs) (truncatedWeight_antitone cot t start hs)
    ((m : ℝ)/(2*|(x.valMinAbs : ℝ)|)) (by positivity)
    (fun n => character_prefix_norm x hx start n) (s := 0) (t := length)
  simp only [← Finset.range_eq_Ico, Complex.real_smul] at hb
  have hw : truncatedWeight cot t start 0 ≤ (t : ℝ)/(2*(start : ℝ)) := by
    unfold truncatedWeight
    simp only [Nat.add_zero]
    split_ifs with h
    · exact trigonometricWeight_le cot hs h
    · positivity
  calc
    _ ≤ 2*truncatedWeight cot t start 0*((m : ℝ)/(2*|(x.valMinAbs : ℝ)|)) := hb
    _ ≤ 2*((t : ℝ)/(2*(start : ℝ)))*((m : ℝ)/(2*|(x.valMinAbs : ℝ)|)) := by gcongr
    _ = _ := by ring

end NField.Alignment.CommonResetEndpointPhases
