/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FirstDerivativeCancellation

/-! # Inverse-chord monotonicity on a real period -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.InverseChordMonotonicity
open FirstDerivativeCancellation FejerKernel

/-- The character and real trigonometric phase use the same sign convention. -/
theorem character_exp (t : ℝ) : fourier 1 (t : AddCircle (1 : ℝ)) =
    Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem sine_positive (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : 0 < Real.sin (Real.pi*t) := by
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  nlinarith [Real.pi_pos]

/-- Exact cotangent coordinates of the inverse chord, away from the integers. -/
theorem inverseChord_im (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (inverseChord (fourier 1 (t : AddCircle (1 : ℝ)))).im =
      -Real.cos (Real.pi*t)/(2*Real.sin (Real.pi*t)) := by
  have hs := sine_positive t ht ht1
  have hd : Complex.normSq (fourier 1 (t : AddCircle (1 : ℝ))-1) =
      4*(Real.sin (Real.pi*t))^2 := by
    rw [Complex.normSq_eq_norm_sq, character_distance, mul_pow, sq_abs]
    ring
  unfold inverseChord
  rw [Complex.inv_im, Complex.sub_im, Complex.one_im, sub_zero, hd, character_exp,
    Complex.exp_ofReal_mul_I_im]
  rw [show 2*Real.pi*t = 2*(Real.pi*t) by ring, Real.sin_two_mul]
  field_simp
  ring

/-- Cotangent decreases throughout a single open half-turn. -/
theorem cot_ratio_antitone (s t : ℝ) (hs : 0 < s) (ht1 : t < 1) (hst : s ≤ t) :
    Real.cos (Real.pi*t)/Real.sin (Real.pi*t) ≤ Real.cos (Real.pi*s)/Real.sin (Real.pi*s) := by
  have hss := sine_positive s hs (by linarith)
  have hts := sine_positive t (by linarith) ht1
  apply (div_le_div_iff₀ hts hss).mpr
  have hh : 0 ≤ Real.sin (Real.pi*t-Real.pi*s) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  rw [Real.sin_sub] at hh
  nlinarith

/-- The imaginary inverse-chord coordinate increases with its phase. -/
theorem inverseChord_im_monotone (s t : ℝ) (hs : 0 < s) (ht1 : t < 1) (hst : s ≤ t) :
    (inverseChord (fourier 1 (s : AddCircle (1 : ℝ)))).im ≤
      (inverseChord (fourier 1 (t : AddCircle (1 : ℝ)))).im := by
  rw [inverseChord_im s hs (by linarith), inverseChord_im t (by linarith) ht1]
  have hh := cot_ratio_antitone s t hs ht1 hst
  calc
    _ = -(Real.cos (Real.pi*s)/Real.sin (Real.pi*s))/2 := by ring
    _ ≤ -(Real.cos (Real.pi*t)/Real.sin (Real.pi*t))/2 := by linarith
    _ = _ := by ring

theorem character_ne_one (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    fourier 1 (t : AddCircle (1 : ℝ)) ≠ 1 := by
  intro hh
  have hn := character_distance t
  rw [hh, sub_self, norm_zero, abs_of_pos (sine_positive t ht ht1)] at hn
  linarith [sine_positive t ht ht1]

/-- The inverse chord has the required inverse-distance endpoint bound. -/
theorem inverseChord_norm_bound (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1/2) :
    ‖inverseChord (fourier 1 (t : AddCircle (1 : ℝ)))‖ ≤ 1/(4*t) := by
  have hs := Real.mul_le_sin (x := Real.pi*t) (by positivity) (by nlinarith [Real.pi_pos])
  have he : 2/Real.pi*(Real.pi*t) = 2*t := by field_simp
  rw [he] at hs
  have hd : 4*t ≤ ‖fourier 1 (t : AddCircle (1 : ℝ))-1‖ := by
    rw [character_distance]
    nlinarith [le_abs_self (Real.sin (Real.pi*t))]
  unfold inverseChord
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 4*t) hd

end NField.Alignment.InverseChordMonotonicity
