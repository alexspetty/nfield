/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetEndpointTailRows
import NField.Alignment.CommonResetSecondDerivative

/-! # The actual cotangent amplitudes increase across every conductor interval -/

noncomputable section

namespace NField.Alignment.CommonResetAmplitude

open scoped BigOperators
open Set CommonResetTailWeights

theorem angle_cot_derivative {x : ℝ} (hx : 0 < x) (hxp : x < Real.pi/2) :
    HasDerivAt (fun y : ℝ => y*Real.cot y)
      ((Real.sin x*Real.cos x-x)/(Real.sin x)^2) x := by
  have hs : Real.sin x ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])).ne'
  have hd := ((hasDerivAt_id' x).mul (Real.hasDerivAt_cos x)).div (Real.hasDerivAt_sin x) hs
  convert! hd using 1
  · ext y
    change y*Real.cot y = (y*Real.cos y)/Real.sin y
    rw [Real.cot_eq_cos_div_sin]
    ring
  · change (Real.sin x*Real.cos x-x)/(Real.sin x)^2 =
      ((1*Real.cos x+x*(-Real.sin x))*Real.sin x-x*Real.cos x*Real.cos x)/(Real.sin x)^2
    congr 1
    linear_combination x*(Real.sin_sq_add_cos_sq x)

theorem angle_cot_antitone : AntitoneOn (fun x : ℝ => x*Real.cot x) (Ioo 0 (Real.pi/2)) := by
  have hderiv (x : ℝ) (hx : x ∈ Ioo 0 (Real.pi/2)) := angle_cot_derivative hx.1 hx.2
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _)
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
  · intro x hx
    exact (hderiv x (by simpa only [interior_Ioo] using hx)).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 (Real.pi/2) := by simpa only [interior_Ioo] using hx
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have hs := Real.sin_le (show (0 : ℝ) ≤ 2*x by linarith [hx'.1])
    rw [Real.sin_two_mul] at hs
    linarith

/-- Title: `The scaled cotangent factor increases with the actual conductor`. -/
theorem scaled_cotangent_monotone {a t s : ℕ} (ha : 0 < a) (hat : 2*a < t) (hts : t ≤ s) :
    Real.cot (halfAngle t a)/(t : ℝ) ≤ Real.cot (halfAngle s a)/(s : ℝ) := by
  have hb1 := halfAngle_bounds ha hat
  have hb2 := halfAngle_bounds ha (hat.trans_le hts)
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hang : halfAngle s a ≤ halfAngle t a := by
    exact div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le haR.le) htR (Nat.cast_le.mpr hts)
  have hb := angle_cot_antitone hb2 hb1 hang
  dsimp only at hb
  have he (r : ℕ) : halfAngle r a*Real.cot (halfAngle r a) =
      (Real.pi*(a : ℝ))*(Real.cot (halfAngle r a)/(r : ℝ)) := by unfold halfAngle; ring
  rw [he, he] at hb
  exact (mul_le_mul_iff_right₀ (mul_pos Real.pi_pos haR)).mp hb

theorem weight_modulus_monotone (cot : Bool) {a t s : ℕ}
    (ha : 0 < a) (hat : 2*a < t) (hts : t ≤ s) :
    trigonometricWeight cot t a ≤ trigonometricWeight cot s a := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hb1 := halfAngle_bounds ha hat
  have hb2 := halfAngle_bounds ha (hat.trans_le hts)
  have hang : halfAngle s a ≤ halfAngle t a :=
    div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg a)) htR (Nat.cast_le.mpr hts)
  cases cot
  · unfold trigonometricWeight
    simp only [Bool.false_eq_true, ite_false]
    apply inv_anti₀ (Real.sin_pos_of_pos_of_lt_pi hb2.1 (by linarith [Real.pi_pos]))
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hb1.2.le hang
  · unfold trigonometricWeight
    simp only [ite_true]
    have hsmall : Real.cot (halfAngle t a)/(t : ℝ) ≤ Real.cot (halfAngle s a)/(t : ℝ) := by
      have hc := InverseChordMonotonicity.cot_ratio_antitone
        ((a : ℝ)/(s : ℝ)) ((a : ℝ)/(t : ℝ))
        (div_pos (by exact_mod_cast ha) hsR)
        ((div_lt_one htR).mpr (by exact_mod_cast (show a < t by omega)))
        (div_le_div_of_nonneg_left (Nat.cast_nonneg a) htR (Nat.cast_le.mpr hts))
      simpa only [halfAngle, mul_div_assoc, Real.cot_eq_cos_div_sin] using
        div_le_div_of_nonneg_right hc htR.le
    exact (div_le_div_iff_of_pos_right htR).mp hsmall

def bandAmplitude (cot : Bool) (t u v j : ℕ) : ℝ :=
  (if cot then 2 else 1)/(t : ℝ)^2*
    Real.cot (halfAngle t u)*Real.cot (halfAngle t v)*trigonometricWeight cot t j

theorem bandAmplitude_nonneg (cot : Bool) {t u v j : ℕ}
    (hu : 0 < u) (hut : 2*u < t) (hv : 0 < v) (hvt : 2*v < t)
    (hj : 0 < j) (hjt : 2*j < t) : 0 ≤ bandAmplitude cot t u v j := by
  have hu0 := trigonometricWeight_nonneg true hu hut
  have hv0 := trigonometricWeight_nonneg true hv hvt
  have hj0 := trigonometricWeight_nonneg cot hj hjt
  simp only [trigonometricWeight, ite_true] at hu0 hv0
  unfold bandAmplitude
  have hcoef : (0 : ℝ) ≤ if cot then 2 else 1 := by split_ifs <;> norm_num
  positivity

/-- Title: `Every absolute amplitude increases throughout the permitted conductor interval`. -/
theorem bandAmplitude_monotone (cot : Bool) {t s u v j : ℕ} (hts : t ≤ s)
    (hu : 0 < u) (hut : 2*u < t) (hv : 0 < v) (hvt : 2*v < t)
    (hj : 0 < j) (hjt : 2*j < t) :
    bandAmplitude cot t u v j ≤ bandAmplitude cot s u v j := by
  have hu0 := trigonometricWeight_nonneg true hu hut
  have hv0 := trigonometricWeight_nonneg true hv hvt
  have hs0 := trigonometricWeight_nonneg true hu (hut.trans_le hts)
  have hj0 := trigonometricWeight_nonneg cot hj hjt
  simp only [trigonometricWeight, ite_true] at hu0 hv0 hs0
  have hcoef : (0 : ℝ) ≤ if cot then 2 else 1 := by split_ifs <;> norm_num
  have he (r : ℕ) : bandAmplitude cot r u v j = (if cot then 2 else 1)*
      ((Real.cot (halfAngle r u)/(r : ℝ))*(Real.cot (halfAngle r v)/(r : ℝ))*
        trigonometricWeight cot r j) := by unfold bandAmplitude; ring
  rw [he, he]
  apply mul_le_mul_of_nonneg_left _ hcoef
  apply mul_le_mul
  · exact mul_le_mul (scaled_cotangent_monotone hu hut hts) (scaled_cotangent_monotone hv hvt hts)
      (by positivity) (by positivity)
  · exact weight_modulus_monotone cot hj hjt hts
  · exact hj0
  · have hvS := trigonometricWeight_nonneg true hv (hvt.trans_le hts)
    simp only [trigonometricWeight, ite_true] at hvS
    positivity

/-- Title: `Each conductor amplitude has the printed reciprocal-frequency size`. -/
theorem bandAmplitude_bound (cot : Bool) {t u v j : ℕ}
    (hu : 0 < u) (hut : 2*u < t) (hv : 0 < v) (hvt : 2*v < t)
    (hj : 0 < j) (hjt : 2*j < t) :
    bandAmplitude cot t u v j ≤ (t : ℝ)/(4*(u : ℝ)*(v : ℝ)*(j : ℝ)) := by
  have hu0 := trigonometricWeight_nonneg true hu hut
  have hv0 := trigonometricWeight_nonneg true hv hvt
  have hj0 := trigonometricWeight_nonneg cot hj hjt
  have hub := trigonometricWeight_le true hu hut
  have hvb := trigonometricWeight_le true hv hvt
  have hjb := trigonometricWeight_le cot hj hjt
  simp only [trigonometricWeight, ite_true] at hu0 hv0 hub hvb
  have hcoef : (if cot then 2 else 1 : ℝ) ≤ 2 := by split_ifs <;> norm_num
  unfold bandAmplitude
  calc
    _ ≤ (2/(t : ℝ)^2)*((t : ℝ)/(2*u))*((t : ℝ)/(2*v))*((t : ℝ)/(2*j)) := by
      gcongr
    _ = _ := by
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
      field_simp
      ring

end NField.Alignment.CommonResetAmplitude
