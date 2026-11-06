/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandGeometry

/-! # Reducing the completed reciprocal estimate to the printed band scale -/

noncomputable section

namespace NField.Alignment.CommonResetBandScale

open Set CommonResetBandParameters CommonResetBandGeometry CommonResetCompletedDerivative
open CommonResetReciprocalGeometry

def bandPhaseScale (p m u v j : ℕ) : ℝ :=
  Real.sqrt (p : ℝ)*Real.sqrt ((j : ℝ)*v)/Real.sqrt (m : ℝ) +
    Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v)) +
    Real.sqrt (u : ℝ)*Real.log (2*(u : ℝ))

theorem bandPhaseScale_nonneg (p m u v j : ℕ) (hu : 0 < u) :
    0 ≤ bandPhaseScale p m u v j := by
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hl : 0 ≤ Real.log (2*(u : ℝ)) := Real.log_nonneg (by linarith)
  unfold bandPhaseScale
  positivity

theorem root_curvature_upper {p m A y : ℝ} (hp : 0 < p) (hm : 0 < m) (hA : 0 < A)
    (hy : y ≤ 24*m^3*A/p) :
    Real.sqrt y ≤ 5*m*Real.sqrt m*Real.sqrt A/Real.sqrt p := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have he : (5*m*Real.sqrt m*Real.sqrt A/Real.sqrt p)^2 = 25*m^3*A/p := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hm.le, Real.sq_sqrt hA.le,
      Real.sq_sqrt hp.le]
    ring
  rw [he]
  exact hy.trans (div_le_div_of_nonneg_right (by nlinarith [mul_pos (pow_pos hm 3) hA]) hp.le)

theorem root_curvature_inverse {p m A y : ℝ} (hp : 0 < p) (hm : 0 < m) (hA : 0 < A)
    (hy : m^3*A/(8*p) ≤ y) :
    1/Real.sqrt y ≤ 3*Real.sqrt p/(m*Real.sqrt m*Real.sqrt A) := by
  have hypos : 0 < y := (by positivity : 0 < m^3*A/(8*p)).trans_le hy
  have hlo : m*Real.sqrt m*Real.sqrt A/(3*Real.sqrt p) ≤ Real.sqrt y := by
    apply Real.le_sqrt_of_sq_le
    have he : (m*Real.sqrt m*Real.sqrt A/(3*Real.sqrt p))^2 = m^3*A/(9*p) := by
      rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hm.le, Real.sq_sqrt hA.le,
        Real.sq_sqrt hp.le]
      ring
    rw [he]
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)).trans hy
  calc
    _ ≤ 1/(m*Real.sqrt m*Real.sqrt A/(3*Real.sqrt p)) :=
      one_div_le_one_div_of_le (by positivity) hlo
    _ = _ := by field_simp

/-- Title: `The completed derivative scale reduces to the three stated quotient-band terms`. -/
theorem completed_band_scale {p m u v j N : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (η : ℤ) (hη : η=0 ∨ η=1 ∨ η=-1)
    (hL : (N : ℝ)+1 ≤ 2*(p : ℝ)/(m : ℝ)^2) :
    completedDerivativeScale u N (reciprocalCoefficient p u v j η/(4*(bandLeft p m)^3)) ≤
      10*bandPhaseScale p m u v j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hA : 0 < (j : ℝ)*v := mul_pos hjR hvR
  have hc := band_curvature_scale hp hm hu hup hv hj η hη
  let y := (u : ℝ)*(reciprocalCoefficient p u v j η/(4*(bandLeft p m)^3))
  have hupper : Real.sqrt y ≤ 5*(m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v)/Real.sqrt (p : ℝ) := by
    apply root_curvature_upper hpR hmR hA
    dsimp only [y]
    convert hc.2 using 1 <;> ring
  have hinv : 1/Real.sqrt y ≤ 3*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v)) := by
    apply root_curvature_inverse hpR hmR hA
    dsimp only [y]
    convert hc.1 using 1 <;> ring
  have hfirst : ((N : ℝ)+1)*Real.sqrt y ≤
      10*Real.sqrt (p : ℝ)*Real.sqrt ((j : ℝ)*v)/Real.sqrt (m : ℝ) := by
    calc
      _ ≤ (2*(p : ℝ)/(m : ℝ)^2)*
          (5*(m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v)/Real.sqrt (p : ℝ)) :=
        mul_le_mul hL hupper (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by
        have hsp := Real.sq_sqrt hpR.le
        have hsm := Real.sq_sqrt hmR.le
        have hsp0 := (Real.sqrt_pos.mpr hpR).ne'
        have hsm0 := (Real.sqrt_pos.mpr hmR).ne'
        field_simp
        nlinarith
  have hlog : 0 ≤ Real.sqrt (u : ℝ)*Real.log (2*(u : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
  have hmiddle : 0 ≤ Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v)) := by positivity
  have hfirst' : ((N : ℝ)+1)*Real.sqrt y ≤
      10*(Real.sqrt (p : ℝ)*Real.sqrt ((j : ℝ)*v)/Real.sqrt (m : ℝ)) := by
    convert hfirst using 1 <;> ring
  have hinv' : 1/Real.sqrt y ≤
      3*(Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v))) := by
    convert hinv using 1 <;> ring
  change ((N : ℝ)+1)*Real.sqrt y+1/Real.sqrt y+_ ≤ _
  unfold bandPhaseScale
  linarith

/-- Title: `The literal reciprocal band phase obeys the printed three-term estimate on every subinterval`. -/
theorem reciprocal_band_bound {p m u v j : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hmsq : m^2 ≤ p) (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (η : ℤ) (hη : η=0 ∨ η=1 ∨ η=-1)
    [NeZero u] (n : ZMod u) (a : ℤ) (N : ℕ)
    (hsub : Icc (a : ℝ) (a+N) ⊆ Icc (bandLeft p m) (bandRight p m)) :
    ‖reciprocalInterval n a N (fun t : ℝ => reciprocalCoefficient p u v j η/t)‖ ≤
      129600*(u.divisors.card : ℝ)*Real.sqrt (n.val.gcd u : ℝ)*bandPhaseScale p m u v j := by
  have hb : 0 < reciprocalCoefficient p u v j η :=
    (by positivity : 0 < (p : ℝ)^2*j*v/(2*u)).trans
      (reciprocal_coefficient_bounds hp hu hup hv hj η hη).1
  have hbound := reciprocal_box_completion n a N (band_left_pos hp hm) hb
    (band_interval_dyadic hm a N hsub)
  have hs := completed_band_scale hp hm hu hup hv hj η hη (band_interval_length hm hmsq a N hsub)
  calc
    _ ≤ 12960*(u.divisors.card : ℝ)*Real.sqrt (n.val.gcd u : ℝ)*
        completedDerivativeScale u N (reciprocalCoefficient p u v j η/(4*(bandLeft p m)^3)) := hbound
    _ ≤ 12960*(u.divisors.card : ℝ)*Real.sqrt (n.val.gcd u : ℝ)*(10*bandPhaseScale p m u v j) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end NField.Alignment.CommonResetBandScale
