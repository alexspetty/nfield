/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetReciprocalGeometry
import NField.Alignment.CommonResetInverseReciprocity
import NField.Alignment.CommonResetAmplitude

/-! # Literal quotient-band scales and all three reciprocal coefficients -/

noncomputable section

namespace NField.Alignment.CommonResetBandParameters

open scoped BigOperators
open Set

def bandLeft (p m : ℕ) : ℝ := ((p-1 : ℕ) : ℝ)/((m : ℝ)+1)

def reciprocalCoefficient (p u v j : ℕ) (η : ℤ) : ℝ :=
  (p : ℝ)^2*j*v/u + (η : ℝ)*j*((p : ℝ)-1/2)

theorem reciprocal_coefficient_bounds {p u v j : ℕ} (hp : 2 ≤ p)
    (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (η : ℤ) (hη : η=0 ∨ η=1 ∨ η=-1) :
    (p : ℝ)^2*j*v/(2*u) < reciprocalCoefficient p u v j η ∧
      reciprocalCoefficient p u v j η < 3*((p : ℝ)^2*j*v)/(2*u) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hupR : 2*(u : ℝ) < p := by exact_mod_cast hup
  have hbase : 2*(u : ℝ)*(p : ℝ)*j < (p : ℝ)^2*j*v := by
    calc
      _ = (2*(u : ℝ))*((p : ℝ)*j) := by ring
      _ < (p : ℝ)*((p : ℝ)*j) := mul_lt_mul_of_pos_right hupR (mul_pos (by linarith) hjR)
      _ = ((p : ℝ)^2*j)*1 := by ring
      _ ≤ ((p : ℝ)^2*j)*v := mul_le_mul_of_nonneg_left hvR (by positivity)
  have hhalf : (p : ℝ)*j < (p : ℝ)^2*j*v/(2*u) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hηabs : |(η : ℝ)| ≤ 1 := by rcases hη with rfl|rfl|rfl <;> norm_num
  have hpm : (0 : ℝ) ≤ (p : ℝ)-1/2 := by linarith
  have hshift : |(η : ℝ)*j*((p : ℝ)-1/2)| ≤ (p : ℝ)*j := by
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ j by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ)-1/2 by linarith)]
    calc
      _ ≤ 1*(j : ℝ)*((p : ℝ)-1/2) := by gcongr
      _ ≤ _ := by nlinarith
  have hs := abs_le.mp hshift
  have htwo : (p : ℝ)^2*j*v/u = 2*((p : ℝ)^2*j*v/(2*u)) := by ring
  have hthree : 3*((p : ℝ)^2*j*v)/(2*u) = 3*((p : ℝ)^2*j*v/(2*u)) := by ring
  unfold reciprocalCoefficient
  rw [htwo, hthree]
  constructor <;> linarith [hs.1, hs.2]

/-- Title: `The actual quotient band has the printed reciprocal scale with absolute constants`. -/
theorem band_left_bounds {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (p : ℝ)/(4*m) ≤ bandLeft p m ∧ bandLeft p m ≤ (p : ℝ)/m := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold bandLeft
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4*m) (by positivity : (0 : ℝ) < m+1)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ m by positivity) (show (0 : ℝ) ≤ (p : ℝ)-2 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ p by positivity) (show (0 : ℝ) ≤ (m : ℝ)-1 by linarith)]
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < m+1) (by positivity : (0 : ℝ) < m)).mpr
    nlinarith

theorem band_left_pos {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) : 0 < bandLeft p m :=
  (show (0 : ℝ) < (p : ℝ)/(4*m) by positivity).trans_le (band_left_bounds hp hm).1

/-- Title: `Every linked phase has the stated conductor times curvature scale`. -/
theorem band_curvature_scale {p m u v j : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (η : ℤ) (hη : η=0 ∨ η=1 ∨ η=-1) :
    (m : ℝ)^3*j*v/(8*p) ≤
        (u : ℝ)*(reciprocalCoefficient p u v j η/(4*(bandLeft p m)^3)) ∧
      (u : ℝ)*(reciprocalCoefficient p u v j η/(4*(bandLeft p m)^3)) ≤
        24*((m : ℝ)^3*j*v)/(p : ℝ) := by
  have hb := reciprocal_coefficient_bounds hp hu hup hv hj η hη
  have hX := band_left_bounds hp hm
  have hXpos := band_left_pos hp hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hublo : (p : ℝ)^2*j*v/2 ≤ (u : ℝ)*reciprocalCoefficient p u v j η := by
    have hh := (div_lt_iff₀ (show (0 : ℝ) < 2*u by positivity)).mp hb.1
    linarith
  have hubhi : (u : ℝ)*reciprocalCoefficient p u v j η ≤ 3*((p : ℝ)^2*j*v)/2 := by
    have hh := (lt_div_iff₀ (show (0 : ℝ) < 2*u by positivity)).mp hb.2
    linarith
  have hpowhi := pow_le_pow_left₀ hXpos.le hX.2 3
  have hpowlo := pow_le_pow_left₀ (show (0 : ℝ) ≤ (p : ℝ)/(4*m) by positivity) hX.1 3
  constructor
  · calc
      _ = ((p : ℝ)^2*j*v/2)/(4*((p : ℝ)/m)^3) := by field_simp; ring
      _ ≤ ((p : ℝ)^2*j*v/2)/(4*(bandLeft p m)^3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hpowhi (by norm_num))
      _ ≤ ((u : ℝ)*reciprocalCoefficient p u v j η)/(4*(bandLeft p m)^3) :=
        div_le_div_of_nonneg_right hublo (by positivity)
      _ = _ := by ring
  · calc
      _ = ((u : ℝ)*reciprocalCoefficient p u v j η)/(4*(bandLeft p m)^3) := by ring
      _ ≤ (3*((p : ℝ)^2*j*v)/2)/(4*(bandLeft p m)^3) :=
        div_le_div_of_nonneg_right hubhi (by positivity)
      _ ≤ (3*((p : ℝ)^2*j*v)/2)/(4*((p : ℝ)/(4*m))^3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hpowlo (by norm_num))
      _ = _ := by field_simp; ring

end NField.Alignment.CommonResetBandParameters
