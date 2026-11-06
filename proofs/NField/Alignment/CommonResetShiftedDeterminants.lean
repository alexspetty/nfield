/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDeterminants

/-! # The two shifted endpoint determinants -/

noncomputable section

namespace NField.Alignment.CommonResetShiftedDeterminants

open CommonResetDeterminants DedekindInverseResidueTransform

def twiceEndpointPhase (p v u t : ℕ) (η : ℤ) : ℤ :=
  2*(p^2*v*inverseResidue u t : ℕ)+η*(2*(p : ℤ)-1)

def centeredEndpointPhase (p v u t : ℕ) (η : ℤ) : ℤ :=
  (twiceEndpointPhase p v u t η : ZMod (2*t)).valMinAbs

def shiftedDeterminant (p v u : ℕ) (η y : ℤ) : ℤ :=
  2*(p : ℤ)^2*(v : ℤ)+η*(u : ℤ)*(2*(p : ℤ)-1)-(u : ℤ)*y

theorem endpoint_phase_congruence (p v u t : ℕ) (η : ℤ) :
    (2*(t : ℤ)) ∣ twiceEndpointPhase p v u t η-centeredEndpointPhase p v u t η := by
  rw [show 2*(t : ℤ) = ((2*t : ℕ) : ℤ) by push_cast; ring,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, centeredEndpointPhase, ZMod.coe_valMinAbs, sub_self]

/-- Title: `The three endpoint phases have their literal doubled-modulus determinants`. -/
theorem shifted_determinant_congruence {p v u t : ℕ} (ht : 0 < t)
    (hu : u.Coprime t) (η : ℤ) :
    2*(t : ℤ) ∣ shiftedDeterminant p v u η (centeredEndpointPhase p v u t η) := by
  have hbase : (t : ℤ) ∣ (p : ℤ)^2*(v : ℤ)-
      (u : ℤ)*(p^2*v*inverseResidue u t : ℕ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    letI : NeZero t := ⟨ht.ne'⟩
    push_cast
    have hi : (u : ZMod t)*(inverseResidue u t : ZMod t) = 1 := by
      unfold inverseResidue
      rw [dif_neg ht.ne', dif_pos hu, ZMod.natCast_zmod_val]
      exact (ZMod.unitOfCoprime u hu).val_inv
    calc
      (p : ZMod t)^2*v-u*(p^2*v*(inverseResidue u t : ZMod t)) =
          p^2*v*(1-u*(inverseResidue u t : ZMod t)) := by ring
      _ = 0 := by rw [hi]; ring
  have hfirst : 2*(t : ℤ) ∣ 2*((p : ℤ)^2*(v : ℤ)-
      (u : ℤ)*(p^2*v*inverseResidue u t : ℕ)) := mul_dvd_mul_left 2 hbase
  have hsecond := (endpoint_phase_congruence p v u t η).mul_left (u : ℤ)
  have he : shiftedDeterminant p v u η (centeredEndpointPhase p v u t η) =
      2*((p : ℤ)^2*(v : ℤ)-(u : ℤ)*(p^2*v*inverseResidue u t : ℕ))+
        (u : ℤ)*(twiceEndpointPhase p v u t η-centeredEndpointPhase p v u t η) := by
    unfold shiftedDeterminant twiceEndpointPhase
    ring
  rw [he]
  exact hfirst.add hsecond

/-- Title: `Neither unshifted nor shifted endpoint phases have zero centered residue`. -/
theorem centeredEndpointPhase_ne_zero {p v u t : ℕ} (hp : p.Prime)
    (ht : 0 < t) (htp : t < p) (hv : 0 < v) (hvt : v < t) (hu : u.Coprime t)
    (η : ℤ) (hη : η = 0 ∨ η = 1 ∨ η = -1) :
    centeredEndpointPhase p v u t η ≠ 0 := by
  intro hz
  have hd := endpoint_phase_congruence p v u t η
  rw [hz, sub_zero] at hd
  rcases hη with hη|hη|hη
  · subst η
    simp only [twiceEndpointPhase, zero_mul, add_zero] at hd
    have hdn : 2*t ∣ 2*(p^2*v*inverseResidue u t) := by exact_mod_cast hd
    have htdiv : t ∣ p^2*v*inverseResidue u t :=
      Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2) hdn
    have hc : centeredCarrier p v u t = 0 := by
      unfold centeredCarrier
      rw [ZMod.valMinAbs_eq_zero, ZMod.natCast_eq_zero_iff]
      exact htdiv
    exact centeredCarrier_ne_zero hp ht htp hv hvt hu hc
  · subst η
    have htwo : (2 : ℤ) ∣ twiceEndpointPhase p v u t 1 :=
      dvd_trans (dvd_mul_right 2 (t : ℤ)) hd
    rcases htwo with ⟨k, hk⟩
    unfold twiceEndpointPhase at hk
    omega
  · subst η
    have htwo : (2 : ℤ) ∣ twiceEndpointPhase p v u t (-1) :=
      dvd_trans (dvd_mul_right 2 (t : ℤ)) hd
    rcases htwo with ⟨k, hk⟩
    unfold twiceEndpointPhase at hk
    omega

theorem centeredEndpointPhase_bound {p v u t : ℕ} (ht : 0 < t) (η : ℤ) :
    |centeredEndpointPhase p v u t η| ≤ (t : ℤ) := by
  letI : NeZero (2*t) := ⟨by omega⟩
  have h := (twiceEndpointPhase p v u t η : ZMod (2*t)).valMinAbs_mem_Ioc
  change -(2*t : ℕ) < centeredEndpointPhase p v u t η*2 ∧
    centeredEndpointPhase p v u t η*2 ≤ (2*t : ℕ) at h
  push_cast at h
  rw [abs_le]
  constructor <;> omega

/-- Title: `All three shifted determinants lie in the same positive divisor range`. -/
theorem shifted_determinant_range {p v u t : ℕ} (hp : 2 ≤ p)
    (ht : 0 < t) (htp : t < p) (hv : 0 < v) (hvp : 2*v < p) (hup : 2*u < p)
    (η : ℤ) (hη : |η| ≤ 1) :
    0 < shiftedDeterminant p v u η (centeredEndpointPhase p v u t η) ∧
      shiftedDeterminant p v u η (centeredEndpointPhase p v u t η) < 2*(p : ℤ)^3 := by
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have htpZ : (t : ℤ) < p := by exact_mod_cast htp
  have hvZ : (1 : ℤ) ≤ v := by exact_mod_cast hv
  have hvpZ : 2*(v : ℤ) < p := by exact_mod_cast hvp
  have hupZ : 2*(u : ℤ) < p := by exact_mod_cast hup
  have huZ : (0 : ℤ) ≤ u := by positivity
  have hy := centeredEndpointPhase_bound (p := p) (v := v) (u := u) ht η
  have hshift : |η*(u : ℤ)*(2*(p : ℤ)-1)| < (p : ℤ)^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg huZ, abs_of_nonneg (by omega : 0 ≤ 2*(p : ℤ)-1)]
    calc
      _ ≤ 1*(u : ℤ)*(2*(p : ℤ)-1) := by gcongr <;> omega
      _ ≤ 2*(u : ℤ)*p := by nlinarith
      _ < (p : ℤ)^2 := by nlinarith [mul_lt_mul_of_pos_right hupZ (show 0 < (p : ℤ) by omega)]
  have huy : |(u : ℤ)*centeredEndpointPhase p v u t η| < (p : ℤ)^2 := by
    rw [abs_mul, abs_of_nonneg huZ]
    calc
      _ ≤ (u : ℤ)*t := mul_le_mul_of_nonneg_left hy huZ
      _ ≤ (u : ℤ)*p := mul_le_mul_of_nonneg_left htpZ.le huZ
      _ < (p : ℤ)^2 := by
        have hh := mul_lt_mul_of_pos_right (show (u : ℤ) < p by omega) (show 0 < (p : ℤ) by omega)
        nlinarith
  have hlo : 2*(p : ℤ)^2 ≤ 2*(p : ℤ)^2*(v : ℤ) := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℤ)) (sub_nonneg.mpr hvZ)]
  have hhi : 2*(p : ℤ)^2*(v : ℤ) < (p : ℤ)^3 := by
    nlinarith [mul_lt_mul_of_pos_left hvpZ (show 0 < (p : ℤ)^2 by positivity)]
  have hpow : 2*(p : ℤ)^2 ≤ (p : ℤ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℤ)) (show 0 ≤ (p : ℤ)-2 by omega)]
  have hs := abs_lt.mp hshift
  have hu := abs_lt.mp huy
  unfold shiftedDeterminant
  constructor <;> linarith

end NField.Alignment.CommonResetShiftedDeterminants
