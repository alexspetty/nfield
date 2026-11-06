/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetLift
import Mathlib.Data.ZMod.ValMinAbs

/-! # Actual nonzero determinants of the prime-square carrier -/

noncomputable section

namespace NField.Alignment.CommonResetDeterminants

open scoped BigOperators
open DedekindInverseResidueTransform PrimeSquareReducedRatio

def centeredCarrier (p b u t : ℕ) : ℤ :=
  ((p^2*b*inverseResidue u t : ℕ) : ZMod t).valMinAbs

theorem centeredCarrier_congruence {p b u t : ℕ} (ht : 0 < t) (hu : u.Coprime t) :
    (t : ℤ) ∣ (p : ℤ)^2*(b : ℤ)-(u : ℤ)*centeredCarrier p b u t := by
  letI : NeZero t := ⟨ht.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    centeredCarrier, ZMod.coe_valMinAbs, Nat.cast_mul, Nat.cast_pow]
  have hi : (u : ZMod t)*(inverseResidue u t : ZMod t) = 1 := by
    unfold inverseResidue
    rw [dif_neg ht.ne', dif_pos hu, ZMod.natCast_zmod_val]
    exact (ZMod.unitOfCoprime u hu).val_inv
  calc
    (p : ZMod t)^2*b-u*(p^2*b*(inverseResidue u t : ZMod t)) =
        p^2*b*(1-u*(inverseResidue u t : ZMod t)) := by ring
    _ = 0 := by rw [hi]; ring

/-- Title: `The centered prime-square determinant cannot have zero residue`. -/
theorem centeredCarrier_ne_zero {p b u t : ℕ} (hp : p.Prime)
    (ht : 0 < t) (htp : t < p) (hb : 0 < b) (hbt : b < t) (hu : u.Coprime t) :
    centeredCarrier p b u t ≠ 0 := by
  letI : NeZero t := ⟨ht.ne'⟩
  have hq : (p^2).Coprime t := (smallNatUnit_coprime hp ht htp).symm
  intro hz
  have hd := centeredCarrier_congruence (p := p) (b := b) ht hu
  rw [hz, mul_zero, sub_zero] at hd
  have hdn : t ∣ p^2*b := by exact_mod_cast hd
  have htb : t ∣ b := hq.symm.dvd_of_dvd_mul_left hdn
  exact Nat.not_dvd_of_pos_of_lt hb hbt htb

theorem centeredCarrier_bound {p b u t : ℕ} (ht : 0 < t) :
    2*|centeredCarrier p b u t| ≤ (t : ℤ) := by
  letI : NeZero t := ⟨ht.ne'⟩
  have h := (((p^2*b*inverseResidue u t : ℕ) : ZMod t)).valMinAbs_mem_Ioc
  dsimp only [centeredCarrier]
  rcases le_total (0 : ℤ) (((p^2*b*inverseResidue u t : ℕ) : ZMod t).valMinAbs) with hz|hz
  · rw [abs_of_nonneg hz]
    linarith [h.2]
  · rw [abs_of_nonpos hz]
    linarith [h.1]

/-- Title: `Every carrier determinant is positive and below twice the cube`. -/
theorem carrier_determinant_range {p b u t : ℕ} (hp : 2 ≤ p)
    (ht : 0 < t) (htp : t < p) (hb : 0 < b) (hbp : b < p) (hup : u < p) :
    0 < (p : ℤ)^2*(b : ℤ)-(u : ℤ)*centeredCarrier p b u t ∧
      (p : ℤ)^2*(b : ℤ)-(u : ℤ)*centeredCarrier p b u t < 2*(p : ℤ)^3 := by
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have htZ : (t : ℤ) < p := by exact_mod_cast htp
  have hbZ : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hbpZ : (b : ℤ) < p := by exact_mod_cast hbp
  have hupZ : (u : ℤ) < p := by exact_mod_cast hup
  have huZ : (0 : ℤ) ≤ u := by positivity
  have hz := centeredCarrier_bound (p := p) (b := b) (u := u) ht
  have hzp : |centeredCarrier p b u t| ≤ (p : ℤ) := by linarith [abs_nonneg (centeredCarrier p b u t)]
  have huz : |(u : ℤ)*centeredCarrier p b u t| < (p : ℤ)^2 := by
    rw [abs_mul, abs_of_nonneg huZ]
    calc
      _ ≤ (u : ℤ)*p := mul_le_mul_of_nonneg_left hzp huZ
      _ < (p : ℤ)*p := mul_lt_mul_of_pos_right hupZ (by omega)
      _ = _ := by ring
  have hqlo : (p : ℤ)^2 ≤ (p : ℤ)^2*(b : ℤ) := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℤ)) (sub_nonneg.mpr hbZ)]
  have hqhi : (p : ℤ)^2*(b : ℤ) < (p : ℤ)^3 := by
    have h := mul_lt_mul_of_pos_left hbpZ (show 0 < (p : ℤ)^2 by positivity)
    nlinarith
  have hpow : (p : ℤ)^2 ≤ (p : ℤ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℤ)) (show 0 ≤ (p : ℤ)-1 by omega)]
  have huabs := abs_lt.mp huz
  constructor <;> linarith

/-- Title: `Possible moduli are counted as divisors of the actual nonzero determinant`. -/
theorem carrier_moduli_count {p b u : ℕ} (z : ℤ) (S : Finset ℕ)
    (hdet : 0 < (p : ℤ)^2*(b : ℤ)-(u : ℤ)*z)
    (hS : ∀ t ∈ S, (t : ℤ) ∣ (p : ℤ)^2*(b : ℤ)-(u : ℤ)*z) :
    S.card ≤ (((p : ℤ)^2*(b : ℤ)-(u : ℤ)*z).toNat).divisors.card := by
  apply Finset.card_le_card
  intro t ht
  apply Nat.mem_divisors.mpr
  constructor
  · have hd := hS t ht
    have he : (((p : ℤ)^2*(b : ℤ)-(u : ℤ)*z).toNat : ℤ) =
        (p : ℤ)^2*(b : ℤ)-(u : ℤ)*z := Int.toNat_of_nonneg hdet.le
    rw [← he] at hd
    exact_mod_cast hd
  · omega

end NField.Alignment.CommonResetDeterminants
