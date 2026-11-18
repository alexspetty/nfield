/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreLattice
/-! # The full jump vector at a reduced reset -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped BigOperators Topology
open NField.Alignment CommonResetGram CollisionRampEnergy FibreReconstruction

theorem fract_nat_ratio_zero_iff (a : ℕ) {k : ℕ} (hk : 0 < k) :
    Int.fract ((a : ℝ)/(k : ℝ))=0 ↔ k ∣ a := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod, div_eq_zero_iff]
  simp only [Nat.cast_eq_zero, hk.ne', or_false, Nat.dvd_iff_mod_eq_zero]

theorem rational_contact_iff {k a : ℕ} (hk : 0 < k) (ha : a.Coprime k) (j : ℕ) :
    Int.fract ((j : ℝ)*((a : ℝ)/(k : ℝ)))=0 ↔ k ∣ j := by
  rw [← mul_div_assoc, ← Nat.cast_mul, fract_nat_ratio_zero_iff _ hk]
  exact ha.symm.dvd_mul_right

theorem contact_mass_at_reduced {k a : ℕ} (hk : 0 < k) (ha : a.Coprime k)
    (N : ℕ) (c : ℕ → ℝ) :
    contactMass N c ((a : ℝ)/(k : ℝ))=Core.resetMass N c k := by
  simp only [contactMass, Core.resetMass, Core.sourceIndices, rational_contact_iff hk ha]

theorem shifted_rational_contact_iff {p k a j : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (ha : a.Coprime k)
    (hj : j ∈ Finset.Icc 1 (p-1)) (v : Fin p) :
    Int.fract ((j : ℝ)*(((v.val : ℝ)+(a : ℝ)/(k : ℝ))/(p : ℝ)))=0 ↔
      k ∣ j ∧ p ∣ v.val*k+a := by
  have hkB := Finset.mem_Icc.mp hk
  have hjB := Finset.mem_Icc.mp hj
  have hkp : k.Coprime p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hkB.1 (by have := hp.two_le; omega))).symm
  have hpj : p.Coprime j := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hjB.1 (by have := hp.two_le; omega))
  have hknum : k.Coprime (v.val*k+a) :=
    (Nat.coprime_mul_right_add_right k a v.val).mpr ha.symm
  have he : (j : ℝ)*(((v.val : ℝ)+(a : ℝ)/(k : ℝ))/(p : ℝ))=
      ((j*(v.val*k+a) : ℕ) : ℝ)/((k*p : ℕ) : ℝ) := by
    push_cast
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp
  rw [he, fract_nat_ratio_zero_iff _ (Nat.mul_pos hkB.1 hp.pos)]
  constructor
  · intro hd
    exact ⟨hknum.dvd_of_dvd_mul_right ((dvd_mul_right k p).trans hd),
      hpj.dvd_of_dvd_mul_left ((dvd_mul_left p k).trans hd)⟩
  · rintro ⟨hkj, hpn⟩
    exact hkp.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_left hkj _) (dvd_mul_of_dvd_right hpn _)

theorem reset_fibre_unique {p k a : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (v0 v : Fin p)
    (hv0 : (v0.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹) :
    p ∣ v.val*k+a ↔ v=v0 := by
  have hkB := Finset.mem_Icc.mp hk
  have hcop : k.Coprime p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hkB.1 (by have := hp.two_le; omega))).symm
  have hunit := (ZMod.isUnit_iff_coprime k p).mpr hcop
  constructor
  · intro hd
    have hz : (v.val : ZMod p)*(k : ZMod p)+(a : ZMod p)=0 := by
      simpa only [Nat.cast_add, Nat.cast_mul] using (ZMod.natCast_eq_zero_iff _ p).mpr hd
    have he : (v.val : ZMod p)=(v0.val : ZMod p) := by
      rw [hv0]
      have hm := congrArg (fun z : ZMod p => z*(k : ZMod p)⁻¹) hz
      rw [add_mul, mul_assoc, ZMod.mul_inv_of_unit _ hunit, mul_one, zero_mul] at hm
      simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hm
    apply Fin.ext
    have hval := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt v.isLt, Nat.mod_eq_of_lt v0.isLt] using hval
  · intro hv
    subst v
    exact reset_fibre_divisibility hp hk a v0 hv0

theorem shifted_contact_mass_at_reset {p k a : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (ha : a.Coprime k)
    (v0 v : Fin p) (hv0 : (v0.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹)
    (c : ℕ → ℝ) :
    contactMass (p-1) c (((v.val : ℝ)+(a : ℝ)/(k : ℝ))/(p : ℝ))=
      if v=v0 then Core.resetMass (p-1) c k else 0 := by
  unfold contactMass Core.resetMass Core.sourceIndices
  by_cases hv : v=v0
  · rw [if_pos hv]
    apply Finset.sum_congr rfl
    intro j hj
    have hd := (reset_fibre_unique hp hk v0 v hv0).mpr hv
    simp only [shifted_rational_contact_iff hp hk ha hj, hd, and_true]
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [shifted_rational_contact_iff hp hk ha hj,
      reset_fibre_unique hp hk v0 v hv0, hv, and_false, if_false]

theorem fibre_path_jump_at_reduced {p k a : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (ha : a.Coprime k)
    (v0 v : Fin p) (hv0 : (v0.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹)
    (c : ℕ → ℝ) :
    fibreRight p c ((a : ℝ)/(k : ℝ)) v-fibreLeft p c ((a : ℝ)/(k : ℝ)) v=
      -2*Core.resetMass (p-1) c k*resetDirection p v0 v := by
  rw [fibre_jump_contact_formula, shifted_contact_mass_at_reset hp hk ha v0 v hv0,
    contact_mass_at_reduced (Finset.mem_Icc.mp hk).1 ha]
  unfold resetDirection
  split_ifs <;> ring

end NField.ResetForests.FibreTraces
