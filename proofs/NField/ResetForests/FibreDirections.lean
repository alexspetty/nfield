/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreInjective
/-! # Counting Gram and exact readings at a reset address

The negative pairing between distinct directions is retained. The root
reading is the literal midpoint field at the returned rational address.
-/

noncomputable section

namespace NField.ResetForests.FibreReconstruction

open scoped BigOperators
open NField.Alignment CommonResetGram

def resetDirection (p : ℕ) (v i : Fin p) : ℝ :=
  (if i=v then 1 else 0)-1/(p : ℝ)

theorem reset_direction_zero_sum {p : ℕ} (hp : 0 < p) (v : Fin p) :
    (∑ i : Fin p, resetDirection p v i)=0 := by
  simp only [resetDirection, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  norm_num

theorem reset_direction_pairing {p : ℕ} (hp : 0 < p) (v b : Fin p) :
    (∑ i : Fin p, resetDirection p v i*resetDirection p b i)=
      (if v=b then 1 else 0)-1/(p : ℝ) := by
  have hpoint (i : Fin p) : resetDirection p v i*resetDirection p b i=
      (if i=v ∧ i=b then (1 : ℝ) else 0)-
        (if i=v then 1/(p : ℝ) else 0)-(if i=b then 1/(p : ℝ) else 0)+1/(p : ℝ)^2 := by
    unfold resetDirection
    split_ifs <;> first | tauto | ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  by_cases hvb : v=b
  · simp [hvb]
    field_simp
    ring
  · have hnot : ∀ i : Fin p, ¬(i=v ∧ i=b) := by
      rintro i ⟨hi, hb⟩
      exact hvb (hi.symm.trans hb)
    simp only [hnot, if_false, Finset.sum_const_zero, zero_sub, hvb,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
    ring

theorem reset_direction_square_work {p : ℕ} (hp : 0 < p) (v : Fin p) :
    (∑ i : Fin p, (resetDirection p v i)^2)=1-1/(p : ℝ) := by
  simpa [pow_two] using reset_direction_pairing hp v v

theorem reset_fibre_divisibility {p k : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (a : ℕ) (v : Fin p)
    (hv : (v.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹) :
    p ∣ v.val*k+a := by
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  have hkI := Finset.mem_Icc.mp hk
  have hcop : k.Coprime p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hkI.1 (by have := hp.two_le; omega))).symm
  have hunit := (ZMod.isUnit_iff_coprime k p).mpr hcop
  push_cast
  rw [hv]
  calc
    _ = -(a : ZMod p)*((k : ZMod p)⁻¹*(k : ZMod p))+(a : ZMod p) := by ring
    _ = 0 := by rw [ZMod.inv_mul_of_unit _ hunit]; ring

theorem fibre_root_reading {p k a : ℕ} (hp : 0 < p) (hk : 0 < k) (v : Fin p)
    (hdiv : p ∣ v.val*k+a) (c : ℕ → ℝ) :
    fibrePath p c ((a : ℝ)/(k : ℝ)) v+
        weightedProfile (p-1) c ((a : ℝ)/(k : ℝ))/(p : ℝ)=
      weightedProfile (p-1) c ((((v.val*k+a)/p : ℕ) : ℝ)/(k : ℝ)) := by
  unfold fibrePath
  rw [sub_add_cancel]
  congr 1
  have he : (((v.val*k+a)/p : ℕ) : ℝ)*(p : ℝ)=
      (v.val : ℝ)*(k : ℝ)+(a : ℝ) := by exact_mod_cast Nat.div_mul_cancel hdiv
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  nlinarith

theorem returned_root_congruence {p k a : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (v : Fin p) (hdiv : p ∣ v.val*k+a) :
    (((v.val*k+a)/p : ℕ) : ZMod k)=(a : ZMod k)*(p : ZMod k)⁻¹ := by
  have hcop := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk hkp)
  have hunit := (ZMod.isUnit_iff_coprime p k).mpr hcop
  have hn := Nat.div_mul_cancel hdiv
  have he : (((v.val*k+a)/p : ℕ) : ZMod k)*(p : ZMod k)=(a : ZMod k) := by
    have he' := congrArg (fun n : ℕ => (n : ZMod k)) hn
    simpa only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, mul_zero, zero_add] using he'
  calc
    _ = (((v.val*k+a)/p : ℕ) : ZMod k)*((p : ZMod k)*(p : ZMod k)⁻¹) := by
      rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
    _ = _ := by rw [← mul_assoc, he]

theorem returned_root_reduced_coordinates {p k a : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hkp : k < p) (ha : 0 < a) (hak : a < k)
    (v : Fin p) (hdiv : p ∣ v.val*k+a) :
    1 ≤ (v.val*k+a)/p ∧ (v.val*k+a)/p < k ∧
      (v.val*k+a)/p=((a : ZMod k)*(p : ZMod k)⁻¹).val := by
  have hpos : 1 ≤ (v.val*k+a)/p := by
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    simpa only [one_mul] using Nat.le_of_dvd (by omega : 0 < v.val*k+a) hdiv
  have hlt : (v.val*k+a)/p < k := by
    apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
    have hu := Nat.mul_le_mul_right k (Nat.succ_le_of_lt v.isLt)
    nlinarith
  have hc := congrArg ZMod.val (returned_root_congruence hp hk hkp v hdiv)
  refine ⟨hpos, hlt, ?_⟩
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] using hc

theorem fibre_root_reading_at_return {p k a : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (ha : 0 < a) (hak : a < k)
    (v : Fin p) (hv : (v.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹)
    (c : ℕ → ℝ) :
    fibrePath p c ((a : ℝ)/(k : ℝ)) v+
        weightedProfile (p-1) c ((a : ℝ)/(k : ℝ))/(p : ℝ)=
      weightedProfile (p-1) c
        ((((a : ZMod k)*(p : ZMod k)⁻¹).val : ℝ)/(k : ℝ)) := by
  have hkI := Finset.mem_Icc.mp hk
  have hkp : k < p := by have := hp.two_le; omega
  have hd := reset_fibre_divisibility hp hk a v hv
  have hr := fibre_root_reading hp.pos hkI.1 v hd c
  rw [(returned_root_reduced_coordinates hp hkI.1 hkp ha hak v hd).2.2] at hr
  exact hr

end NField.ResetForests.FibreReconstruction
