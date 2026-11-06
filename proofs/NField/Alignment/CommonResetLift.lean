/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetKernel

/-! # Complete harmonic lifts of the exact-order source -/

noncomputable section

namespace NField.Alignment.CommonResetLift

open scoped BigOperators
open CommonResetConductor CommonResetKernel CommonResetDedekind
open CommonResetSampling DedekindInverseResidueTransform DedekindReciprocity

theorem conductorKernel_congr {t h k : ℕ} (ht : 0 < t) (hmod : h%t = k%t) :
    conductorKernel t h = conductorKernel t k := by
  by_cases ht1 : t = 1
  · subst t
    simp [conductorKernel_one]
  · letI : NeZero t := ⟨ht.ne'⟩
    rw [conductorKernel_eq_units (by omega), conductorKernel_eq_units (by omega)]
    congr 1
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hmod

theorem conductorKernel_zero {t : ℕ} (ht : 0 < t) : conductorKernel t 0 = 0 := by
  unfold conductorKernel
  simp [CommonResetFourier.cotangentTerm]

theorem inverseDedekindTerm_eq {q k : ℕ} (hk : 0 < k) (hq : q.Coprime k) (j : ℕ) :
    inverseDedekindTerm q j k = arithmeticDedekindSum (inverseResidue q k*j) k := by
  unfold inverseDedekindTerm inverseResidue
  rw [dif_pos hq, dif_neg hk.ne', dif_pos hq]

theorem inverse_conductor_inversion {q k : ℕ} (hk : 0 < k) (hq : q.Coprime k) (j : ℕ) :
    (k : ℝ)*(inverseDedekindTerm q j k : ℝ) =
      ∑ d ∈ k.divisors, conductorKernel d (inverseResidue q d*j) := by
  rw [inverseDedekindTerm_eq hk hq, conductor_inversion hk]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  apply conductorKernel_congr hdpos
  have he := inverseResidue_mod_of_dvd hdpos hk (Nat.dvd_of_mem_divisors hd) hq
  have hi := inverseResidue_lt hdpos (hq.of_dvd_right (Nat.dvd_of_mem_divisors hd))
  rw [Nat.mul_mod, he]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt hi]

theorem inverse_kernel_period {q t : ℕ} (ht : 0 < t) (a : ℕ) :
    conductorKernel t (inverseResidue q t*(a+t)) = conductorKernel t (inverseResidue q t*a) := by
  apply conductorKernel_congr ht
  simp [Nat.mul_add, Nat.add_mod, Nat.mul_mod]

theorem inverse_kernel_period_zero {q t : ℕ} (ht : 0 < t) (hq : q.Coprime t) :
    (∑ a ∈ Finset.range t, conductorKernel t (inverseResidue q t*a)) = 0 := by
  by_cases ht1 : t = 1
  · subst t
    simp [conductorKernel_one]
  · letI : NeZero t := ⟨ht.ne'⟩
    let u : (ZMod t)ˣ := (ZMod.unitOfCoprime q hq)⁻¹
    rw [← CommonResetGrid.sum_residue_values]
    have he (a : ZMod t) : conductorKernel t (inverseResidue q t*a.val) = unitKernel (u.val*a) := by
      rw [conductorKernel_eq_units (by omega), Nat.cast_mul, ZMod.natCast_zmod_val]
      congr 1
      unfold inverseResidue
      rw [dif_neg ht.ne', dif_pos hq, ZMod.natCast_zmod_val]
    simp only [he]
    have hp := Equiv.sum_comp u.mulLeft unitKernel
    simpa only [Units.mulLeft_apply, unitKernel_sum_zero (by omega : 2 ≤ t)] using hp

theorem sum_real_periodic_blocks (f : ℕ → ℝ) {k : ℕ}
    (hperiod : ∀ r, f (r+k) = f r) (M s : ℕ) :
    (∑ r ∈ Finset.range (M*k+s), f r) =
      (M : ℝ)*(∑ r ∈ Finset.range k, f r) + ∑ r ∈ Finset.range s, f r := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.succ_mul, show M*k+k+s=k+(M*k+s) by omega, Finset.sum_range_add]
    have htail : (∑ x ∈ Finset.range (M*k+s), f (k+x)) =
        ∑ x ∈ Finset.range (M*k+s), f x := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Nat.add_comm] using hperiod x
    rw [htail, ih]
    push_cast
    ring

/-- Title: `Complete numerator periods cancel before the terminal prefix is retained`. -/
theorem inverse_kernel_prefix {q t : ℕ} (ht : 0 < t) (hq : q.Coprime t) (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, conductorKernel t (inverseResidue q t*a)) =
      ∑ a ∈ Finset.Icc 1 (N%t), conductorKernel t (inverseResidue q t*a) := by
  let f := fun a => conductorKernel t (inverseResidue q t*a)
  have hzero : f 0 = 0 := by simp only [f, Nat.mul_zero, conductorKernel_zero ht]
  have hperiod : ∀ a, f (a+t) = f a := inverse_kernel_period ht
  have hblock := inverse_kernel_period_zero ht hq
  have hs := sum_real_periodic_blocks (k := t) (fun a => f (a+1))
    (fun a => by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperiod (a+1))
    (N/t) (N%t)
  have shift (n : ℕ) : (∑ a ∈ Finset.range n, f (a+1)) = ∑ a ∈ Finset.Icc 1 n, f a := by
    have hset : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by ext a; simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm]
  have hb : (∑ a ∈ Finset.range t, f (a+1)) = 0 := by
    have htel := Finset.sum_range_succ' f t
    rw [Finset.sum_range_succ, hzero, add_zero] at htel
    have htzero : f t = 0 := by simpa only [zero_add, hzero] using hperiod 0
    rw [htzero, add_zero] at htel
    exact htel.symm.trans hblock
  rw [show N/t*t+N%t=N by simpa only [Nat.mul_comm] using Nat.div_add_mod N t,
    hb, mul_zero, zero_add, shift, shift] at hs
  exact hs

theorem weighted_divisor_columns (N : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (1/(k : ℝ))*∑ d ∈ k.divisors, f d) =
      ∑ d ∈ Finset.Icc 1 N, (harmonic (N/d) : ℝ)/(d : ℝ)*f d := by
  classical
  have hset (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
      k.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ k) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    have hkd := Finset.mem_Icc.mp hk
    constructor
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hkd.1,
        (Nat.le_of_dvd hkd.1 h.1).trans hkd.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, by omega⟩
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        if d ∣ k then (1/(k : ℝ))*f d else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hset k hk, Finset.mul_sum, Finset.sum_filter]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        if d ∣ k then (1/(k : ℝ))*f d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := (Finset.mem_Icc.mp hd).1
      rw [sum_Icc_divisible_reindex _ hdpos]
      have hpoint (k : ℕ) : (1/((d*k : ℕ) : ℝ))*f d =
          ((k : ℝ)⁻¹)*((d : ℝ)⁻¹*f d) := by push_cast; simp [mul_inv_rev, mul_assoc, mul_comm]
      simp only [hpoint, ← Finset.sum_mul]
      have hH : (∑ k ∈ Finset.Icc 1 (N/d), (k : ℝ)⁻¹) = (harmonic (N/d) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
      rw [hH]
      ring

/-- Title: `Every original modulus contributes its full harmonic lift weight`. -/
theorem full_lift_weight (N q : ℕ) (hq : ∀ k ∈ Finset.Icc 1 N, q.Coprime k) :
    interiorSource N q = 2*∑ t ∈ Finset.Icc 2 N,
      (harmonic (N/t) : ℝ)/(t : ℝ)*
        ∑ a ∈ Finset.Icc 1 (N%t), conductorKernel t (inverseResidue q t*a) := by
  rw [dedekind_representation N q hq]
  congr 1
  have he (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
      (∑ j ∈ Finset.Icc 1 N, (inverseDedekindTerm q j k : ℝ)) =
        (1/(k : ℝ))*∑ t ∈ k.divisors, ∑ j ∈ Finset.Icc 1 N,
          conductorKernel t (inverseResidue q t*j) := by
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← inverse_conductor_inversion hkpos (hq k hk)]
    field_simp
  rw [Finset.sum_congr rfl he, weighted_divisor_columns]
  have hprefix : (∑ t ∈ Finset.Icc 1 N, (harmonic (N/t) : ℝ)/(t : ℝ)*
      ∑ j ∈ Finset.Icc 1 N, conductorKernel t (inverseResidue q t*j)) =
      ∑ t ∈ Finset.Icc 1 N, (harmonic (N/t) : ℝ)/(t : ℝ)*
        ∑ j ∈ Finset.Icc 1 (N%t), conductorKernel t (inverseResidue q t*j) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [inverse_kernel_prefix (Finset.mem_Icc.mp ht).1 (hq t ht)]
  rw [hprefix]
  symm
  apply sum_Icc_remove_one
  simp [conductorKernel_one]

end NField.Alignment.CommonResetLift
