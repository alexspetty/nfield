/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReciprocalBudget
import NField.Alignment.ProfiniteRemainderMeasure
import NField.Alignment.CollisionJordanVariance
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.GaussSum

/-!
# Primitive additive sums and their divisor identity

The primitive sum is defined from the actual additive exponentials.
Reduction of finite rational addresses yields its divisor identity;
Mobius inversion then identifies its real arithmetic formula.
-/

noncomputable section

namespace NField.Alignment.CollisionRamanujan

open scoped BigOperators
open CollisionReciprocalBudget ProfiniteRemainderMeasure

def phase (q : ℕ) (h : ℤ) (a : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (a : ℂ) / (q : ℂ))

def primitiveSum (q : ℕ) (h : ℤ) : ℂ :=
  (if q = 1 then 1 else 0) +
    ∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q), phase q h a

def ramanujan (q : ℕ) (h : ℤ) : ℝ :=
  ∑ d ∈ q.divisors, if (d : ℤ) ∣ h then
    (d : ℝ) * (ArithmeticFunction.moebius (q/d) : ℝ) else 0

theorem phase_std {q : ℕ} (hq : 0 < q) (h : ℤ) (a : ℕ) :
    letI : NeZero q := ⟨hq.ne'⟩
    phase q h a = ZMod.stdAddChar ((h : ZMod q) * (a : ZMod q)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hc : (h : ZMod q)*(a : ZMod q) = ((h*(a : ℤ) : ℤ) : ZMod q) := by push_cast; rfl
  rw [hc, ZMod.stdAddChar_coe]
  unfold phase
  push_cast
  congr 1
  ring

theorem sum_zmod_val_complex (n : ℕ) [NeZero n] (F : ℕ → ℂ) :
    (∑ j : ZMod n, F j.val) = ∑ j ∈ Finset.range n, F j := by
  have h := Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun j => F j.val)
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, val_finEquiv] at h
  exact h.symm.trans (Fin.sum_univ_eq_sum_range F n)

theorem full_phase_sum {n : ℕ} (hn : 0 < n) (h : ℤ) :
    (∑ a ∈ Finset.range n, phase n h a) = if (n : ℤ) ∣ h then (n : ℂ) else 0 := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  rw [← sum_zmod_val_complex]
  simp_rw [phase_std hn, ZMod.natCast_zmod_val]
  have he : (∑ j : ZMod n, ZMod.stdAddChar ((h : ZMod n) * j)) =
      if (h : ZMod n) = 0 then (n : ℂ) else 0 := by
    by_cases hz : (h : ZMod n) = 0
    · simp [hz, ZMod.card]
    · rw [if_neg hz]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n hz)
  rw [he]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem primitive_address_phase_sum {n : ℕ} (hn : 0 < n) (h : ℤ) :
    (∑ a ∈ Finset.Ico 1 n, phase n h a) =
      ∑ p ∈ primitiveAddresses n, phase p.1 h p.2 := by
  apply Finset.sum_bij (fun a _ => reducedAddress n a)
  · intro a ha; exact reducedAddress_mem ha
  · intro a ha b hb he
    have hr := congrArg (fun p : Σ _ : ℕ, ℕ => (n/p.1)*p.2) he
    simpa only [reducedAddress_restore ha, reducedAddress_restore hb] using hr
  · intro p hp
    exact ⟨(n/p.1)*p.2, (primitiveAddress_restore p hp).1, (primitiveAddress_restore p hp).2⟩
  · intro a ha
    have hap := (Finset.mem_Ico.mp ha).1
    have hg := Nat.gcd_pos_of_pos_left n hap
    have hgC : (a.gcd n : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [reducedAddress, phase]
    congr 1
    rw [Nat.cast_div (Nat.gcd_dvd_left a n) hgC,
      Nat.cast_div (Nat.gcd_dvd_right a n) hgC]
    field_simp

theorem primitiveSum_divisors {n : ℕ} (hn : 0 < n) (h : ℤ) :
    (∑ q ∈ n.divisors, primitiveSum q h) = if (n : ℤ) ∣ h then (n : ℂ) else 0 := by
  classical
  have hI : (Finset.range n).erase 0 = Finset.Ico 1 n := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hzero : phase n h 0 = 1 := by simp [phase]
  have hsum := Finset.sum_erase_add (Finset.range n) (phase n h)
    (show 0 ∈ Finset.range n from Finset.mem_range.mpr hn)
  rw [hI, hzero] at hsum
  calc
    _ = 1 + ∑ p ∈ primitiveAddresses n, phase p.1 h p.2 := by
      simp only [primitiveSum, Finset.sum_add_distrib, primitiveAddresses, Finset.sum_sigma]
      rw [Finset.sum_ite_eq']
      simp [Nat.one_mem_divisors.mpr hn.ne']
    _ = ∑ a ∈ Finset.range n, phase n h a := by
      rw [← primitive_address_phase_sum hn h, add_comm]
      exact hsum
    _ = _ := full_phase_sum hn h

theorem primitiveSum_eq_ramanujan (q : ℕ) (h : ℤ) : primitiveSum q h = (ramanujan q h : ℂ) := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [primitiveSum, ramanujan]
  have hb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℂ) (f := fun n => primitiveSum n h)
    (g := fun n => if (n : ℤ) ∣ h then (n : ℂ) else 0)).mp
      (fun n hn => primitiveSum_divisors hn h) q (Nat.pos_of_ne_zero hq)
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y => (ArithmeticFunction.moebius x : ℂ) *
      (if (y : ℤ) ∣ h then (y : ℂ) else 0))] at hb
  rw [← hb]
  unfold ramanujan
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp [mul_comm]

theorem ramanujan_divisors {n : ℕ} (hn : 0 < n) (h : ℤ) :
    (∑ q ∈ n.divisors, ramanujan q h) = if (n : ℤ) ∣ h then (n : ℝ) else 0 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← primitiveSum_eq_ramanujan]
  have hb := primitiveSum_divisors hn h
  split_ifs at hb ⊢ <;> simpa using hb

@[simp] theorem ramanujan_one (h : ℤ) : ramanujan 1 h = 1 := by
  simp [ramanujan]

theorem phase_norm (q : ℕ) (h : ℤ) (a : ℕ) : ‖phase q h a‖ = 1 := by
  unfold phase
  have he : 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (a : ℂ) / (q : ℂ) =
      ((2 * Real.pi * (h : ℝ) * (a : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.norm_exp_ofReal_mul_I]

theorem primitiveSum_eq_units {q : ℕ} (hq : 2 ≤ q) (h : ℤ) :
    letI : NeZero q := ⟨by omega⟩
    primitiveSum q h = ∑ u : (ZMod q)ˣ,
      ZMod.stdAddChar ((h : ZMod q) * (u : ZMod q)) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  unfold primitiveSum
  rw [if_neg (by omega : q ≠ 1), zero_add]
  symm
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    have hc := ZMod.val_coe_unit_coprime u
    have hz : (u : ZMod q).val ≠ 0 := by
      intro hz
      rw [hz, Nat.coprime_zero_left] at hc
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, ZMod.val_lt _⟩, hc⟩
  · intro u _ v _ he
    apply Units.ext
    exact ZMod.val_injective q he
  · intro a ha
    obtain ⟨ha, hc⟩ := Finset.mem_filter.mp ha
    refine ⟨ZMod.unitOfCoprime a hc, Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_Ico.mp ha).2]
  · intro u _
    rw [phase_std (by omega), ZMod.natCast_zmod_val]

theorem primitiveSum_norm_le (q : ℕ) (h : ℤ) : ‖primitiveSum q h‖ ≤ (q : ℝ) := by
  by_cases hq : q = 1
  · simp [primitiveSum, hq]
  unfold primitiveSum
  rw [if_neg hq, zero_add]
  calc
    _ ≤ ∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q), ‖phase q h a‖ := norm_sum_le _ _
    _ = (((Finset.Ico 1 q).filter (fun a => a.Coprime q)).card : ℝ) := by simp [phase_norm]
    _ ≤ ((Finset.Ico 1 q).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ ≤ (q : ℝ) := by simp only [Nat.card_Ico]; exact_mod_cast Nat.sub_le q 1

theorem ramanujan_norm_le (q : ℕ) (h : ℤ) : ‖ramanujan q h‖ ≤ (q : ℝ) := by
  have he := primitiveSum_norm_le q h
  rw [primitiveSum_eq_ramanujan, Complex.norm_real] at he
  exact he

theorem reciprocal_square_product {n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.Icc 2 n, (1 - ((j : ℝ)^2)⁻¹)) = ((n : ℝ)+1)/(2*(n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hnp : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    push_cast
    field_simp
    ring

theorem jordanTwo_quadratic_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ)^2 / 2 ≤ CollisionJordanVariance.jordanTwo n := by
  have hp : n.primeFactors ⊆ Finset.Icc 2 n := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)⟩
  have hprod : (∏ j ∈ Finset.Icc 2 n, (1 - ((j : ℝ)^2)⁻¹)) ≤
      ∏ p ∈ n.primeFactors, (1 - ((p : ℝ)^2)⁻¹) := by
    apply Finset.prod_le_prod_of_subset_of_le_one hp
    · intro j hj
      have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      have hs : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
      linarith [inv_le_one_of_one_le₀ hs]
    · intro j _ _
      have : 0 ≤ ((j : ℝ)^2)⁻¹ := by positivity
      linarith
  rw [reciprocal_square_product hn] at hprod
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : (1/2 : ℝ) ≤ ((n : ℝ)+1)/(2*(n : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  rw [CollisionJordanVariance.jordanTwo_euler_product (by omega)]
  calc
    _ = (n : ℝ)^2 * (1/2 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hhalf.trans hprod) (sq_nonneg _)

theorem jordanTwo_linear_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ≤ CollisionJordanVariance.jordanTwo n := by
  have h := jordanTwo_quadratic_lower (by omega : 1 ≤ n)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

end NField.Alignment.CollisionRamanujan
