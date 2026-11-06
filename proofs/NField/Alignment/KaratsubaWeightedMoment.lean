/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaScaledFourierMoment

/-! # Finite weighted character moments with actual multiplicities -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaWeightedMoment
open scoped BigOperators
open KaratsubaFourierMoment KaratsubaFiberEnergy

theorem weighted_character_orthogonality {α : Type*} [Fintype α]
    {m : ℕ} [NeZero m] (f : α → ZMod m) (w : α → ℂ) :
    (∑ t : ZMod m, (∑ x, w x * ZMod.stdAddChar (t * f x)) *
      (starRingEnd ℂ) (∑ x, w x * ZMod.stdAddChar (t * f x))) =
      (m : ℂ) * ∑ x, ∑ y, if f x = f y then w x * (starRingEnd ℂ) (w y) else 0 := by
  classical
  simp only [map_sum, Finset.sum_mul_sum]
  have hc (t : ZMod m) (x y : α) :
      (w x * ZMod.stdAddChar (t * f x)) *
        (starRingEnd ℂ) (w y * ZMod.stdAddChar (t * f y)) =
      (w x * (starRingEnd ℂ) (w y)) * ZMod.stdAddChar (t * (f x - f y)) := by
    rw [map_mul (starRingEnd ℂ), show (starRingEnd ℂ) (ZMod.stdAddChar (t * f y)) =
      ZMod.stdAddChar (-(t * f y)) from (AddChar.map_neg_eq_conj _ _).symm]
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod m))),
    ← Finset.mul_sum, character_orthogonality, sub_eq_zero]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> ring

theorem weighted_norm_moment {α : Type*} [Fintype α] {m : ℕ} [NeZero m]
    (f : α → ZMod m) (w : α → ℂ) :
    (∑ t : ZMod m, ‖∑ x, w x * ZMod.stdAddChar (t * f x)‖ ^ 2) =
      (m : ℝ) * ∑ x, ∑ y, if f x = f y then (w x * (starRingEnd ℂ) (w y)).re else 0 := by
  have h := weighted_character_orthogonality f w
  simp_rw [Complex.mul_conj] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, apply_ite, Complex.zero_re, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using hr

theorem weighted_norm_moment_le {α : Type*} [Fintype α] {m : ℕ} [NeZero m]
    (f : α → ZMod m) (w : α → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1) :
    (∑ t : ZMod m, ‖∑ x, w x * ZMod.stdAddChar (t * f x)‖ ^ 2) ≤
      (m : ℝ) * ∑ y, (fiberCount f y : ℝ) ^ 2 := by
  classical
  rw [weighted_norm_moment]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have he : ∑ y, (fiberCount f y : ℝ) ^ 2 = ∑ x, (fiberCount f (f x) : ℝ) := by
    exact_mod_cast sum_fiberCount_sq f
  rw [he]
  apply Finset.sum_le_sum
  intro x _
  simp only [fiberCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_le_sum
  intro y _
  by_cases hxy : f x = f y
  · simp only [if_pos hxy, if_pos hxy.symm]
    calc
      _ ≤ ‖w x * (starRingEnd ℂ) (w y)‖ := Complex.re_le_norm _
      _ = ‖w x‖ * ‖w y‖ := by simp
      _ ≤ 1 := by simpa using mul_le_mul (hw x) (hw y) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  · simp [hxy, Ne.symm hxy]

open KaratsubaPrimeMoment KaratsubaFrequencyKernel

def weightedPrimeSum (P : Finset ℕ) {m : ℕ} [NeZero m]
    (w : {p // p ∈ P} → ℂ) (a : ZMod m) : ℂ :=
  ∑ p, w p * ZMod.stdAddChar (a * (p.val : ZMod m)⁻¹)

theorem weighted_prime_power (P : Finset ℕ) {m : ℕ} [NeZero m]
    (w : {p // p ∈ P} → ℂ) (a t : ZMod m) (k : ℕ) :
    weightedPrimeSum P w (t*a) ^ k = ∑ u : PrimeTuple P k,
      (∏ i, w (u i)) * ZMod.stdAddChar (t * (a * reciprocalSum m (fun i => (u i).val))) := by
  rw [weightedPrimeSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.prod_mul_distrib, reciprocalSum, Finset.mul_sum, character_sum, mul_assoc]

theorem weighted_prime_norm_moment_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2*k-1) < m)
    (w : {p // p ∈ P} → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) (a : ZMod m) :
    (∑ t : ZMod m, ‖weightedPrimeSum P w (t*a)‖ ^ (2*k)) ≤
      (m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)) := by
  have hp (u : PrimeTuple P k) : ‖∏ i, w (u i)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hw (u i))
  have h := weighted_norm_moment_le
    (fun u : PrimeTuple P k => a * reciprocalSum m (fun i => (u i).val))
    (fun u => ∏ i, w (u i)) hp
  have he : (∑ y, (fiberCount (fun u : PrimeTuple P k =>
      a * reciprocalSum m (fun i => (u i).val)) y : ℝ) ^ 2) ≤
        (a.val.gcd m * (k.factorial * P.card ^ k) : ℕ) := by
    exact_mod_cast reciprocal_frequency_energy_le hX hprime hcop hlower hupper hsize a
  have hh := h.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg m))
  simp_rw [← weighted_prime_power, norm_pow, ← pow_mul] at hh
  simpa only [Nat.mul_comm k 2, Nat.cast_mul, Nat.cast_pow] using hh

def mixedPrimeSum (P : Finset ℕ) {m : ℕ} [NeZero m] (a b : ZMod m) : ℂ :=
  ∑ p : {p // p ∈ P}, ZMod.stdAddChar (a * (p.val : ZMod m)⁻¹ + b * (p.val : ZMod m))

theorem mixedPrimeSum_eq_weighted (P : Finset ℕ) {m : ℕ} [NeZero m] (a b : ZMod m) :
    mixedPrimeSum P a b = weightedPrimeSum P (fun p => ZMod.stdAddChar (b*(p.val : ZMod m))) a := by
  simp only [mixedPrimeSum, weightedPrimeSum, AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem mixed_prime_norm_moment_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2*k-1) < m) (a b : ZMod m) :
    (∑ t : ZMod m, ‖mixedPrimeSum P (t*a) b‖ ^ (2*k)) ≤
      (m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)) := by
  simp_rw [mixedPrimeSum_eq_weighted]
  apply weighted_prime_norm_moment_le hX hprime hcop hlower hupper hsize
  intro p
  simp [AddChar.norm_apply]

theorem mixed_parameter_moment_le {ι : Type*} (B : Finset ι)
    {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2*k-1) < m) (a : ZMod m) (b : ι → ZMod m) :
    (∑ j ∈ B, ∑ t : ZMod m, ‖mixedPrimeSum P (t*a) (b j)‖ ^ (2*k)) ≤
      (B.card : ℝ) * ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k))) := by
  calc
    _ ≤ ∑ _j ∈ B, (m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)) :=
      Finset.sum_le_sum fun j _ => mixed_prime_norm_moment_le hX hprime hcop hlower hupper hsize a (b j)
    _ = _ := by simp

end NField.Alignment.KaratsubaWeightedMoment
