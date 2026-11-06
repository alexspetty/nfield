/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaFiberEnergy
import Mathlib.Analysis.Fourier.ZMod

/-! # Finite character orthogonality for actual reciprocal tuples -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaFourierMoment
open scoped BigOperators
open KaratsubaPrimeMoment

theorem character_orthogonality {m : ℕ} [NeZero m] (t : ZMod m) :
    (∑ a : ZMod m, ZMod.stdAddChar (a * t)) = if t = 0 then (m : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht, ZMod.card]
  · rw [if_neg ht]
    simpa only [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m ht)

/-- Orthogonality counts ordered tuple pairs, retaining all repetitions. -/
theorem reciprocal_pair_orthogonality (P : Finset ℕ) (m k : ℕ) [NeZero m] :
    (∑ a : ZMod m, ∑ u : PrimeTuple P k, ∑ v : PrimeTuple P k,
      ZMod.stdAddChar (a * (reciprocalSum m (fun i => (v i).val) -
        reciprocalSum m (fun i => (u i).val)))) =
      (m : ℂ) * reciprocalCollisionCount P m k := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod m))), character_orthogonality,
    sub_eq_zero]
  simp only [reciprocalCollisionCount, reciprocalFiber, Nat.cast_sum,
    Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.mul_sum, mul_ite, mul_one, mul_zero]

theorem character_sum {m : ℕ} [NeZero m] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod m) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

def primeExponentialSum (P : Finset ℕ) (m : ℕ) [NeZero m] (a : ZMod m) : ℂ :=
  ∑ p : {p // p ∈ P}, ZMod.stdAddChar (a * (p.val : ZMod m)⁻¹)

theorem prime_sum_power (P : Finset ℕ) (m k : ℕ) [NeZero m] (a : ZMod m) :
    primeExponentialSum P m a ^ k = ∑ u : PrimeTuple P k,
      ZMod.stdAddChar (a * reciprocalSum m (fun i => (u i).val)) := by
  rw [primeExponentialSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro u _
  simp only [reciprocalSum, Finset.mul_sum, character_sum]

/-- The exact even moment, expressed as a product with its complex conjugate. -/
theorem prime_even_moment (P : Finset ℕ) (m k : ℕ) [NeZero m] :
    (∑ a : ZMod m, primeExponentialSum P m a ^ k *
      (starRingEnd ℂ) (primeExponentialSum P m a ^ k)) =
      (m : ℂ) * reciprocalCollisionCount P m k := by
  rw [← reciprocal_pair_orthogonality]
  apply Finset.sum_congr rfl
  intro a _
  simp only [prime_sum_power, map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [show (starRingEnd ℂ) (ZMod.stdAddChar (a * reciprocalSum m (fun i => (u i).val))) =
      ZMod.stdAddChar (-(a * reciprocalSum m (fun i => (u i).val))) from
    (AddChar.map_neg_eq_conj _ _).symm]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem prime_norm_even_moment (P : Finset ℕ) (m k : ℕ) [NeZero m] :
    (∑ a : ZMod m, ‖primeExponentialSum P m a‖ ^ (2 * k)) =
      (m : ℝ) * reciprocalCollisionCount P m k := by
  have h := prime_even_moment P m k
  simp_rw [Complex.mul_conj, map_pow] at h
  have hr := congrArg Complex.re h
  simpa [← Complex.ofReal_pow, Complex.normSq_eq_norm_sq, pow_mul] using hr

theorem prime_norm_even_moment_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) :
    (∑ a : ZMod m, ‖primeExponentialSum P m a‖ ^ (2 * k)) ≤
      (m : ℝ) * (k.factorial * P.card ^ k) := by
  rw [prime_norm_even_moment]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast reciprocalCollisionCount_le hX hprime hcop hlower hupper hsize

end NField.Alignment.KaratsubaFourierMoment
