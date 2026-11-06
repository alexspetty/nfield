/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaFourierMoment
import NField.Alignment.KaratsubaFrequencyKernel

/-! # Scaled prime moments with the exact frequency gcd -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaScaledFourierMoment
open scoped BigOperators
open KaratsubaFiberEnergy KaratsubaFourierMoment KaratsubaFrequencyKernel KaratsubaPrimeMoment

theorem finite_character_energy {α : Type*} [Fintype α] {m : ℕ} [NeZero m]
    (f : α → ZMod m) :
    (∑ t : ZMod m, (∑ x, ZMod.stdAddChar (t * f x)) *
      (starRingEnd ℂ) (∑ x, ZMod.stdAddChar (t * f x))) =
      (m : ℂ) * ∑ y, (fiberCount f y : ℂ) ^ 2 := by
  classical
  have he : ∑ y, (fiberCount f y : ℂ) ^ 2 = ∑ x, (fiberCount f (f x) : ℂ) := by
    exact_mod_cast sum_fiberCount_sq f
  rw [he]
  simp only [map_sum, Finset.sum_mul_sum]
  have hc (t : ZMod m) (x y : α) :
      ZMod.stdAddChar (t * f x) * (starRingEnd ℂ) (ZMod.stdAddChar (t * f y)) =
        ZMod.stdAddChar (t * (f x - f y)) := by
    rw [show (starRingEnd ℂ) (ZMod.stdAddChar (t * f y)) =
      ZMod.stdAddChar (-(t * f y)) from (AddChar.map_neg_eq_conj _ _).symm,
      ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod m))), character_orthogonality,
    sub_eq_zero]
  simp only [fiberCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro y _
  simp only [eq_comm]

theorem scaled_prime_norm_moment (P : Finset ℕ) (m k : ℕ) [NeZero m] (a : ZMod m) :
    (∑ t : ZMod m, ‖primeExponentialSum P m (t * a)‖ ^ (2 * k)) =
      (m : ℝ) * ∑ y, (fiberCount (fun u : PrimeTuple P k =>
        a * reciprocalSum m (fun i => (u i).val)) y : ℝ) ^ 2 := by
  have h := finite_character_energy (fun u : PrimeTuple P k =>
    a * reciprocalSum m (fun i => (u i).val))
  have hp (t : ZMod m) : (∑ u : PrimeTuple P k,
      ZMod.stdAddChar (t * (a * reciprocalSum m (fun i => (u i).val)))) =
        primeExponentialSum P m (t * a) ^ k := by
    rw [prime_sum_power]
    simp only [mul_assoc]
  simp_rw [hp, Complex.mul_conj, map_pow] at h
  have hr := congrArg Complex.re h
  simpa [← Complex.ofReal_pow, ← Nat.cast_pow, Complex.normSq_eq_norm_sq, pow_mul] using hr

theorem scaled_prime_norm_moment_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) (a : ZMod m) :
    (∑ t : ZMod m, ‖primeExponentialSum P m (t * a)‖ ^ (2 * k)) ≤
      (m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)) := by
  rw [scaled_prime_norm_moment]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast reciprocal_frequency_energy_le hX hprime hcop hlower hupper hsize a

end NField.Alignment.KaratsubaScaledFourierMoment
