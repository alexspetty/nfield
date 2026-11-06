/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rigidity of short sums of prime reciprocals

Clearing denominators over the distinct prime support turns a congruence
of reciprocal sums into an equality of small natural numbers. Reducing
that equality modulo each support prime recovers its multiplicity.

This is the finite arithmetic step behind the prime moment argument in
Karatsuba, *Fractional parts of functions of a special form*, Theorem 1.
The bound uses the actual upper endpoint and retains repeated primes.
It does not assert the bilinear estimate or the final Korolev input.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.KaratsubaPrimeReciprocalRigidity

open scoped BigOperators

def cofactor (S : Finset ℕ) (p : ℕ) : ℕ := ∏ q ∈ S.erase p, q

def clearedNumerator (S : Finset ℕ) (a : ℕ → ℕ) : ℕ :=
  ∑ p ∈ S, a p * cofactor S p

theorem cofactor_mul {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    cofactor S p * p = ∏ q ∈ S, q :=
  Finset.prod_erase_mul S id hp

theorem cofactor_cast {S : Finset ℕ} {m p : ℕ}
    (hp : p ∈ S) (hcop : p.Coprime m) :
    (cofactor S p : ZMod m) = (∏ q ∈ S, (q : ZMod m)) * (p : ZMod m)⁻¹ := by
  have hmul : (cofactor S p : ZMod m) * (p : ZMod m) = ∏ q ∈ S, (q : ZMod m) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ZMod m)) (cofactor_mul hp)
  calc
    (cofactor S p : ZMod m) = (cofactor S p : ZMod m) *
        ((p : ZMod m) * (p : ZMod m)⁻¹) := by rw [ZMod.coe_mul_inv_eq_one p hcop, mul_one]
    _ = _ := by rw [← mul_assoc, hmul]

/-- Denominator clearing preserves the exact multiplicities. -/
theorem clearedNumerator_cast (S : Finset ℕ) (a : ℕ → ℕ) (m : ℕ)
    (hcop : ∀ p ∈ S, p.Coprime m) :
    (clearedNumerator S a : ZMod m) =
      (∏ p ∈ S, (p : ZMod m)) * ∑ p ∈ S, (a p : ZMod m) * (p : ZMod m)⁻¹ := by
  simp only [clearedNumerator, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cofactor_cast hp (hcop p hp)]
  ring

theorem cofactor_le {S : Finset ℕ} {p k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hcard : S.card ≤ 2 * k)
    (hupper : ∀ q ∈ S, (q : ℝ) ≤ X) (hp : p ∈ S) :
    (cofactor S p : ℝ) ≤ X ^ (2 * k - 1) := by
  calc
    (cofactor S p : ℝ) = ∏ q ∈ S.erase p, (q : ℝ) := by simp [cofactor]
    _ ≤ ∏ _q ∈ S.erase p, X :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun q hq => hupper q (Finset.mem_of_mem_erase hq))
    _ = X ^ (S.erase p).card := by simp
    _ ≤ X ^ (2 * k - 1) := by
      apply pow_le_pow_right₀ hX
      rw [Finset.card_erase_of_mem hp]
      omega

theorem clearedNumerator_le {S : Finset ℕ} {a : ℕ → ℕ} {k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hcard : S.card ≤ 2 * k)
    (hupper : ∀ p ∈ S, (p : ℝ) ≤ X) (ha : ∑ p ∈ S, a p ≤ k) :
    (clearedNumerator S a : ℝ) ≤ k * X ^ (2 * k - 1) := by
  calc
    (clearedNumerator S a : ℝ) = ∑ p ∈ S, (a p : ℝ) * (cofactor S p : ℝ) := by
      simp [clearedNumerator]
    _ ≤ ∑ p ∈ S, (a p : ℝ) * X ^ (2 * k - 1) := by
      exact Finset.sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_left (cofactor_le hX hcard hupper hp) (Nat.cast_nonneg _)
    _ = (∑ p ∈ S, (a p : ℝ)) * X ^ (2 * k - 1) := (Finset.sum_mul _ _ _).symm
    _ ≤ k * X ^ (2 * k - 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
      exact_mod_cast ha

theorem clearedNumerator_mod_prime {S : Finset ℕ} (a : ℕ → ℕ)
    {p : ℕ} (hp : p ∈ S) :
    (clearedNumerator S a : ZMod p) = (a p : ZMod p) * (cofactor S p : ZMod p) := by
  simp only [clearedNumerator, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_eq_single p
  · intro q hq hqp
    have hd : p ∣ cofactor S q := Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩)
    have hz : (cofactor S q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [hz, mul_zero]
  · exact fun h => (h hp).elim

/-- Small multiplicities are determined by their cleared numerator. -/
theorem multiplicities_eq_of_clearedNumerator_eq {S : Finset ℕ} {a b : ℕ → ℕ}
    (hprime : ∀ p ∈ S, p.Prime)
    (ha : ∀ p ∈ S, a p < p) (hb : ∀ p ∈ S, b p < p)
    (heq : clearedNumerator S a = clearedNumerator S b) :
    ∀ p ∈ S, a p = b p := by
  intro p hp
  have hpp := hprime p hp
  letI : Fact p.Prime := ⟨hpp⟩
  have hnz : (cofactor S p : ZMod p) ≠ 0 := by
    simp only [cofactor, Nat.cast_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have hqprime := hprime q (Finset.mem_of_mem_erase hq)
    have hpeq : p = q := (Nat.dvd_prime hqprime).mp hd |>.resolve_left hpp.ne_one
    exact (Finset.mem_erase.mp hq).1 hpeq.symm
  have he := congrArg (fun n : ℕ => (n : ZMod p)) heq
  rw [clearedNumerator_mod_prime a hp, clearedNumerator_mod_prime b hp] at he
  have hab : (a p : ZMod p) = (b p : ZMod p) := mul_right_cancel₀ hnz he
  have hmod := (ZMod.natCast_eq_natCast_iff' (a p) (b p) p).mp hab
  simpa only [Nat.mod_eq_of_lt (ha p hp), Nat.mod_eq_of_lt (hb p hp)] using hmod

/-- A reciprocal congruence in the short range determines every prime multiplicity. -/
theorem multiplicities_eq_of_reciprocal_congruence {S : Finset ℕ} {a b : ℕ → ℕ}
    {m k : ℕ} {X : ℝ} (hX : 1 ≤ X) (hcard : S.card ≤ 2 * k)
    (hprime : ∀ p ∈ S, p.Prime) (hcop : ∀ p ∈ S, p.Coprime m)
    (hlower : ∀ p ∈ S, k < p) (hupper : ∀ p ∈ S, (p : ℝ) ≤ X)
    (ha : ∑ p ∈ S, a p ≤ k) (hb : ∑ p ∈ S, b p ≤ k)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m)
    (heq : (∑ p ∈ S, (a p : ZMod m) * (p : ZMod m)⁻¹) =
      ∑ p ∈ S, (b p : ZMod m) * (p : ZMod m)⁻¹) :
    ∀ p ∈ S, a p = b p := by
  have hna : clearedNumerator S a < m := by
    exact_mod_cast (clearedNumerator_le hX hcard hupper ha).trans_lt hsize
  have hnb : clearedNumerator S b < m := by
    exact_mod_cast (clearedNumerator_le hX hcard hupper hb).trans_lt hsize
  have hc : (clearedNumerator S a : ZMod m) = (clearedNumerator S b : ZMod m) := by
    rw [clearedNumerator_cast S a m hcop, clearedNumerator_cast S b m hcop, heq]
  have hn : clearedNumerator S a = clearedNumerator S b := by
    have he := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc
    simpa only [Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb] using he
  apply multiplicities_eq_of_clearedNumerator_eq hprime _ _ hn
  · intro p hp
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp).trans ha |>.trans_lt (hlower p hp)
  · intro p hp
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp).trans hb |>.trans_lt (hlower p hp)

end NField.Alignment.KaratsubaPrimeReciprocalRigidity
