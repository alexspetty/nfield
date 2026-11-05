/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.ZMod.Basic

/-! # The terminating and coprime parts of a long-division denominator -/

set_option autoImplicit false
namespace NField.Alignment.DenominatorSplit

def supportedFactors (b q : ℕ) : List ℕ := q.primeFactorsList.filter (fun p => p ∣ b)

def supportedPart (b q : ℕ) : ℕ := (supportedFactors b q).prod

def coprimePart (b q : ℕ) : ℕ :=
  (q.primeFactorsList.filter (fun p => ¬p ∣ b)).prod

def burnIn (b q : ℕ) : ℕ := (supportedFactors b q).length

theorem factorization (b : ℕ) {q : ℕ} (hq : q ≠ 0) :
    supportedPart b q * coprimePart b q = q := by
  have h := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => p ∣ b) id q.primeFactorsList
  simpa [supportedPart, supportedFactors, coprimePart, Nat.prod_primeFactorsList hq]
    using h

theorem supportedPart_ne_zero (b : ℕ) {q : ℕ} (hq : q ≠ 0) :
    supportedPart b q ≠ 0 := by
  intro h
  have := factorization b hq
  simp only [h, zero_mul] at this
  exact hq this.symm

theorem coprimePart_ne_zero (b : ℕ) {q : ℕ} (hq : q ≠ 0) :
    coprimePart b q ≠ 0 := by
  intro h
  have := factorization b hq
  simp only [h, mul_zero] at this
  exact hq this.symm

theorem coprimePart_dvd (b : ℕ) {q : ℕ} (hq : q ≠ 0) : coprimePart b q ∣ q := by
  exact ⟨supportedPart b q, (factorization b hq).symm.trans (mul_comm _ _)⟩

theorem list_prod_dvd_pow_length (b : ℕ) (l : List ℕ)
    (hl : ∀ p ∈ l, p ∣ b) : l.prod ∣ b ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ']
    exact Nat.mul_dvd_mul (hl p (by simp)) (ih (fun a ha => hl a (by simp [ha])))

theorem supportedPart_dvd_power (b q : ℕ) : supportedPart b q ∣ b ^ burnIn b q := by
  apply list_prod_dvd_pow_length
  intro p hp
  exact of_decide_eq_true (List.mem_filter.mp hp).2

theorem coprimePart_coprime_base (b q : ℕ) : (coprimePart b q).Coprime b := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro p hp
  rcases List.mem_filter.mp hp with ⟨hp, hb⟩
  exact (Nat.prime_of_mem_primeFactorsList hp).coprime_iff_not_dvd.mpr
    (of_decide_eq_true hb)

theorem parts_coprime (b q : ℕ) : (supportedPart b q).Coprime (coprimePart b q) :=
  ((coprimePart_coprime_base b q).pow_right (burnIn b q)).of_dvd_right
    (supportedPart_dvd_power b q) |>.symm

/-- The CRT map is on the original denominator, including both of its parts. -/
noncomputable def remainderCRT (b : ℕ) {q : ℕ} (hq : q ≠ 0) :
    ZMod q ≃+* ZMod (supportedPart b q) × ZMod (coprimePart b q) :=
  (ZMod.ringEquivCongr (factorization b hq).symm).trans
    (ZMod.chineseRemainder (parts_coprime b q))

theorem remainderCRT_natCast (b : ℕ) {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    remainderCRT b hq (n : ZMod q) =
      ((n : ZMod (supportedPart b q)), (n : ZMod (coprimePart b q))) := by
  exact map_natCast (remainderCRT b hq) n

theorem supportedPart_eventually_zero (b q k n : ℕ) :
    ((b ^ (burnIn b q + k) * n : ℕ) : ZMod (supportedPart b q)) = 0 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  rw [pow_add]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (supportedPart_dvd_power b q) _) _

end NField.Alignment.DenominatorSplit
