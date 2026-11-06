/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacterPrimeLimit
import NField.Alignment.PrimeEulerLog

/-! # The literal complex prime series and its active Euler logarithms -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ComplexPrimeCharacterExpansion

open scoped BigOperators
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionPrimeLimits
open NField.Alignment.PrimeEulerLog

def periodicPrimeTerm {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (s : ℂ) (p : Nat.Primes) : ℂ :=
  unitExtension F p * (p : ℂ) ^ (-s)

def primeCutoff (c : ℕ) : Finset Nat.Primes :=
  (Finset.range (c + 1)).subtype Nat.Prime

@[simp] theorem mem_primeCutoff (c : ℕ) (p : Nat.Primes) :
    p ∈ primeCutoff c ↔ (p : ℕ) ≤ c := by
  exact (Finset.mem_subtype (a := (⟨p.val, p.property⟩ : Subtype Nat.Prime))).trans
    (Finset.mem_range.trans Nat.lt_succ_iff)

def finiteCorrection {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (c : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ primeCutoff c, periodicPrimeTerm F s p

def periodicPrimeSeries {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (c : ℕ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, if c < (p : ℕ) then periodicPrimeTerm F s p else 0

theorem periodicPrimeTerm_active {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (s : ℂ) (p : Nat.Primes) :
    periodicPrimeTerm F s p =
      ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * primeTerm χ s p := by
  classical
  have hall : periodicPrimeTerm F s p =
      ∑ χ : Character q, collisionCoefficient F χ * primeTerm χ s p := by
    simp only [periodicPrimeTerm, unitExtension_character_decomposition, Finset.sum_mul,
      primeTerm, mul_assoc]
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro χ _ hχ
  have hz : collisionCoefficient F χ = 0 := by simpa [activeCharacters] using hχ
  rw [hz, zero_mul]

theorem periodicPrimeTerm_summable {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    {s : ℂ} (hs : 1 < s.re) : Summable (periodicPrimeTerm F s) := by
  classical
  have h (t : Finset (Character q)) : Summable (fun p : Nat.Primes =>
      ∑ χ ∈ t, collisionCoefficient F χ * primeTerm χ s p) := by
    induction t using Finset.induction_on with
    | empty => simpa using (summable_zero : Summable (fun _ : Nat.Primes => (0 : ℂ)))
    | @insert χ t hχ ih =>
      simpa only [Finset.sum_insert hχ] using ((primeTerm_summable χ hs).mul_left _).add ih
  exact (h (activeCharacters F)).congr (fun p => (periodicPrimeTerm_active F s p).symm)

theorem periodicPrimeSeries_summable {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (c : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => if c < (p : ℕ) then periodicPrimeTerm F s p else 0) := by
  refine ((periodicPrimeTerm_summable F hs).indicator
    {p : Nat.Primes | c < (p : ℕ)}).congr ?_
  intro p
  by_cases hp : c < (p : ℕ)
  · simp [Set.indicator_of_mem hp, hp]
  · simp [Set.indicator_of_notMem hp, hp]

theorem all_prime_active_expansion {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' p : Nat.Primes, periodicPrimeTerm F s p) =
      ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * primeSeries χ s := by
  classical
  simp_rw [periodicPrimeTerm_active]
  rw [Summable.tsum_finsetSum (fun χ _ => (primeTerm_summable χ hs).mul_left _)]
  apply Finset.sum_congr rfl
  intro χ _
  exact (primeTerm_summable χ hs).tsum_mul_left _

theorem periodicPrimeSeries_eq_sub_finiteCorrection {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (c : ℕ) {s : ℂ} (hs : 1 < s.re) :
    periodicPrimeSeries F c s = (∑' p : Nat.Primes, periodicPrimeTerm F s p) -
      finiteCorrection F c s := by
  classical
  have h := (periodicPrimeTerm_summable F hs).sum_add_tsum_compl (s := primeCutoff c)
  have ht : (∑' p : ↑((↑(primeCutoff c) : Set Nat.Primes)ᶜ), periodicPrimeTerm F s p) =
      periodicPrimeSeries F c s := by
    simpa only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, mem_primeCutoff,
      not_le, periodicPrimeSeries] using
      tsum_subtype ((↑(primeCutoff c) : Set Nat.Primes)ᶜ) (periodicPrimeTerm F s)
  rw [ht] at h
  change finiteCorrection F c s + periodicPrimeSeries F c s = _ at h
  linear_combination h

/-- Title: `The complex collision prime series equals its active Euler logarithms and exact finite correction`. -/
theorem periodicPrimeSeries_euler_expansion {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (c : ℕ) {s : ℂ} (hs : 1 < s.re) :
    periodicPrimeSeries F c s =
      (∑ χ ∈ activeCharacters F, collisionCoefficient F χ * eulerLog χ s) -
      (∑ χ ∈ activeCharacters F, collisionCoefficient F χ * higherPowerSum χ s) -
      finiteCorrection F c s := by
  rw [periodicPrimeSeries_eq_sub_finiteCorrection F c hs, all_prime_active_expansion F hs]
  simp_rw [primeSeries_eq_eulerLog_sub_higherPower _ hs, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Title: `The exact finite prime correction is entire`. -/
theorem finiteCorrection_differentiable {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (c : ℕ) : Differentiable ℂ (finiteCorrection F c) := by
  apply Differentiable.fun_sum
  intro p _
  unfold periodicPrimeTerm
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact ((differentiable_id.neg).const_cpow (.inl hp)).const_mul _

end NField.Alignment.ComplexPrimeCharacterExpansion
