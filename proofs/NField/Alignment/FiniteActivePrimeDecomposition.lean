/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacterPrimeLimit

/-! # The exact finite real-exponent prime-character decomposition -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.FiniteActivePrimeDecomposition

open scoped BigOperators
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionPrimeLimits

def finitePrimeCharacterSum {q : ℕ} (χ : Character q) (c : ℕ) (X σ : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc c ⌊X⌋₊,
    if p.Prime then χ (p : ZMod q) / (((p : ℝ) ^ σ : ℝ) : ℂ) else 0

def finitePeriodicPrimeSum {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) (c : ℕ) (X σ : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc c ⌊X⌋₊,
    if p.Prime then unitExtension F p / (((p : ℝ) ^ σ : ℝ) : ℂ) else 0

/-- Title: `The finite prime sum has exactly its active character expansion`. -/
theorem finite_prime_active_decomposition {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (c : ℕ) (X σ : ℝ) :
    finitePeriodicPrimeSum F c X σ =
      ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * finitePrimeCharacterSum χ c X σ := by
  classical
  have hall : finitePeriodicPrimeSum F c X σ =
      ∑ χ : Character q, collisionCoefficient F χ * finitePrimeCharacterSum χ c X σ := by
    unfold finitePeriodicPrimeSum finitePrimeCharacterSum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · simp only [hp, if_true, unitExtension_character_decomposition, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    · simp [hp]
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro χ _ hχ
  have hz : collisionCoefficient F χ = 0 := by simpa [activeCharacters] using hχ
  rw [hz, zero_mul]

end NField.Alignment.FiniteActivePrimeDecomposition
