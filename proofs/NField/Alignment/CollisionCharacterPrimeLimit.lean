/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealCollisionPrimeLimits
import NField.Alignment.PrimeResidualCutoffs

/-! # The finite character formula at the prime harmonic boundary -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.ProgressionMertens
open NField.Alignment.CharacterPrimeReciprocal
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionTransform
open NField.Alignment.CenteredCollisionSum

def characterPrimeTail {q : ℕ} (χ : Character q) (c : ℕ) (x : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc c ⌊x⌋₊, if p.Prime then χ (p : ZMod q) / (p : ℂ) else 0

theorem character_prime_tail_converges {q : ℕ} [NeZero q]
    (χ : Character q) (hχ : χ ≠ 1) (c : ℕ) :
    ∃ L : ℂ, Tendsto (characterPrimeTail χ c) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := primeReciprocal_tendsto χ hχ
  have h := hL.comp ((tendsto_add_atTop_nat 1).comp
    (tendsto_nat_floor_atTop : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop))
  have hz : primeReciprocal χ 0 = 0 := by simp [primeReciprocal]
  have hfull : Tendsto (characterPrimeTail χ 0) atTop (𝓝 L) := by
    convert h using 1
    ext x
    exact sum_Ioc_eq_range_succ hz ⌊x⌋₊
  exact ⟨_, sum_Ioc_cutoff_limit (primeReciprocal χ) c hfull⟩

def characterPrimeConstant {q : ℕ} [NeZero q] (χ : Character q) (c : ℕ) : ℂ :=
  if h : χ ≠ 1 then (character_prime_tail_converges χ h c).choose else 0

theorem characterPrimeConstant_limit {q : ℕ} [NeZero q]
    (χ : Character q) (hχ : χ ≠ 1) (c : ℕ) :
    Tendsto (characterPrimeTail χ c) atTop (𝓝 (characterPrimeConstant χ c)) := by
  rw [characterPrimeConstant, dif_pos hχ]
  exact (character_prime_tail_converges χ hχ c).choose_spec

def collisionGateCharacters (b ell : ℕ) [NeZero b] [NeZero (allLagModulus b ell)] :
    Finset (Character (allLagModulus b ell)) := by
  classical
  exact Finset.univ.filter (fun χ => χ.Odd ∧ ¬BaseFactored χ)

theorem odd_character_ne_one {q : ℕ} [NeZero q]
    {χ : Character q} (hodd : χ.Odd) : χ ≠ 1 := by
  intro h
  subst χ
  have heven : (1 : Character q).Even := by
    unfold DirichletCharacter.Even
    exact MulChar.one_apply isUnit_neg_one
  exact (1 : Character q).not_even_and_odd ⟨heven, hodd⟩

theorem coefficient_zero_outside_gate {b ell : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell))
    (hχ : χ ∉ collisionGateCharacters b ell) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 := by
  classical
  by_cases hodd : χ.Odd
  · have hfactor : BaseFactored χ := by
      by_contra hn
      exact hχ (by simp [collisionGateCharacters, hodd, hn])
    exact centeredCollisionTransform_baseFactored_zero χ hfactor
  · rcases χ.even_or_odd with heven | ho
    · exact centeredCollisionTransform_even_zero hb hell χ heven
    · exact (hodd ho).elim

theorem unitExtension_character_decomposition {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (n : ℕ) :
    unitExtension F n = ∑ χ : Character q, collisionCoefficient F χ * χ (n : ZMod q) := by
  classical
  by_cases hn : IsUnit (n : ZMod q)
  · rw [unitExtension, dif_pos hn, ← collisionCoefficient_inversion F hn.unit]
    simp only [hn.unit_spec]
  · simp only [unitExtension, dif_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro χ _
    rw [MulChar.map_nonunit χ hn, mul_zero]

theorem centered_prime_tail_character_decomposition
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (c : ℕ) (x : ℝ) :
    (∑ p ∈ Finset.Ioc c ⌊x⌋₊,
      if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0) =
    ∑ χ ∈ collisionGateCharacters b ell,
      collisionCoefficient (centeredCollisionTransform b ell) χ * characterPrimeTail χ c x := by
  classical
  have hall : (∑ p ∈ Finset.Ioc c ⌊x⌋₊,
      if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0) =
      ∑ χ : Character (allLagModulus b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ * characterPrimeTail χ c x := by
    simp only [characterPrimeTail, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · simp only [hp, ↓reduceIte, directCenteredCollisionValue_eq_unitExtension hb hell,
        unitExtension_character_decomposition, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    · simp [hp]
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro χ _ hχ
  rw [coefficient_zero_outside_gate hb hell χ hχ, zero_mul]

/-- Title: `The centered harmonic constant is the finite gated character sum`.
The character limits use the literal prime cutoff of the manuscript. -/
theorem centered_harmonic_character_formula
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ K : ℝ,
      Tendsto (realPrimeTailSum (fun p => realDirectCenteredCollisionValue b ell p / p)
        (allLagModulus b ell)) atTop (𝓝 K) ∧
      (K : ℂ) = ∑ χ ∈ collisionGateCharacters b ell,
        collisionCoefficient (centeredCollisionTransform b ell) χ *
          characterPrimeConstant χ (allLagModulus b ell) := by
  classical
  obtain ⟨K, hK⟩ := real_centered_collision_harmonic_limit hb hell
  refine ⟨K, hK, ?_⟩
  have hsum : Tendsto (fun x : ℝ => ∑ χ ∈ collisionGateCharacters b ell,
      collisionCoefficient (centeredCollisionTransform b ell) χ *
        characterPrimeTail χ (allLagModulus b ell) x) atTop
      (𝓝 (∑ χ ∈ collisionGateCharacters b ell,
        collisionCoefficient (centeredCollisionTransform b ell) χ *
          characterPrimeConstant χ (allLagModulus b ell))) := by
    apply tendsto_finsetSum
    intro χ hχ
    have ho : χ.Odd := (Finset.mem_filter.mp hχ).2.1
    exact (characterPrimeConstant_limit χ (odd_character_ne_one ho) _).const_mul _
  have hcast := (Complex.continuous_ofReal.tendsto K).comp hK
  have heq (x : ℝ) :
      (realPrimeTailSum (fun p => realDirectCenteredCollisionValue b ell p / p)
        (allLagModulus b ell) x : ℂ) =
      ∑ χ ∈ collisionGateCharacters b ell,
        collisionCoefficient (centeredCollisionTransform b ell) χ *
          characterPrimeTail χ (allLagModulus b ell) x := by
    rw [ofReal_realPrimeTailSum]
    simp only [Complex.ofReal_div, ofReal_realDirectCenteredCollisionValue,
      Complex.ofReal_natCast]
    exact centered_prime_tail_character_decomposition hb hell _ x
  exact tendsto_nhds_unique hcast (hsum.congr' (Filter.Eventually.of_forall (fun x => (heq x).symm)))

end NField.Alignment.CollisionPrimeLimits
