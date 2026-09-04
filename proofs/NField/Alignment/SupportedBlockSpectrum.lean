/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import NField.Alignment.CrossAlignmentMatrix

/-!
# Spectrum of synchronized supported blocks

This file closes the linear-algebraic content of a matrix that is a direct sum
of one all-ones terminating block of size `s - 1` and `p - 1` all-ones
nonterminating blocks of size `s`.  The implementation is independent of any
manuscript title.
-/

namespace NField.Alignment.SupportedBlockSpectrum

open scoped BigOperators
open NField.Alignment.CrossAlignmentMatrix

/-- The matrix action is exactly the vector of block sums, repeated on every
coordinate of the corresponding block. -/
theorem supportedBlockMatrix_mulVec_apply
    {p s : ℕ} (v : SupportedBlockIndex p s → ℚ) :
    (∀ i : Fin (s - 1),
      Matrix.mulVec (supportedBlockMatrix p s) v (Sum.inl i) =
        ∑ j : Fin (s - 1), v (Sum.inl j)) ∧
    (∀ c : Fin (p - 1), ∀ i : Fin s,
      Matrix.mulVec (supportedBlockMatrix p s) v (Sum.inr (c, i)) =
        ∑ j : Fin s, v (Sum.inr (c, j))) := by
  constructor
  · intro i
    simp [Matrix.mulVec, dotProduct, supportedBlockMatrix,
      Fintype.sum_sum_type]
  · intro c i
    simp only [Matrix.mulVec, dotProduct, supportedBlockMatrix,
      Fintype.sum_sum_type, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_prod_type]
    simp

/-- For `s ≥ 2`, the null space is exactly the space of vectors whose sum
inside every all-ones block vanishes. -/
theorem supportedBlockMatrix_mulVec_eq_zero_iff
    {p s : ℕ} (hs : 2 ≤ s) (v : SupportedBlockIndex p s → ℚ) :
    Matrix.mulVec (supportedBlockMatrix p s) v = 0 ↔
      (∑ i : Fin (s - 1), v (Sum.inl i) = 0) ∧
      (∀ c : Fin (p - 1), ∑ i : Fin s, v (Sum.inr (c, i)) = 0) := by
  constructor
  · intro hzero
    have htermIndex : 0 < s - 1 := by omega
    let i : Fin (s - 1) := ⟨0, htermIndex⟩
    have hterm := congrFun hzero (Sum.inl i)
    have hres (c : Fin (p - 1)) :
        ∑ j : Fin s, v (Sum.inr (c, j)) = 0 := by
      let j : Fin s := ⟨0, by omega⟩
      have hj := congrFun hzero (Sum.inr (c, j))
      simpa [supportedBlockMatrix_mulVec_apply v] using hj
    constructor
    · simpa [supportedBlockMatrix_mulVec_apply v] using hterm
    · exact hres
  · rintro ⟨hterm, hres⟩
    exact supportedBlockMatrix_mulVec_eq_zero v hterm hres

/-- Block labels in the positive supported-lift case. -/
abbrev PositiveBlockLabel (p : ℕ) := Sum (Fin 1) (Fin (p - 1))

/-- Sum the entries in each synchronized block. -/
def blockSumLinear (p s : ℕ) :
    (SupportedBlockIndex p s → ℚ) →ₗ[ℚ] (PositiveBlockLabel p → ℚ) where
  toFun v
    | Sum.inl _ => ∑ i : Fin (s - 1), v (Sum.inl i)
    | Sum.inr c => ∑ i : Fin s, v (Sum.inr (c, i))
  map_add' x y := by
    funext label
    cases label <;> simp [Finset.sum_add_distrib]
  map_smul' a x := by
    funext label
    cases label <;> simp [Finset.mul_sum]

/-- Repeat one block value on every coordinate of that block. -/
def blockRepeatLinear (p s : ℕ) :
    (PositiveBlockLabel p → ℚ) →ₗ[ℚ] (SupportedBlockIndex p s → ℚ) where
  toFun z
    | Sum.inl _ => z (Sum.inl 0)
    | Sum.inr ci => z (Sum.inr ci.1)
  map_add' x y := by
    funext i
    cases i <;> rfl
  map_smul' a x := by
    funext i
    cases i <;> rfl

/-- The supported block matrix factors as block summation followed by block
repetition. -/
theorem supportedBlockMatrix_mulVecLin_factor (p s : ℕ) :
    (supportedBlockMatrix p s).mulVecLin =
      (blockRepeatLinear p s).comp (blockSumLinear p s) := by
  apply LinearMap.ext
  intro v
  funext i
  rcases supportedBlockMatrix_mulVec_apply v with ⟨hterm, hres⟩
  cases i with
  | inl i => simpa [blockRepeatLinear, blockSumLinear] using hterm i
  | inr ci =>
      rcases ci with ⟨c, i⟩
      simpa [blockRepeatLinear, blockSumLinear] using hres c i

/-- When every block is nonempty, arbitrary block sums can be prescribed. -/
theorem blockSumLinear_surjective {p s : ℕ} (hs : 2 ≤ s) :
    Function.Surjective (blockSumLinear p s) := by
  intro z
  let termIndex : Fin (s - 1) := ⟨0, by omega⟩
  let residueIndex : Fin s := ⟨0, by omega⟩
  let v : SupportedBlockIndex p s → ℚ
    | Sum.inl i => if i = termIndex then z (Sum.inl 0) else 0
    | Sum.inr ci => if ci.2 = residueIndex then z (Sum.inr ci.1) else 0
  refine ⟨v, ?_⟩
  funext label
  cases label with
  | inl i =>
      fin_cases i
      simp [blockSumLinear, v, termIndex]
  | inr c =>
      simp [blockSumLinear, v, residueIndex]

/-- Repetition is injective when every block is nonempty. -/
theorem blockRepeatLinear_injective {p s : ℕ} (hs : 2 ≤ s) :
    Function.Injective (blockRepeatLinear p s) := by
  intro x y h
  funext label
  cases label with
  | inl i =>
      fin_cases i
      let termIndex : Fin (s - 1) := ⟨0, by omega⟩
      exact congrFun h (Sum.inl termIndex)
  | inr c =>
      let residueIndex : Fin s := ⟨0, by omega⟩
      exact congrFun h (Sum.inr (c, residueIndex))

/-- For `s ≥ 2`, the exact rank is the number `p` of nonempty synchronized
blocks. -/
theorem supportedBlockMatrix_rank_of_two_le
    {p s : ℕ} (hp : 1 ≤ p) (hs : 2 ≤ s) :
    (supportedBlockMatrix p s).rank = p := by
  rw [Matrix.rank, supportedBlockMatrix_mulVecLin_factor]
  have hsurj := blockSumLinear_surjective (p := p) hs
  have hrange : LinearMap.range
      ((blockRepeatLinear p s).comp (blockSumLinear p s)) =
      LinearMap.range (blockRepeatLinear p s) := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      exact ⟨blockSumLinear p s v, rfl⟩
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      rcases hsurj z with ⟨v, hv⟩
      exact ⟨v, by simp [hv]⟩
  rw [hrange]
  have hinj := blockRepeatLinear_injective (p := p) hs
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi]
  simp
  omega

/-- At `s = 1` the terminating block is empty and every residue block is a
singleton, so the matrix is the identity. -/
theorem supportedBlockMatrix_one (p : ℕ) :
    supportedBlockMatrix p 1 = 1 := by
  ext i j
  cases i with
  | inl i => exact Fin.elim0 i
  | inr i =>
      cases j with
      | inl j => exact Fin.elim0 j
      | inr j =>
          rcases i with ⟨c, i⟩
          rcases j with ⟨d, j⟩
          fin_cases i
          fin_cases j
          simp [supportedBlockMatrix, Matrix.one_apply, Prod.ext_iff]

/-- At `s = 1` the exact rank is `p - 1`. -/
theorem supportedBlockMatrix_rank_one (p : ℕ) :
    (supportedBlockMatrix p 1).rank = p - 1 := by
  rw [supportedBlockMatrix_one, Matrix.rank_one]
  simp

/-- The zero-eigenspace has exactly the multiplicity printed in the supported
lift spectrum. -/
theorem supportedBlockMatrix_kernel_finrank
    {p s : ℕ} (hp : 1 ≤ p) (hs : 2 ≤ s) :
    Module.finrank ℚ (supportedBlockMatrix p s).mulVecLin.ker =
      p * s - p - 1 := by
  have hdimension :=
    (supportedBlockMatrix p s).mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℚ
      (supportedBlockMatrix p s).mulVecLin.range = p := by
    simpa [Matrix.rank] using supportedBlockMatrix_rank_of_two_le hp hs
  have hdomain : Module.finrank ℚ
      (SupportedBlockIndex p s → ℚ) = p * s - 1 := by
    rw [Module.finrank_pi]
    simp only [SupportedBlockIndex, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_prod]
    rw [Nat.sub_mul, one_mul]
    have hsps : s ≤ p * s := by
      simpa [one_mul] using Nat.mul_le_mul_right s hp
    omega
  rw [hrange, hdomain] at hdimension
  omega

/-- Complete eigenvalue ledger for the supported block model.  The displayed
eigenvectors realize the nonzero eigenvalues, and the exact kernel condition
accounts for every remaining direction. -/
theorem supportedBlockSpectrum_complete {p s : ℕ}
    (hp : 1 ≤ p) (hs : 2 ≤ s) :
    (supportedBlockMatrix p s).rank = p ∧
    Module.finrank ℚ (supportedBlockMatrix p s).mulVecLin.ker =
      p * s - p - 1 ∧
    (∀ c : Fin (p - 1),
      Matrix.mulVec (supportedBlockMatrix p s) (residueBlockVector p s c) =
        (s : ℚ) • residueBlockVector p s c) ∧
    Matrix.mulVec (supportedBlockMatrix p s) (terminatingBlockVector p s) =
      ((s - 1 : ℕ) : ℚ) • terminatingBlockVector p s ∧
    (∀ v : SupportedBlockIndex p s → ℚ,
      Matrix.mulVec (supportedBlockMatrix p s) v = 0 ↔
        (∑ i : Fin (s - 1), v (Sum.inl i) = 0) ∧
        (∀ c : Fin (p - 1),
          ∑ i : Fin s, v (Sum.inr (c, i)) = 0)) := by
  exact ⟨supportedBlockMatrix_rank_of_two_le hp hs,
    supportedBlockMatrix_kernel_finrank hp hs,
    supportedBlockMatrix_residue_eigenvector p s,
    supportedBlockMatrix_terminating_eigenvector p s,
    supportedBlockMatrix_mulVec_eq_zero_iff hs⟩

end NField.Alignment.SupportedBlockSpectrum
