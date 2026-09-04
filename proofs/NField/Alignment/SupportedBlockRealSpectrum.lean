/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import NField.Alignment.SupportedBlockReindexing
import NField.Alignment.SupportedBlockSpectrum

/-!
# Real spectrum of synchronized supported blocks

Title-independent real-linear closure for the block matrix obtained from the
literal synchronized matrix.  This supplements the exact rational model with
rank, kernel, and eigenvector statements in the scalar field used by the
literal Gram matrix.
-/

namespace NField.Alignment.SupportedBlockRealSpectrum

open scoped BigOperators
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.SupportedBlockReindexing
open NField.Alignment.SupportedBlockSpectrum

/-- Indicator of the terminating all-ones block over the reals. -/
def terminatingBlockVectorReal (p s : ℕ) :
    SupportedBlockIndex p s → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Indicator of one nonterminating residue block over the reals. -/
def residueBlockVectorReal (p s : ℕ) (c : Fin (p - 1)) :
    SupportedBlockIndex p s → ℝ
  | Sum.inl _ => 0
  | Sum.inr ci => if ci.1 = c then 1 else 0

/-- The real block matrix acts by summing within a synchronized block and
repeating that sum on every coordinate of the block. -/
theorem supportedBlockMatrixReal_mulVec_apply
    {p s : ℕ} (v : SupportedBlockIndex p s → ℝ) :
    (∀ i : Fin (s - 1),
      Matrix.mulVec (supportedBlockMatrixReal p s) v (Sum.inl i) =
        ∑ j : Fin (s - 1), v (Sum.inl j)) ∧
    (∀ c : Fin (p - 1), ∀ i : Fin s,
      Matrix.mulVec (supportedBlockMatrixReal p s) v (Sum.inr (c, i)) =
        ∑ j : Fin s, v (Sum.inr (c, j))) := by
  constructor
  · intro i
    simp [Matrix.mulVec, dotProduct, supportedBlockMatrixReal,
      supportedBlockMatrix, Fintype.sum_sum_type]
  · intro c i
    simp only [Matrix.mulVec, dotProduct, supportedBlockMatrixReal,
      supportedBlockMatrix, Matrix.map_apply, map_zero,
      Fintype.sum_sum_type, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_prod_type]
    simp

/-- For nonempty terminating and residue blocks, the real null space is
exactly the space of vectors with zero sum in every block. -/
theorem supportedBlockMatrixReal_mulVec_eq_zero_iff
    {p s : ℕ} (hs : 2 ≤ s) (v : SupportedBlockIndex p s → ℝ) :
    Matrix.mulVec (supportedBlockMatrixReal p s) v = 0 ↔
      (∑ i : Fin (s - 1), v (Sum.inl i) = 0) ∧
      (∀ c : Fin (p - 1), ∑ i : Fin s, v (Sum.inr (c, i)) = 0) := by
  constructor
  · intro hzero
    let i : Fin (s - 1) := ⟨0, by omega⟩
    have hterm := congrFun hzero (Sum.inl i)
    have hres (c : Fin (p - 1)) :
        ∑ j : Fin s, v (Sum.inr (c, j)) = 0 := by
      let j : Fin s := ⟨0, by omega⟩
      have hj := congrFun hzero (Sum.inr (c, j))
      simpa [supportedBlockMatrixReal_mulVec_apply v] using hj
    constructor
    · simpa [supportedBlockMatrixReal_mulVec_apply v] using hterm
    · exact hres
  · rintro ⟨hterm, hres⟩
    funext i
    cases i with
    | inl i =>
        simpa [supportedBlockMatrixReal_mulVec_apply v] using hterm
    | inr ci =>
        simpa [supportedBlockMatrixReal_mulVec_apply v] using hres ci.1

/-- Sum the entries in each real synchronized block. -/
def realBlockSumLinear (p s : ℕ) :
    (SupportedBlockIndex p s → ℝ) →ₗ[ℝ]
      (Sum (Fin 1) (Fin (p - 1)) → ℝ) where
  toFun v
    | Sum.inl _ => ∑ i : Fin (s - 1), v (Sum.inl i)
    | Sum.inr c => ∑ i : Fin s, v (Sum.inr (c, i))
  map_add' x y := by
    funext label
    cases label <;> simp [Finset.sum_add_distrib]
  map_smul' a x := by
    funext label
    cases label <;> simp [Finset.mul_sum]

/-- Repeat one real block value on every coordinate in that block. -/
def realBlockRepeatLinear (p s : ℕ) :
    (Sum (Fin 1) (Fin (p - 1)) → ℝ) →ₗ[ℝ]
      (SupportedBlockIndex p s → ℝ) where
  toFun z
    | Sum.inl _ => z (Sum.inl 0)
    | Sum.inr ci => z (Sum.inr ci.1)
  map_add' x y := by
    funext i
    cases i <;> rfl
  map_smul' a x := by
    funext i
    cases i <;> rfl

/-- The real matrix factors as block summation followed by repetition. -/
theorem supportedBlockMatrixReal_mulVecLin_factor (p s : ℕ) :
    (supportedBlockMatrixReal p s).mulVecLin =
      (realBlockRepeatLinear p s).comp (realBlockSumLinear p s) := by
  apply LinearMap.ext
  intro v
  funext i
  rcases supportedBlockMatrixReal_mulVec_apply v with ⟨hterm, hres⟩
  cases i with
  | inl i => simpa [realBlockRepeatLinear, realBlockSumLinear] using hterm i
  | inr ci =>
      rcases ci with ⟨c, i⟩
      simpa [realBlockRepeatLinear, realBlockSumLinear] using hres c i

/-- Every real block-sum vector can be prescribed when `s ≥ 2`. -/
theorem realBlockSumLinear_surjective {p s : ℕ} (hs : 2 ≤ s) :
    Function.Surjective (realBlockSumLinear p s) := by
  intro z
  let termIndex : Fin (s - 1) := ⟨0, by omega⟩
  let residueIndex : Fin s := ⟨0, by omega⟩
  let v : SupportedBlockIndex p s → ℝ
    | Sum.inl i => if i = termIndex then z (Sum.inl 0) else 0
    | Sum.inr ci => if ci.2 = residueIndex then z (Sum.inr ci.1) else 0
  refine ⟨v, ?_⟩
  funext label
  cases label with
  | inl i =>
      fin_cases i
      simp [realBlockSumLinear, v, termIndex]
  | inr c =>
      simp [realBlockSumLinear, v, residueIndex]

/-- Repetition of real block values is injective when every block is
nonempty. -/
theorem realBlockRepeatLinear_injective {p s : ℕ} (hs : 2 ≤ s) :
    Function.Injective (realBlockRepeatLinear p s) := by
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

/-- For `s ≥ 2`, the literal real block model has exact rank `p`. -/
theorem supportedBlockMatrixReal_rank_of_two_le
    {p s : ℕ} (hp : 1 ≤ p) (hs : 2 ≤ s) :
    (supportedBlockMatrixReal p s).rank = p := by
  rw [Matrix.rank, supportedBlockMatrixReal_mulVecLin_factor]
  have hsurj := realBlockSumLinear_surjective (p := p) hs
  have hrange : LinearMap.range
      ((realBlockRepeatLinear p s).comp (realBlockSumLinear p s)) =
      LinearMap.range (realBlockRepeatLinear p s) := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      exact ⟨realBlockSumLinear p s v, rfl⟩
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      rcases hsurj z with ⟨v, hv⟩
      exact ⟨v, by simp [hv]⟩
  rw [hrange]
  have hinj := realBlockRepeatLinear_injective (p := p) hs
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi]
  simp
  omega

/-- At `s = 1`, the real block matrix is the identity. -/
theorem supportedBlockMatrixReal_one (p : ℕ) :
    supportedBlockMatrixReal p 1 = 1 := by
  rw [supportedBlockMatrixReal, supportedBlockMatrix_one]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- At `s = 1`, the real block matrix has rank `p-1`. -/
theorem supportedBlockMatrixReal_rank_one (p : ℕ) :
    (supportedBlockMatrixReal p 1).rank = p - 1 := by
  rw [supportedBlockMatrixReal_one, Matrix.rank_one]
  simp

/-- The real terminating block direction has eigenvalue `s-1`. -/
theorem supportedBlockMatrixReal_terminating_eigenvector (p s : ℕ) :
    Matrix.mulVec (supportedBlockMatrixReal p s)
        (terminatingBlockVectorReal p s) =
      ((s - 1 : ℕ) : ℝ) • terminatingBlockVectorReal p s := by
  funext i
  cases i with
  | inl i =>
      rw [(supportedBlockMatrixReal_mulVec_apply
        (terminatingBlockVectorReal p s)).1 i]
      simp [terminatingBlockVectorReal]
  | inr ci =>
      rw [(supportedBlockMatrixReal_mulVec_apply
        (terminatingBlockVectorReal p s)).2 ci.1 ci.2]
      simp [terminatingBlockVectorReal]

/-- Each real residue-block direction has eigenvalue `s`. -/
theorem supportedBlockMatrixReal_residue_eigenvector
    (p s : ℕ) (c : Fin (p - 1)) :
    Matrix.mulVec (supportedBlockMatrixReal p s)
        (residueBlockVectorReal p s c) =
      (s : ℝ) • residueBlockVectorReal p s c := by
  funext i
  cases i with
  | inl i =>
      rw [(supportedBlockMatrixReal_mulVec_apply
        (residueBlockVectorReal p s c)).1 i]
      simp [residueBlockVectorReal]
  | inr ci =>
      rcases ci with ⟨c', i⟩
      rw [(supportedBlockMatrixReal_mulVec_apply
        (residueBlockVectorReal p s c)).2 c' i]
      by_cases h : c' = c
      · subst c'
        simp [residueBlockVectorReal]
      · simp [residueBlockVectorReal, h]

/-- The real zero eigenspace has exactly the manuscript's multiplicity. -/
theorem supportedBlockMatrixReal_kernel_finrank
    {p s : ℕ} (hp : 1 ≤ p) (hs : 2 ≤ s) :
    Module.finrank ℝ (supportedBlockMatrixReal p s).mulVecLin.ker =
      p * s - p - 1 := by
  have hdimension :=
    (supportedBlockMatrixReal p s).mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ
      (supportedBlockMatrixReal p s).mulVecLin.range = p := by
    simpa [Matrix.rank] using supportedBlockMatrixReal_rank_of_two_le hp hs
  have hdomain : Module.finrank ℝ
      (SupportedBlockIndex p s → ℝ) = p * s - 1 := by
    rw [Module.finrank_pi]
    simp only [SupportedBlockIndex, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_prod]
    rw [Nat.sub_mul, one_mul]
    have hsps : s ≤ p * s := by
      simpa [one_mul] using Nat.mul_le_mul_right s hp
    omega
  rw [hrange, hdomain] at hdimension
  omega

/-- Complete real rank, kernel, and nonzero-eigenvalue ledger for the literal
supported block model. -/
theorem supportedBlockMatrixReal_spectrum_complete
    {p s : ℕ} (hp : 1 ≤ p) (hs : 2 ≤ s) :
    (supportedBlockMatrixReal p s).rank = p ∧
    Module.finrank ℝ (supportedBlockMatrixReal p s).mulVecLin.ker =
      p * s - p - 1 ∧
    (∀ c : Fin (p - 1),
      Matrix.mulVec (supportedBlockMatrixReal p s)
          (residueBlockVectorReal p s c) =
        (s : ℝ) • residueBlockVectorReal p s c) ∧
    Matrix.mulVec (supportedBlockMatrixReal p s)
        (terminatingBlockVectorReal p s) =
      ((s - 1 : ℕ) : ℝ) • terminatingBlockVectorReal p s ∧
    (∀ v : SupportedBlockIndex p s → ℝ,
      Matrix.mulVec (supportedBlockMatrixReal p s) v = 0 ↔
        (∑ i : Fin (s - 1), v (Sum.inl i) = 0) ∧
        (∀ c : Fin (p - 1),
          ∑ i : Fin s, v (Sum.inr (c, i)) = 0)) := by
  exact ⟨supportedBlockMatrixReal_rank_of_two_le hp hs,
    supportedBlockMatrixReal_kernel_finrank hp hs,
    supportedBlockMatrixReal_residue_eigenvector p s,
    supportedBlockMatrixReal_terminating_eigenvector p s,
    supportedBlockMatrixReal_mulVec_eq_zero_iff hs⟩

end NField.Alignment.SupportedBlockRealSpectrum
