/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.UpwardMobius
/-! # General reset masks on the complete source space -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ResetMasks

open scoped BigOperators Matrix
open SourceMetrics

theorem reset_source_injective (N : ℕ) : Function.Injective (resetMatrix N).mulVec := by
  intro c e he
  have h := congrArg (fun v => mobiusMatrix N *ᵥ v) he
  simpa only [Matrix.mulVec_mulVec, reset_mobius_left, Matrix.one_mulVec] using h

theorem reset_mask_mass (N : ℕ) (σ c : Fin N → ℝ) (k : Fin N) :
    Core.resetMass N (cutoffCoefficients N (resetMaskMatrix N σ *ᵥ c)) (k.val+1)=
      σ k*Core.resetMass N (cutoffCoefficients N c) (k.val+1) := by
  rw [← reset_matrix_reading, ← reset_matrix_reading, reset_mask_reading]

theorem reset_mask_source_unique (N : ℕ) (σ c e : Fin N → ℝ)
    (he : ∀ k : Fin N, Core.resetMass N (cutoffCoefficients N e) (k.val+1)=
      σ k*Core.resetMass N (cutoffCoefficients N c) (k.val+1)) :
    e=resetMaskMatrix N σ *ᵥ c := by
  apply reset_source_injective N
  funext k
  rw [reset_mask_reading, reset_matrix_reading, reset_matrix_reading]
  exact he k

theorem reset_mask_add (N : ℕ) (σ τ : Fin N → ℝ) :
    resetMaskMatrix N σ+resetMaskMatrix N τ=resetMaskMatrix N (σ+τ) := by
  apply reset_mask_unique
  rw [Matrix.mul_add, reset_mask_identity, reset_mask_identity,
    ← Matrix.add_mul]
  change (Matrix.diagonal σ+Matrix.diagonal τ)*resetMatrix N=
    Matrix.diagonal (fun i => σ i+τ i)*resetMatrix N
  rw [Matrix.diagonal_add]

theorem reset_mask_one (N : ℕ) : resetMaskMatrix N (fun _ => 1)=1 := by
  symm
  apply reset_mask_unique
  simp

theorem reset_mask_complement (N : ℕ) (σ : Fin N → ℝ) :
    resetMaskMatrix N σ+resetMaskMatrix N (fun k => 1-σ k)=1 := by
  rw [reset_mask_add]
  have he : σ+(fun k => 1-σ k)=fun _ => (1 : ℝ) := by funext k; simp
  rw [he, reset_mask_one]

theorem reset_mask_compose (N : ℕ) (σ τ : Fin N → ℝ) :
    resetMaskMatrix N σ*resetMaskMatrix N τ=resetMaskMatrix N (σ*τ) := by
  apply reset_mask_unique
  rw [← Matrix.mul_assoc, reset_mask_identity, Matrix.mul_assoc, reset_mask_identity,
    ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  rfl

end NField.ResetForests.ResetMasks
