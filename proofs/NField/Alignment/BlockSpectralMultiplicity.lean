/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConcreteCollisionBlocks

/-! Exact characteristic-polynomial and spectral multiplicities of the full matrix. -/

namespace NField.Alignment.BlockSpectralMultiplicity

open scoped BigOperators
open Matrix Polynomial

noncomputable def hamiltonian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 - A) ^ 2

theorem compressed_hamiltonian {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (Q : Matrix κ κ ℝ) (hU : Uᵀ * U = 1) :
    hamiltonian (U * Q * Uᵀ) = 1 + U * (hamiltonian Q - 1) * Uᵀ := by
  have hs : (U * Q * Uᵀ) * (U * Q * Uᵀ) = U * (Q * Q) * Uᵀ := calc
    _ = U * Q * (Uᵀ * U) * Q * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hT : hamiltonian Q - 1 = Q * Q - (Q + Q) := by
    unfold hamiltonian
    noncomm_ring
  rw [hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, ← hs]
  unfold hamiltonian
  noncomm_ring

theorem charpoly_add_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : (1 + A).charpoly = A.charpoly.comp (X - 1) := by
  have h := Matrix.charpoly_sub_scalar A (-1)
  simpa [Matrix.scalar, Matrix.diagonal_neg, Matrix.diagonal_one, sub_eq_add_neg, add_comm] using h

theorem charpoly_hamiltonian_compression {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (Q : Matrix κ κ ℝ) (hU : Uᵀ * U = 1)
    (hcard : Fintype.card κ ≤ Fintype.card ι) :
    (hamiltonian (U * Q * Uᵀ)).charpoly =
      (X - 1) ^ (Fintype.card ι - Fintype.card κ) * (hamiltonian Q).charpoly := by
  rw [compressed_hamiltonian U Q hU, charpoly_add_one,
    Matrix.charpoly_mul_comm_of_le (U * (hamiltonian Q - 1)) Uᵀ hcard]
  have hsmall : Uᵀ * (U * (hamiltonian Q - 1)) = hamiltonian Q - 1 := by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [hsmall, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
  have hshift := charpoly_add_one (hamiltonian Q - 1)
  have hcancel : 1 + (hamiltonian Q - 1) = hamiltonian Q := by abel
  rw [hcancel] at hshift
  rw [← hshift]

theorem hamiltonian_spectral_multiset {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (Q : Matrix κ κ ℝ) (hU : Uᵀ * U = 1)
    (hcard : Fintype.card κ ≤ Fintype.card ι) :
    (hamiltonian (U * Q * Uᵀ)).charpoly.roots =
      (Fintype.card ι - Fintype.card κ) • ({1} : Multiset ℝ) +
        (hamiltonian Q).charpoly.roots := by
  rw [charpoly_hamiltonian_compression U Q hU hcard, Polynomial.roots_mul,
    Polynomial.roots_pow]
  · simp only [← Polynomial.C_1, Polynomial.roots_X_sub_C]
  · exact mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)) (Matrix.charpoly_monic _).ne_zero

theorem hamiltonian_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : (hamiltonian A).IsHermitian :=
  (Matrix.isHermitian_one.sub hA).pow 2

/-- Title: `The full spectrum splits into quotient modes and bulk ones`.

The literal particle Hamiltonian has exactly the quotient spectrum and the bulk ones. -/
theorem particle_spectral_multiset {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (label : ι → Fin (n + 1)) (hsurj : Function.Surjective label)
    (x : Fin (n + 1) → ℝ) (τ : ℝ) :
    (hamiltonian (ConcreteCollisionBlocks.particleNormalized label x τ)).charpoly.roots =
      (Fintype.card ι - (n + 1)) • ({1} : Multiset ℝ) +
        (hamiltonian (ExponentialSpectralQuotient.quotient x
          (ConcreteCollisionBlocks.population label) τ)).charpoly.roots := by
  rw [ConcreteCollisionBlocks.particleNormalized_factor label hsurj x τ]
  simpa only [Fintype.card_fin] using hamiltonian_spectral_multiset
    (ConcreteCollisionBlocks.blockEmbedding label) _
    (ConcreteCollisionBlocks.blockEmbedding_orthonormal label hsurj)
    (Fintype.card_le_of_surjective label hsurj)

end NField.Alignment.BlockSpectralMultiplicity
