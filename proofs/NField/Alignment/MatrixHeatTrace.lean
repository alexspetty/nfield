/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BlockSpectralMultiplicity
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! Actual matrix exponentials, the spectral multiset, and the heat trace. -/

namespace NField.Alignment.MatrixHeatTrace

open scoped BigOperators
open Matrix Polynomial Unitary BlockSpectralMultiplicity

theorem charpoly_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).charpoly = A.charpoly := by
  change ((U : Matrix ι ι ℝ) * A * (star U : Matrix ι ι ℝ)).charpoly = A.charpoly
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem trace_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).trace = A.trace := by
  change ((U : Matrix ι ι ℝ) * A * (star U : Matrix ι ι ℝ)).trace = A.trace
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem exp_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    NormedSpace.exp (conjStarAlgAut ℝ _ U A) =
      conjStarAlgAut ℝ _ U (NormedSpace.exp A) :=
  Matrix.exp_units_conj (Unitary.toUnits U) A

theorem hamiltonian_diagonalization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    hamiltonian A = conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal (fun i => (1 - hA.eigenvalues i) ^ 2)) := by
  have hd : hamiltonian (diagonal hA.eigenvalues) =
      diagonal (fun i => (1 - hA.eigenvalues i) ^ 2) := by
    rw [hamiltonian, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_pow]
    rfl
  rw [← hd]
  simp only [hamiltonian, map_pow, map_sub, map_one]
  congr 2
  simpa using hA.spectral_theorem

theorem hamiltonian_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (hamiltonian A).charpoly = ∏ i, (X - C ((1 - hA.eigenvalues i) ^ 2)) := by
  rw [hamiltonian_diagonalization hA, charpoly_unitary_conj, Matrix.charpoly_diagonal]

theorem hamiltonian_roots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (hamiltonian A).charpoly.roots =
      Finset.univ.val.map (fun i => (1 - hA.eigenvalues i) ^ 2) := by
  rw [hamiltonian_charpoly hA, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr (fun i hi => Polynomial.X_sub_C_ne_zero _)

/-- The trace is the sum of the literal exponentials of all eigenvalues, with multiplicity. -/
theorem trace_exp_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (t : ℝ) :
    (NormedSpace.exp (t • A)).trace = ∑ i, Real.exp (t * hA.eigenvalues i) := by
  have hs := hA.spectral_theorem
  have heq : t • A = conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal (fun i => t * hA.eigenvalues i)) := by
    have hd : diagonal (fun i => t * hA.eigenvalues i) = t • diagonal hA.eigenvalues := by
      simp only [← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul]
    rw [hd, map_smul]
    congr 1
  rw [heq, exp_unitary_conj, trace_unitary_conj, Matrix.exp_diagonal, Matrix.trace_diagonal]
  simp only [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]

theorem trace_exp_eq_sum_roots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (t : ℝ) :
    (NormedSpace.exp (t • A)).trace =
      (A.charpoly.roots.map (fun μ => Real.exp (t * μ))).sum := by
  rw [trace_exp_eq_sum_eigenvalues hA t, hA.roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_map, Function.comp_def]

end NField.Alignment.MatrixHeatTrace
