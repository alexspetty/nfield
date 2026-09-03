/-
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Matrix.Spectrum
import NField.Alignment.CrossAlignmentMatrix
import NField.Alignment.SpectralStructure

/-!
# Hermitian spectral excess

This module proves the exact finite identity between squared displacement of
the eigenvalues from one and the off-diagonal square energy of a Hermitian
matrix with unit diagonal.  It is independent of any particular manuscript
or synchronized-matrix construction.
-/

namespace NField.Alignment.SpectralExcessIdentity

open scoped BigOperators
open Matrix
open Unitary
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CoherenceDecomposition

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact real off-diagonal square energy. -/
def realOffDiagonalSquareEnergy (A : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (A i j) ^ 2

/-- Centering a Hermitian matrix at the identity turns the trace of its square
into the sum of squared eigenvalue displacements. -/
theorem trace_centered_square_eq_eigenvalue_excess
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    Matrix.trace ((A - 1) * (A - 1)) =
      ∑ i, (hA.eigenvalues i - 1) ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply]
  let U := (hA.eigenvectorUnitary : Matrix n n ℝ)
  let D := Matrix.diagonal hA.eigenvalues
  change Matrix.trace (((U * D * star U) - 1) * ((U * D * star U) - 1)) = _
  have hcenter : U * D * star U - 1 = U * (D - 1) * star U := by
    rw [mul_sub, sub_mul]
    simp [U]
  rw [hcenter]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U]
  rw [show star U * U = 1 by simp [U]]
  simp only [one_mul]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [show star U * U = 1 by simp [U]]
  simp only [mul_one]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  change ((D - 1) * (D - 1)) i i = _
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [D, pow_two]
  · intro j hj hji
    simp [D, hji, Ne.symm hji]
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

/-- For a unit-diagonal Hermitian matrix, the centered square trace is exactly
the off-diagonal square energy. -/
theorem trace_centered_square_eq_offDiagonal
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 1) :
    Matrix.trace ((A - 1) * (A - 1)) =
      realOffDiagonalSquareEnergy A := by
  have hsym : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA
  unfold realOffDiagonalSquareEnergy
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, (A i j - (1 : Matrix n n ℝ) i j) *
      (A j i - (1 : Matrix n n ℝ) j i)) =
    ∑ j ∈ Finset.univ.erase i, (A i j) ^ 2
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [show (A i i - (1 : Matrix n n ℝ) i i) *
      (A i i - (1 : Matrix n n ℝ) i i) = 0 by simp [hdiag]]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [Matrix.one_apply_ne (Ne.symm hji), Matrix.one_apply_ne hji]
  rw [sub_zero, sub_zero, hsym.apply i j]
  ring

/-- The exact spectral-excess identity. -/
theorem spectral_excess_eq_offDiagonal
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 1) :
    ∑ i, (hA.eigenvalues i - 1) ^ 2 =
      realOffDiagonalSquareEnergy A := by
  rw [← trace_centered_square_eq_eigenvalue_excess A hA]
  exact trace_centered_square_eq_offDiagonal A hA hdiag

/-- Real off-diagonal square energy vanishes exactly when all off-diagonal
entries vanish. -/
theorem realOffDiagonalSquareEnergy_eq_zero_iff (A : Matrix n n ℝ) :
    realOffDiagonalSquareEnergy A = 0 ↔
      ∀ i j, i ≠ j → A i j = 0 := by
  constructor
  · intro hzero i j hij
    have houter := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i => ∑ j ∈ Finset.univ.erase i, (A i j) ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))).mp hzero
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ.erase i) (f := fun j => (A i j) ^ 2)
      (fun j _ => sq_nonneg (A i j))).mp
        (houter i (Finset.mem_univ i))
    have hsquare := hinner j
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    exact sq_eq_zero_iff.mp hsquare
  · intro hoff
    unfold realOffDiagonalSquareEnergy
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    rw [hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))]
    norm_num

/-- With unit diagonal, zero off-diagonal energy is exactly the identity
matrix. -/
theorem realOffDiagonalSquareEnergy_eq_zero_iff_matrix_one
    (A : Matrix n n ℝ) (hdiag : ∀ i, A i i = 1) :
    realOffDiagonalSquareEnergy A = 0 ↔ A = 1 := by
  rw [realOffDiagonalSquareEnergy_eq_zero_iff]
  constructor
  · intro hoff
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [hij, hoff i j hij]
  · intro hA i j hij
    rw [hA]
    simp [hij]

/-! ## The synchronized prime matrix -/

/-- Real scalar extension of the exact rational synchronized prime matrix. -/
noncomputable def primeCrossAlignmentMatrixReal
    (b p length : ℕ) : Matrix (PrimeResidue p) (PrimeResidue p) ℝ :=
  (primeCrossAlignmentMatrix b p length).map (Rat.castHom ℝ)

/-- The real synchronized prime matrix is Hermitian. -/
theorem primeCrossAlignmentMatrixReal_isHermitian
    (b p length : ℕ) :
    (primeCrossAlignmentMatrixReal b p length).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp [primeCrossAlignmentMatrixReal, primeCrossAlignmentMatrix,
    primePairPositionMatchCount, eq_comm]

/-- Every real synchronized prime-matrix diagonal entry is one on a positive
clock. -/
theorem primeCrossAlignmentMatrixReal_diagonal
    {b p length : ℕ} (hlength : 0 < length)
    (r : PrimeResidue p) :
    primeCrossAlignmentMatrixReal b p length r r = 1 := by
  simp [primeCrossAlignmentMatrixReal, primeCrossAlignmentMatrix,
    primePairPositionMatchCount_self, hlength.ne']

/-- Full eigenvalue/off-diagonal identity for the actual synchronized prime
matrix. -/
theorem primeCrossAlignmentMatrix_spectral_excess
    {b p length : ℕ} (hlength : 0 < length) :
    ∑ i, ((primeCrossAlignmentMatrixReal_isHermitian b p length).eigenvalues i -
        1) ^ 2 =
      realOffDiagonalSquareEnergy
        (primeCrossAlignmentMatrixReal b p length) := by
  exact spectral_excess_eq_offDiagonal _
    (primeCrossAlignmentMatrixReal_isHermitian b p length)
    (primeCrossAlignmentMatrixReal_diagonal hlength)

/-- The actual real spectral excess vanishes exactly at the sharp
digit-partitioning boundary. -/
theorem primeCrossAlignmentMatrix_realOffDiagonal_eq_zero_iff_le
    {b p length : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    realOffDiagonalSquareEnergy
        (primeCrossAlignmentMatrixReal b p length) = 0 ↔
      p ≤ b + 1 := by
  rw [realOffDiagonalSquareEnergy_eq_zero_iff_matrix_one _
    (primeCrossAlignmentMatrixReal_diagonal hlength)]
  constructor
  · intro hreal
    have hrat : primeCrossAlignmentMatrix b p length = 1 := by
      ext i j
      have hij := congrFun (congrFun hreal i) j
      simp only [primeCrossAlignmentMatrixReal, Matrix.map_apply,
        Matrix.one_apply] at hij
      change primeCrossAlignmentMatrix b p length i j =
        if i = j then 1 else 0
      by_cases heq : i = j
      · simp [heq] at hij ⊢
        exact_mod_cast hij
      · simp [heq] at hij ⊢
        exact_mod_cast hij
    exact (primeCrossAlignmentMatrix_eq_one_iff_le hb hp hpb hlength).mp hrat
  · intro hle
    have hrat : primeCrossAlignmentMatrix b p length = 1 :=
      (primeCrossAlignmentMatrix_eq_one_iff_le hb hp hpb hlength).mpr hle
    unfold primeCrossAlignmentMatrixReal
    rw [hrat]
    simp

end NField.Alignment.SpectralExcessIdentity
