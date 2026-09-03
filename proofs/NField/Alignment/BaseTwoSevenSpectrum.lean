/-
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralStructure

/-!
# Exact base-two spectrum modulo seven

This title-independent module connects the literal long-division matrix for
base two modulo seven to an exact rational diagonalization.  The two zero
directions and four nonzero directions prove the sharp rank and nullity
values without a numerical eigensolver.
-/

namespace NField.Alignment.BaseTwoSevenSpectrum

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CoherenceDecomposition

/-- Multiplicative-orbit order `1,2,4,3,6,5` modulo seven. -/
def baseTwoSevenResidueValue : Fin 6 → ℕ := ![1, 2, 4, 3, 6, 5]

def baseTwoSevenResidueOrder (i : Fin 6) : PrimeResidue 7 :=
  ⟨baseTwoSevenResidueValue i, by fin_cases i <;> decide,
    by fin_cases i <;> decide⟩

def baseTwoSevenResidueCoordinate (r : PrimeResidue 7) : Fin 6 :=
  match r.val with
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | 3 => 3
  | 6 => 4
  | 5 => 5
  | _ => 0

theorem baseTwoSevenResidueCoordinate_order (i : Fin 6) :
    baseTwoSevenResidueCoordinate (baseTwoSevenResidueOrder i) = i := by
  fin_cases i <;> rfl

theorem baseTwoSevenResidueOrder_coordinate (r : PrimeResidue 7) :
    baseTwoSevenResidueOrder (baseTwoSevenResidueCoordinate r) = r := by
  apply Subtype.ext
  rcases r with ⟨r, hrpos, hrlt⟩
  change baseTwoSevenResidueValue
      (baseTwoSevenResidueCoordinate ⟨r, hrpos, hrlt⟩) = r
  interval_cases r <;>
    norm_num [baseTwoSevenResidueCoordinate,
      baseTwoSevenResidueValue] at hrpos hrlt ⊢ <;> decide

/-- Exact equivalence from orbit order to all six positive residues. -/
def baseTwoSevenResidueEquiv : Fin 6 ≃ PrimeResidue 7 where
  toFun := baseTwoSevenResidueOrder
  invFun := baseTwoSevenResidueCoordinate
  left_inv := baseTwoSevenResidueCoordinate_order
  right_inv := baseTwoSevenResidueOrder_coordinate

/-- Exact rational matrix in multiplicative-orbit order. -/
def baseTwoSevenMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  ![![1, 1/3, 1/3, 2/3, 0, 2/3],
    ![1/3, 1, 1/3, 2/3, 2/3, 0],
    ![1/3, 1/3, 1, 0, 2/3, 2/3],
    ![2/3, 2/3, 0, 1, 1/3, 1/3],
    ![0, 2/3, 2/3, 1/3, 1, 1/3],
    ![2/3, 0, 2/3, 1/3, 1/3, 1]]

/-- The explicit matrix is the literal synchronized prime matrix, not a
detached fixture. -/
theorem baseTwoSeven_primeMatrix_reindex :
    Matrix.reindex baseTwoSevenResidueEquiv.symm
        baseTwoSevenResidueEquiv.symm
        (primeCrossAlignmentMatrix 2 7 3) = baseTwoSevenMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseTwoSevenResidueEquiv, baseTwoSevenResidueOrder,
      baseTwoSevenResidueValue, baseTwoSevenMatrix,
      primeCrossAlignmentMatrix, primePairPositionMatchCount, digitAt,
      NField.CollisionDefinition.digitBin, Finset.filter,
      Finset.card_filter, Fin.sum_univ_succ] <;>
    simp [Multiset.filter_singleton] <;> norm_num

/-- Columns are exact eigenvectors in the order
`0,0,1/3,4/3,4/3,3`. -/
def baseTwoSevenChangeOfBasis : Matrix (Fin 6) (Fin 6) ℚ :=
  ![![1, 0, -1, -1, 0, 1],
    ![0, 1, -1, 0, -1, 1],
    ![-1, -1, -1, 1, 1, 1],
    ![-1, -1, 1, -1, -1, 1],
    ![1, 0, 1, 1, 0, 1],
    ![0, 1, 1, 0, 1, 1]]

def baseTwoSevenChangeOfBasisInverse : Matrix (Fin 6) (Fin 6) ℚ :=
  ![![1/3, -1/6, -1/6, -1/6, 1/3, -1/6],
    ![-1/6, 1/3, -1/6, -1/6, -1/6, 1/3],
    ![-1/6, -1/6, -1/6, 1/6, 1/6, 1/6],
    ![-1/3, 1/6, 1/6, -1/6, 1/3, -1/6],
    ![1/6, -1/3, 1/6, -1/6, -1/6, 1/3],
    ![1/6, 1/6, 1/6, 1/6, 1/6, 1/6]]

theorem baseTwoSevenChangeOfBasis_mul_inverse :
    baseTwoSevenChangeOfBasis * baseTwoSevenChangeOfBasisInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseTwoSevenChangeOfBasis,
      baseTwoSevenChangeOfBasisInverse, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem baseTwoSevenChangeOfBasis_inverse_mul :
    baseTwoSevenChangeOfBasisInverse * baseTwoSevenChangeOfBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseTwoSevenChangeOfBasis,
      baseTwoSevenChangeOfBasisInverse, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ, Matrix.one_apply]

def baseTwoSevenChangeOfBasisUnit :
    (Matrix (Fin 6) (Fin 6) ℚ)ˣ where
  val := baseTwoSevenChangeOfBasis
  inv := baseTwoSevenChangeOfBasisInverse
  val_inv := baseTwoSevenChangeOfBasis_mul_inverse
  inv_val := baseTwoSevenChangeOfBasis_inverse_mul

def baseTwoSevenEigenvalueDiagonal : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.diagonal ![0, 0, 1/3, 4/3, 4/3, 3]

/-- Exact diagonalization equation. -/
theorem baseTwoSevenMatrix_diagonalization :
    baseTwoSevenMatrix * baseTwoSevenChangeOfBasis =
      baseTwoSevenChangeOfBasis * baseTwoSevenEigenvalueDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseTwoSevenMatrix, baseTwoSevenChangeOfBasis,
      baseTwoSevenEigenvalueDiagonal, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem baseTwoSevenEigenvalueDiagonal_rank :
    baseTwoSevenEigenvalueDiagonal.rank = 4 := by
  unfold baseTwoSevenEigenvalueDiagonal
  rw [Matrix.rank_diagonal]
  rw [Fintype.card_of_subtype ({2, 3, 4, 5} : Finset (Fin 6))]
  · decide
  · intro i
    fin_cases i <;> norm_num <;> decide

theorem baseTwoSevenMatrix_rank : baseTwoSevenMatrix.rank = 4 := by
  have hP : IsUnit baseTwoSevenChangeOfBasis :=
    ⟨baseTwoSevenChangeOfBasisUnit, rfl⟩
  have hPdet : IsUnit baseTwoSevenChangeOfBasis.det :=
    (Matrix.isUnit_iff_isUnit_det baseTwoSevenChangeOfBasis).mp hP
  calc
    baseTwoSevenMatrix.rank =
        (baseTwoSevenMatrix * baseTwoSevenChangeOfBasis).rank :=
      (Matrix.rank_mul_eq_left_of_isUnit_det
        baseTwoSevenChangeOfBasis baseTwoSevenMatrix hPdet).symm
    _ = (baseTwoSevenChangeOfBasis *
        baseTwoSevenEigenvalueDiagonal).rank := by
      rw [baseTwoSevenMatrix_diagonalization]
    _ = baseTwoSevenEigenvalueDiagonal.rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det
        baseTwoSevenChangeOfBasis baseTwoSevenEigenvalueDiagonal hPdet
    _ = 4 := baseTwoSevenEigenvalueDiagonal_rank

/-- Actual literal rank, invariant under the explicit residue reindexing. -/
theorem baseTwoSeven_primeMatrix_rank :
    (primeCrossAlignmentMatrix 2 7 3).rank = 4 := by
  rw [← Matrix.rank_reindex baseTwoSevenResidueEquiv.symm
    baseTwoSevenResidueEquiv.symm (primeCrossAlignmentMatrix 2 7 3)]
  rw [baseTwoSeven_primeMatrix_reindex]
  exact baseTwoSevenMatrix_rank

/-- Actual literal nullity. -/
theorem baseTwoSeven_primeMatrix_nullity :
    Module.finrank ℚ
      (primeCrossAlignmentMatrix 2 7 3).mulVecLin.ker = 2 := by
  let A := primeCrossAlignmentMatrix 2 7 3
  have hrank : A.rank = 4 := by
    simpa [A] using baseTwoSeven_primeMatrix_rank
  have hcard : Fintype.card (PrimeResidue 7) = 6 := by
    simpa using (Fintype.card_congr baseTwoSevenResidueEquiv).symm
  have hdim : A.rank + Module.finrank ℚ A.mulVecLin.ker = 6 := by
    simpa [Matrix.rank, hcard] using
      A.mulVecLin.finrank_range_add_finrank_ker
  rw [hrank] at hdim
  change Module.finrank ℚ A.mulVecLin.ker = 2
  omega

/-- Sharpness packet for the literal matrix. -/
theorem baseTwoSeven_actual_rank_nullity :
    (primeCrossAlignmentMatrix 2 7 3).rank = 4 ∧
      Module.finrank ℚ
        (primeCrossAlignmentMatrix 2 7 3).mulVecLin.ker = 2 :=
  ⟨baseTwoSeven_primeMatrix_rank, baseTwoSeven_primeMatrix_nullity⟩

end NField.Alignment.BaseTwoSevenSpectrum
