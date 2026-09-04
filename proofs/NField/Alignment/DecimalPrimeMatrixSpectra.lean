/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DecimalOrbitSpectra
import NField.Alignment.PrimeCosetFourierSpectrum

/-!
# Exact decimal prime-matrix spectra

This module connects the concrete decimal orbit words to the literal
prime-residue cross-alignment matrices.  The residue orders are explicit
equivalences, so the finite spectral certificates apply to the actual
matrices rather than to detached word fixtures.
-/

namespace NField.Alignment.DecimalPrimeMatrixSpectra

open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CoherenceDecomposition
open NField.Alignment.DecimalOrbitSpectra

/-! ## The two decimal orbits modulo thirteen -/

/-- The natural residue represented by each coordinate of the two decimal
orbits modulo thirteen. -/
def decimalThirteenResidueValue : Sum (Fin 6) (Fin 6) → ℕ
  | Sum.inl r => ![1, 10, 9, 12, 3, 4] r
  | Sum.inr r => ![2, 7, 5, 11, 6, 8] r

/-- The displayed two-orbit ordering as actual positive residues modulo
thirteen. -/
def decimalThirteenResidueOrder
    (i : Sum (Fin 6) (Fin 6)) : PrimeResidue 13 :=
  ⟨decimalThirteenResidueValue i,
    by cases i with
       | inl r => fin_cases r <;> decide
       | inr r => fin_cases r <;> decide,
    by cases i with
       | inl r => fin_cases r <;> decide
       | inr r => fin_cases r <;> decide⟩

/-- Inverse lookup from a nonzero residue modulo thirteen to its displayed
orbit coordinate.  The fallback branch is unreachable on `PrimeResidue 13`.
-/
def decimalThirteenResidueCoordinate
    (r : PrimeResidue 13) : Sum (Fin 6) (Fin 6) :=
  match r.val with
  | 1 => Sum.inl 0
  | 10 => Sum.inl 1
  | 9 => Sum.inl 2
  | 12 => Sum.inl 3
  | 3 => Sum.inl 4
  | 4 => Sum.inl 5
  | 2 => Sum.inr 0
  | 7 => Sum.inr 1
  | 5 => Sum.inr 2
  | 11 => Sum.inr 3
  | 6 => Sum.inr 4
  | 8 => Sum.inr 5
  | _ => Sum.inl 0

theorem decimalThirteenResidueCoordinate_order
    (i : Sum (Fin 6) (Fin 6)) :
    decimalThirteenResidueCoordinate (decimalThirteenResidueOrder i) = i := by
  cases i with
  | inl r => fin_cases r <;> rfl
  | inr r => fin_cases r <;> rfl

theorem decimalThirteenResidueOrder_coordinate (r : PrimeResidue 13) :
    decimalThirteenResidueOrder (decimalThirteenResidueCoordinate r) = r := by
  apply Subtype.ext
  rcases r with ⟨r, hrpos, hrlt⟩
  change decimalThirteenResidueValue
      (decimalThirteenResidueCoordinate ⟨r, hrpos, hrlt⟩) = r
  interval_cases r <;>
    norm_num [decimalThirteenResidueCoordinate,
      decimalThirteenResidueValue] at hrpos hrlt ⊢ <;> decide

/-- Exact equivalence from the displayed orbit coordinates to all nonzero
natural residues modulo thirteen. -/
def decimalThirteenResidueEquiv :
    Sum (Fin 6) (Fin 6) ≃ PrimeResidue 13 where
  toFun := decimalThirteenResidueOrder
  invFun := decimalThirteenResidueCoordinate
  left_inv := decimalThirteenResidueCoordinate_order
  right_inv := decimalThirteenResidueOrder_coordinate

@[simp] theorem decimalThirteenResidueEquiv_apply
    (i : Sum (Fin 6) (Fin 6)) :
    decimalThirteenResidueEquiv i = decimalThirteenResidueOrder i :=
  rfl

/-- The orbit word attached to either displayed coordinate family modulo
thirteen. -/
def decimalThirteenOrbitWord
    (i : Sum (Fin 6) (Fin 6)) : Fin 6 → Fin 10 :=
  match i with
  | Sum.inl _ => decimalThirteenLeft
  | Sum.inr _ => decimalThirteenRight

/-- The cyclic phase attached to a displayed coordinate modulo thirteen. -/
def decimalThirteenOrbitPhase
    (i : Sum (Fin 6) (Fin 6)) : Fin 6 :=
  match i with
  | Sum.inl r => r
  | Sum.inr r => r

/-- Every digit emitted from an explicitly ordered residue is the displayed
orbit word at the translated common-clock coordinate. -/
theorem digitAt_decimalThirteenResidueOrder
    (i : Sum (Fin 6) (Fin 6)) (position : Fin 6) :
    digitAt 10 13 (decimalThirteenResidueOrder i).val position.val =
      (decimalThirteenOrbitWord i
        (position + decimalThirteenOrbitPhase i)).val := by
  cases i with
  | inl r =>
      fin_cases r <;> fin_cases position <;> decide
  | inr r =>
      fin_cases r <;> fin_cases position <;> decide

/-- Literal position matching on the prime residue clock equals matching in
the displayed two-word orbit coordinates. -/
theorem decimalThirteen_primePairPositionMatchCount_eq_orbitMatchCount
    (i j : Sum (Fin 6) (Fin 6)) :
    primePairPositionMatchCount 10 13
        (decimalThirteenResidueOrder i).val
        (decimalThirteenResidueOrder j).val 6 =
      orbitMatchCount (decimalThirteenOrbitWord i)
        (decimalThirteenOrbitWord j)
        (decimalThirteenOrbitPhase i) (decimalThirteenOrbitPhase j) := by
  classical
  unfold primePairPositionMatchCount orbitMatchCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro position _
  rw [digitAt_decimalThirteenResidueOrder i position,
    digitAt_decimalThirteenResidueOrder j position]
  simp only [Fin.val_inj]

/-- In the explicit residue order, the literal decimal prime matrix is
exactly the two-word matrix used by the spectral certificate. -/
theorem decimalThirteen_primeMatrix_reindex :
    Matrix.reindex decimalThirteenResidueEquiv.symm
        decimalThirteenResidueEquiv.symm
        (primeCrossAlignmentMatrix 10 13 6) =
      decimalThirteenMatrix := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    decimalThirteenResidueEquiv_apply, primeCrossAlignmentMatrix]
  rw [decimalThirteen_primePairPositionMatchCount_eq_orbitMatchCount]
  cases i <;> cases j <;> rfl

/-! ## The primitive decimal orbit modulo seventeen -/

/-- The powers of ten modulo seventeen, in exponent order. -/
def decimalSeventeenResidueValue : Fin 16 → ℕ :=
  ![1, 10, 15, 14, 4, 6, 9, 5, 16, 7, 2, 3, 13, 11, 8, 12]

/-- The displayed primitive-orbit ordering as actual positive residues
modulo seventeen. -/
def decimalSeventeenResidueOrder (r : Fin 16) : PrimeResidue 17 :=
  ⟨decimalSeventeenResidueValue r,
    by fin_cases r <;> decide,
    by fin_cases r <;> decide⟩

/-- Inverse lookup from a nonzero residue modulo seventeen to its exponent in
the displayed primitive orbit.  The fallback branch is unreachable on
`PrimeResidue 17`. -/
def decimalSeventeenResidueCoordinate (r : PrimeResidue 17) : Fin 16 :=
  match r.val with
  | 1 => 0
  | 10 => 1
  | 15 => 2
  | 14 => 3
  | 4 => 4
  | 6 => 5
  | 9 => 6
  | 5 => 7
  | 16 => 8
  | 7 => 9
  | 2 => 10
  | 3 => 11
  | 13 => 12
  | 11 => 13
  | 8 => 14
  | 12 => 15
  | _ => 0

theorem decimalSeventeenResidueCoordinate_order (r : Fin 16) :
    decimalSeventeenResidueCoordinate (decimalSeventeenResidueOrder r) = r := by
  fin_cases r <;> rfl

theorem decimalSeventeenResidueOrder_coordinate (r : PrimeResidue 17) :
    decimalSeventeenResidueOrder (decimalSeventeenResidueCoordinate r) = r := by
  apply Subtype.ext
  rcases r with ⟨r, hrpos, hrlt⟩
  change decimalSeventeenResidueValue
      (decimalSeventeenResidueCoordinate ⟨r, hrpos, hrlt⟩) = r
  interval_cases r <;>
    norm_num [decimalSeventeenResidueCoordinate,
      decimalSeventeenResidueValue] at hrpos hrlt ⊢ <;> decide

/-- Exact equivalence from the primitive-orbit coordinate to all nonzero
natural residues modulo seventeen. -/
def decimalSeventeenResidueEquiv : Fin 16 ≃ PrimeResidue 17 where
  toFun := decimalSeventeenResidueOrder
  invFun := decimalSeventeenResidueCoordinate
  left_inv := decimalSeventeenResidueCoordinate_order
  right_inv := decimalSeventeenResidueOrder_coordinate

@[simp] theorem decimalSeventeenResidueEquiv_apply (r : Fin 16) :
    decimalSeventeenResidueEquiv r = decimalSeventeenResidueOrder r :=
  rfl

/-- Every digit emitted from the primitive residue order is the displayed
word at the translated common-clock coordinate. -/
theorem digitAt_decimalSeventeenResidueOrder
    (r position : Fin 16) :
    digitAt 10 17 (decimalSeventeenResidueOrder r).val position.val =
      (decimalSeventeenWord (position + r)).val := by
  fin_cases r <;> fin_cases position <;> decide

/-- Literal position matching on the prime residue clock equals matching in
the displayed primitive-orbit word. -/
theorem decimalSeventeen_primePairPositionMatchCount_eq_orbitMatchCount
    (r s : Fin 16) :
    primePairPositionMatchCount 10 17
        (decimalSeventeenResidueOrder r).val
        (decimalSeventeenResidueOrder s).val 16 =
      orbitMatchCount decimalSeventeenWord decimalSeventeenWord r s := by
  classical
  unfold primePairPositionMatchCount orbitMatchCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro position _
  rw [digitAt_decimalSeventeenResidueOrder r position,
    digitAt_decimalSeventeenResidueOrder s position]
  simp only [Fin.val_inj]

/-- In exponent order, the literal decimal prime matrix is exactly the
circulant word matrix used by the autocorrelation certificate. -/
theorem decimalSeventeen_primeMatrix_reindex :
    Matrix.reindex decimalSeventeenResidueEquiv.symm
        decimalSeventeenResidueEquiv.symm
        (primeCrossAlignmentMatrix 10 17 16) =
      orbitMatrix decimalSeventeenWord decimalSeventeenWord := by
  ext r s
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    decimalSeventeenResidueEquiv_apply, primeCrossAlignmentMatrix,
    orbitMatrix]
  rw [decimalSeventeen_primePairPositionMatchCount_eq_orbitMatchCount]
  rfl

end NField.Alignment.DecimalPrimeMatrixSpectra
