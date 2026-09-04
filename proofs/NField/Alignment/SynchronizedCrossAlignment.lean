/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import NField.Alignment.CanonicalSynchronizedAlignment
import NField.Alignment.SynchronizedPairwiseAlignment

/-!
# Synchronized cross-alignment

This module gives the literal finite matrix attached to all positive proper
fractions with a common denominator.  Its entries use the common clearing
depth and the full rough-part period.  The construction is independent of the
chosen valid clearing depth and is exactly a normalized Gram matrix of
terminating and digit-position feature vectors.
-/

namespace NField.Alignment.SynchronizedCrossAlignment

open scoped BigOperators
open NField.Alignment
open NField.Alignment.ThreeTier
open NField.Alignment.SynchronizedPairwiseAlignment

/-- An index for one of the positive proper numerators `1, ..., n - 1`. -/
abbrev ProperNumerator (n : ℕ) := Fin (n - 1)

/-- The natural numerator represented by a zero-based matrix index. -/
def numeratorValue {n : ℕ} (i : ProperNumerator n) : ℕ := i.val + 1

theorem numeratorValue_pos {n : ℕ} (i : ProperNumerator n) :
    0 < numeratorValue i := by
  simp [numeratorValue]

theorem numeratorValue_lt {n : ℕ} (hn : 2 ≤ n) (i : ProperNumerator n) :
    numeratorValue i < n := by
  simp only [numeratorValue]
  omega

/-- Equality of two literal digits after a shared clearing depth. -/
def clearedPairMatchAt
    (b n D : ℕ) (i j : ProperNumerator n) (position : ℕ) : Prop :=
  clearedDigit b n (numeratorValue i) D position =
    clearedDigit b n (numeratorValue j) D position

/-- Number of positions at which two proper numerators have equal digits on
the common post-clearing window. -/
noncomputable def clearedPairMatchCount
    (b n D L : ℕ) (i j : ProperNumerator n) : ℕ := by
  classical
  exact ((Finset.range L).filter (clearedPairMatchAt b n D i j)).card

/-- Literal synchronized cross-alignment matrix.  Divisibility by the rough
part is the exact termination marker once `n = q * s`, `s` is supported, and
`q` is coprime to the base. -/
noncomputable def synchronizedCrossAlignmentMatrix
    (b n q D L : ℕ) : Matrix (ProperNumerator n)
      (ProperNumerator n) ℝ :=
  fun i j =>
    if q ∣ numeratorValue i then
      if q ∣ numeratorValue j then 1 else 0
    else if q ∣ numeratorValue j then 0
    else (clearedPairMatchCount b n D L i j : ℝ) / L

/-- The literal digit count reduces to the rough-residue count after any
valid common clearing depth. -/
theorem clearedPairMatchCount_eq_periodic
    {b q s D L : ℕ} (hs : 0 < s) (hD : s ∣ b ^ D)
    (i j : ProperNumerator (q * s)) :
    clearedPairMatchCount b (q * s) D L i j =
      periodicPairMatchCount b q (clearingCofactor b s D)
        (numeratorValue i % q) (numeratorValue j % q) L := by
  classical
  unfold clearedPairMatchCount periodicPairMatchCount
  congr 1
  ext position
  simp only [Finset.mem_filter, Finset.mem_range, clearedPairMatchAt,
    periodicPairMatchAt]
  rw [clearedDigit_eq_periodicDigit hs hD,
    clearedDigit_eq_periodicDigit hs hD]

/-- Every matrix entry is independent of the valid clearing depth. -/
theorem synchronizedCrossAlignmentMatrix_independent_of_clearing_depth
    {b q s D E L : ℕ} (hs : 0 < s)
    (hD : s ∣ b ^ D) (hE : s ∣ b ^ E)
    (hperiod : b ^ L % q = 1 % q) :
    synchronizedCrossAlignmentMatrix b (q * s) q D L =
      synchronizedCrossAlignmentMatrix b (q * s) q E L := by
  ext i j
  unfold synchronizedCrossAlignmentMatrix
  split_ifs with hi hj hj
  · rfl
  · rfl
  · rfl
  · congr 1
    norm_cast
    rw [clearedPairMatchCount_eq_periodic hs hD,
      clearedPairMatchCount_eq_periodic hs hE]
    calc
      periodicPairMatchCount b q (clearingCofactor b s D)
          (numeratorValue i % q) (numeratorValue j % q) L =
          periodicPairMatchCount b q (clearingCofactor b s (D + E))
            (numeratorValue i % q) (numeratorValue j % q) L :=
        (periodicPairMatchCount_independent_of_later_clearing_depth
          hD hperiod).symm
      _ = periodicPairMatchCount b q (clearingCofactor b s (E + D))
            (numeratorValue i % q) (numeratorValue j % q) L := by
        rw [Nat.add_comm D E]
      _ = periodicPairMatchCount b q (clearingCofactor b s E)
            (numeratorValue i % q) (numeratorValue j % q) L :=
        periodicPairMatchCount_independent_of_later_clearing_depth
          hE hperiod

/-- Denominator-indexed form of clearing-depth independence. -/
theorem synchronizedCrossAlignmentMatrix_independent_of_clearing_depth_of_eq
    {b n q s D E L : ℕ} (hfactor : n = q * s) (hs : 0 < s)
    (hD : s ∣ b ^ D) (hE : s ∣ b ^ E)
    (hperiod : b ^ L % q = 1 % q) :
    synchronizedCrossAlignmentMatrix b n q D L =
      synchronizedCrossAlignmentMatrix b n q E L := by
  subst n
  exact synchronizedCrossAlignmentMatrix_independent_of_clearing_depth
    hs hD hE hperiod

/-- The synchronized matrix is symmetric entrywise. -/
theorem synchronizedCrossAlignmentMatrix_isSymm
    (b n q D L : ℕ) :
    (synchronizedCrossAlignmentMatrix b n q D L).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold synchronizedCrossAlignmentMatrix
  by_cases hi : q ∣ numeratorValue i
  · by_cases hj : q ∣ numeratorValue j <;> simp [hi, hj]
  · by_cases hj : q ∣ numeratorValue j
    · simp [hi, hj]
    · simp only [hi, hj, ↓reduceIte]
      congr 1
      norm_cast
      unfold clearedPairMatchCount clearedPairMatchAt
      congr 1
      ext position
      simp [eq_comm]

/-- Every literal self-comparison fills the whole common window. -/
theorem clearedPairMatchCount_self
    (b n D L : ℕ) (i : ProperNumerator n) :
    clearedPairMatchCount b n D L i i = L := by
  simp [clearedPairMatchCount, clearedPairMatchAt]

/-- A positive common window gives unit diagonal. -/
theorem synchronizedCrossAlignmentMatrix_diagonal
    {b n q D L : ℕ} (hL : 0 < L) (i : ProperNumerator n) :
    synchronizedCrossAlignmentMatrix b n q D L i i = 1 := by
  unfold synchronizedCrossAlignmentMatrix
  by_cases hi : q ∣ numeratorValue i
  · simp [hi]
  · simp [hi, clearedPairMatchCount_self, hL.ne']

/-! ## Literal Gram realization -/

/-- Every literal post-clearing digit is a valid base-`b` digit. -/
theorem clearedDigit_lt_base {b n k D position : ℕ}
    (hb : 0 < b) (hn : 0 < n) :
    clearedDigit b n k D position < b := by
  unfold clearedDigit NField.Alignment.digitAt
  exact digitBin_lt_base hb hn (Nat.mod_lt _ hn)

/-- Summing two one-hot digit coordinates records precisely whether the two
digits agree. -/
theorem sum_digit_indicators {b x y : ℕ} (hx : x < b) (hy : y < b) :
    (∑ d : Fin b,
      (if x = d.val then (1 : ℝ) else 0) *
        if y = d.val then (1 : ℝ) else 0) =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    let dx : Fin b := ⟨x, hx⟩
    rw [Finset.sum_eq_single dx]
    · simp [dx]
    · intro d _ hdx
      have hne : x ≠ d.val := by
        intro h
        apply hdx
        apply Fin.ext
        exact h.symm
      simp [hne]
    · simp
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hxd : x = d.val
    · have hyd : y ≠ d.val := by
        intro hyd
        exact hxy (hxd.trans hyd.symm)
      simp [hxd, hyd]
    · simp [hxd]

/-- Unnormalized feature vector.  Terminating fractions receive a vector of
length `sqrt L`; nonterminating fractions receive one unit digit coordinate
at each of the `L` positions.  A final factor `1/L` normalizes both cases. -/
noncomputable def synchronizedFeature
    (b n q D L : ℕ) (i : ProperNumerator n) :
    EuclideanSpace ℝ (Option (Fin L × Fin b)) := by
  classical
  exact WithLp.toLp 2 fun coordinate =>
    match coordinate with
    | none => if q ∣ numeratorValue i then Real.sqrt L else 0
    | some td =>
        if q ∣ numeratorValue i then 0
        else if clearedDigit b n (numeratorValue i) D td.1.val = td.2.val
          then 1 else 0

/-- The feature inner product is `L` for two terminating numerators, zero for
a mixed pair, and the literal digit-match count for two nonterminating
numerators. -/
theorem inner_synchronizedFeature
    {b n q D L : ℕ} (hb : 0 < b) (hn : 0 < n)
    (i j : ProperNumerator n) :
    inner ℝ (synchronizedFeature b n q D L i)
        (synchronizedFeature b n q D L j) =
      if q ∣ numeratorValue i then
        if q ∣ numeratorValue j then L else 0
      else if q ∣ numeratorValue j then 0
      else clearedPairMatchCount b n D L i j := by
  classical
  by_cases hi : q ∣ numeratorValue i
  · by_cases hj : q ∣ numeratorValue j
    · simp only [synchronizedFeature, hi, hj, ↓reduceIte,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        Fintype.sum_option,
        star_id_of_comm, zero_mul, Finset.sum_const_zero,
        add_zero]
      rw [Real.mul_self_sqrt]
      norm_cast
      positivity
    · simp [synchronizedFeature, hi, hj,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        Fintype.sum_option]
  · by_cases hj : q ∣ numeratorValue j
    · simp [synchronizedFeature, hi, hj,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        Fintype.sum_option]
    · simp only [synchronizedFeature, hi, hj, ↓reduceIte,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        Fintype.sum_option,
        star_id_of_comm, zero_mul, zero_add,
        Fintype.sum_prod_type]
      simp_rw [sum_digit_indicators
        (clearedDigit_lt_base hb hn)
        (clearedDigit_lt_base hb hn)]
      calc
        (∑ x : Fin L,
            if clearedDigit b n (numeratorValue j) D x.val =
                clearedDigit b n (numeratorValue i) D x.val
            then (1 : ℝ) else 0) =
            ∑ x ∈ Finset.range L,
              if clearedDigit b n (numeratorValue j) D x =
                  clearedDigit b n (numeratorValue i) D x
              then (1 : ℝ) else 0 :=
          Fin.sum_univ_eq_sum_range
            (fun x : ℕ =>
              if clearedDigit b n (numeratorValue j) D x =
                  clearedDigit b n (numeratorValue i) D x
              then (1 : ℝ) else 0) L
        _ = clearedPairMatchCount b n D L i j := by
          simp [clearedPairMatchCount, clearedPairMatchAt, eq_comm]

/-- Exact equality between the published entrywise matrix and the normalized
Gram matrix of its literal synchronized feature vectors. -/
theorem synchronizedCrossAlignmentMatrix_eq_gram
    {b n q D L : ℕ} (hb : 0 < b) (hn : 0 < n)
    (hL : 0 < L) :
    synchronizedCrossAlignmentMatrix b n q D L =
      (L : ℝ)⁻¹ • Matrix.gram ℝ (synchronizedFeature b n q D L) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.gram_apply,
    inner_synchronizedFeature hb hn i j]
  unfold synchronizedCrossAlignmentMatrix
  by_cases hi : q ∣ numeratorValue i
  · by_cases hj : q ∣ numeratorValue j
    · simp [hi, hj, hL.ne']
    · simp [hi, hj]
  · by_cases hj : q ∣ numeratorValue j
    · simp [hi, hj]
    · simp [hi, hj, div_eq_inv_mul]

/-- The literal matrix is positive semidefinite. -/
theorem synchronizedCrossAlignmentMatrix_posSemidef
    {b n q D L : ℕ} (hb : 0 < b) (hn : 0 < n)
    (hL : 0 < L) :
    Matrix.PosSemidef (synchronizedCrossAlignmentMatrix b n q D L) := by
  rw [synchronizedCrossAlignmentMatrix_eq_gram hb hn hL]
  exact (Matrix.posSemidef_gram ℝ
    (synchronizedFeature b n q D L)).smul (by positivity)

/-- Complete Gram realization: symmetry, positive semidefiniteness, unit
diagonal, and exact feature equality are all certified together. -/
theorem synchronizedCrossAlignmentMatrix_gram_realization
    {b n q D L : ℕ} (hb : 0 < b) (hn : 0 < n)
    (hL : 0 < L) :
    synchronizedCrossAlignmentMatrix b n q D L =
        (L : ℝ)⁻¹ • Matrix.gram ℝ (synchronizedFeature b n q D L) ∧
      (synchronizedCrossAlignmentMatrix b n q D L).IsSymm ∧
      Matrix.PosSemidef (synchronizedCrossAlignmentMatrix b n q D L) ∧
      ∀ i, synchronizedCrossAlignmentMatrix b n q D L i i = 1 := by
  exact ⟨synchronizedCrossAlignmentMatrix_eq_gram hb hn hL,
    synchronizedCrossAlignmentMatrix_isSymm b n q D L,
    synchronizedCrossAlignmentMatrix_posSemidef hb hn hL,
    synchronizedCrossAlignmentMatrix_diagonal hL⟩

/-! ## Canonical supported/rough denominator specialization -/

/-- The synchronized matrix attached canonically to a positive denominator. -/
noncomputable def canonicalCrossAlignmentMatrix
    (b n D : ℕ) (hn : 0 < n) :
    Matrix (ProperNumerator n) (ProperNumerator n) ℝ :=
  synchronizedCrossAlignmentMatrix b n (roughPart b n) D
    (canonicalAlignmentPeriod b n hn)

/-- The canonical matrix does not depend on the valid common clearing depth. -/
theorem canonicalCrossAlignmentMatrix_independent_of_clearing_depth
    {b n D E : ℕ} (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D)
    (hE : supportedPart b n ∣ b ^ E) :
    canonicalCrossAlignmentMatrix b n D hn =
      canonicalCrossAlignmentMatrix b n E hn := by
  unfold canonicalCrossAlignmentMatrix
  exact synchronizedCrossAlignmentMatrix_independent_of_clearing_depth_of_eq
    (roughPart_mul_supportedPart (b := b) hn).symm
      (supportedPart_pos hn) hD hE
      (pow_canonicalAlignmentPeriod_mod_eq_one hn)

/-- In the canonical matrix, the rough divisibility marker is exactly literal
base-`b` termination of the indexed fraction. -/
theorem canonical_matrix_marker_iff_terminates
    {b n : ℕ} (hn : 0 < n) (i : ProperNumerator n) :
    roughPart b n ∣ numeratorValue i ↔
      TerminatesInBase b (numeratorValue i) n := by
  exact (canonicalNumerator_terminates_iff hn).symm

/-- A supported denominator has rough part one. -/
theorem roughPart_eq_one_of_supported {b n : ℕ} (hn : 0 < n)
    (hsupported : Supported b n) : roughPart b n = 1 := by
  exact (roughPart_eq_one_iff_supported hn).2 hsupported

/-- If every fraction terminates, the literal matrix is the all-ones matrix. -/
theorem synchronizedCrossAlignmentMatrix_eq_allOnes_of_rough_eq_one
    {b n q D L : ℕ} (hq : q = 1) :
    synchronizedCrossAlignmentMatrix b n q D L = fun _ _ => 1 := by
  subst q
  ext i j
  simp [synchronizedCrossAlignmentMatrix]

/-- Canonical all-ones specialization for a base-supported denominator. -/
theorem canonicalCrossAlignmentMatrix_eq_allOnes_of_supported
    {b n D : ℕ} (hn : 0 < n) (hsupported : Supported b n) :
    canonicalCrossAlignmentMatrix b n D hn = fun _ _ => 1 := by
  unfold canonicalCrossAlignmentMatrix
  exact synchronizedCrossAlignmentMatrix_eq_allOnes_of_rough_eq_one
    (roughPart_eq_one_of_supported hn hsupported)

/-- Canonical Gram realization, symmetry, positivity, and unit diagonal for
every denominator at least two and every valid common clearing depth. -/
theorem canonicalCrossAlignmentMatrix_gram_realization
    {b n D : ℕ} (hb : 0 < b) (hn : 0 < n) :
    let A := canonicalCrossAlignmentMatrix b n D hn
    A.IsSymm ∧ Matrix.PosSemidef A ∧ ∀ i, A i i = 1 := by
  dsimp only
  unfold canonicalCrossAlignmentMatrix
  exact ⟨synchronizedCrossAlignmentMatrix_isSymm _ _ _ _ _,
    synchronizedCrossAlignmentMatrix_posSemidef hb hn
      (canonicalAlignmentPeriod_pos hn),
    synchronizedCrossAlignmentMatrix_diagonal
      (canonicalAlignmentPeriod_pos hn)⟩

end NField.Alignment.SynchronizedCrossAlignment
