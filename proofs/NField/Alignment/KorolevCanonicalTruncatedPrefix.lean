/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevBlockResidualRange
import NField.Alignment.KorolevCanonicalBlockedPrefix

/-! # The actual blocked prefix with its exact residual support -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalTruncatedPrefix
open KorolevCanonicalPrimeSlices KorolevLogarithmicPartition KorolevBlockResidualRange
  KorolevCanonicalBlockedPrefix KorolevCanonicalSelectedSum DedekindInverseResidueTransform
  DedekindReciprocity
open scoped BigOperators Classical

def truncatedPrefix (P Q : Finset ℕ) (q r X : ℕ) (lp lq Dp Dq A : ℝ) : ℝ :=
  ∑ l ∈ (Finset.Icc 1 ⌊Real.log (X : ℝ)⌋₊).filter (fun l => l.Coprime q),
    ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
      ∑ h ∈ (Finset.Icc 1 (residualBound l X (point lp Dp A i) (point lq Dq A j))).filter
        (fun h => Squarefree h ∧ h.Coprime q),
        primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X q
          (fun n => (rationalSawtooth (r*inverseResidue n q) q : ℝ))

/-- Reordering the finite sums exposes the exact block-dependent residual range. -/
theorem blocked_eq_truncated (P Q : Finset ℕ) (q r X : ℕ) (lp lq Dp Dq A : ℝ) :
    blockedPrefix P Q q r X lp lq Dp Dq A = truncatedPrefix P Q q r X lp lq Dp Dq A := by
  unfold blockedPrefix truncatedPrefix
  apply Finset.sum_congr rfl
  intro l hl
  have hlpos : 0 < l := (Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1).1
  have hswap (F : ℕ → ℕ → ℕ → ℝ) :
      (∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime q),
        ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A), F h i j) =
        ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
          ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime q), F h i j := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime q))
      (t := Finset.range (blockCount Dq A))]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact sum_block_residual_truncated P Q l X q _ lp lq Dp Dq A i j hlpos

/-- The actual prefix equals the truncated block sum plus its actual omitted representations. -/
theorem prefix_eq_truncated_add_failure {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hX : 1 ≤ X)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hPI : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQI : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    inverseResiduePrefix q r X = truncatedPrefix P Q q r X lp lq Dp Dq A +
      ∑ n ∈ failure (X : ℝ) P Q q, (rationalSawtooth (r*inverseResidue n q) q : ℝ) := by
  rw [prefix_eq_blocked_add_failure hP hQ hdis q r X hX lp lq hA hDp hDq hPI hQI,
    blocked_eq_truncated]

/-- Exact residual truncation does not enlarge the omitted-representation error. -/
theorem prefix_truncated_remainder_bound {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hq : 0 < q) (hX : 1 ≤ X)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hPI : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQI : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    |inverseResiduePrefix q r X - truncatedPrefix P Q q r X lp lq Dp Dq A| ≤
      ((failure (X : ℝ) P Q q).card : ℝ)/2 := by
  rw [← blocked_eq_truncated P Q q r X lp lq Dp Dq A]
  exact prefix_block_remainder_bound hP hQ hdis q r X hq hX lp lq hA hDp hDq hPI hQI

end NField.Alignment.KorolevCanonicalTruncatedPrefix
