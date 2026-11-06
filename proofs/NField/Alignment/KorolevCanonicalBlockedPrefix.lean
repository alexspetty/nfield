/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalPrimeSlices
import NField.Alignment.KorolevCanonicalInversePrefix

/-! # The actual inverse-residue prefix in canonical logarithmic prime blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalBlockedPrefix
open KorolevCanonicalPrimeSlices KorolevCanonicalInversePrefix KorolevCanonicalSelectedSum
  KorolevLogarithmicPartition DedekindInverseResidueTransform DedekindReciprocity
open scoped BigOperators Classical

def blockedPrefix (P Q : Finset ℕ) (q r X : ℕ) (lp lq Dp Dq A : ℝ) : ℝ :=
  ∑ l ∈ (Finset.Icc 1 ⌊Real.log (X : ℝ)⌋₊).filter (fun l => l.Coprime q),
    ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime q),
      ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
        primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X q
          (fun n => (rationalSawtooth (r*inverseResidue n q) q : ℝ))

/-- The exact canonical part of the actual prefix is a cutoff-preserving rectangular block sum. -/
theorem canonical_eq_blocked (P Q : Finset ℕ) (q r X : ℕ) (lp lq : ℝ)
    {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hP : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQ : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    canonicalPrefix P Q q r X = blockedPrefix P Q q r X lp lq Dp Dq A := by
  exact sum_tuples_eq_blocks P Q ⌊Real.log (X : ℝ)⌋₊ X q
    (fun n => (rationalSawtooth (r*inverseResidue n q) q : ℝ)) lp lq hA hDp hDq hP hQ

/-- Only the actual omitted representations sit outside the exact block sum. -/
theorem prefix_eq_blocked_add_failure {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hX : 1 ≤ X)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hPI : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQI : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    inverseResiduePrefix q r X = blockedPrefix P Q q r X lp lq Dp Dq A +
      ∑ n ∈ failure (X : ℝ) P Q q, (rationalSawtooth (r*inverseResidue n q) q : ℝ) := by
  rw [prefix_eq_canonical_add_failure hP hQ hdis q r X hX,
    canonical_eq_blocked P Q q r X lp lq hA hDp hDq hPI hQI]

/-- Prime-block decomposition leaves the half-per-failure remainder bound unchanged. -/
theorem prefix_block_remainder_bound {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hq : 0 < q) (hX : 1 ≤ X)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hPI : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQI : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    |inverseResiduePrefix q r X - blockedPrefix P Q q r X lp lq Dp Dq A| ≤
      ((failure (X : ℝ) P Q q).card : ℝ)/2 := by
  rw [← canonical_eq_blocked P Q q r X lp lq hA hDp hDq hPI hQI]
  exact prefix_remainder_bound hP hQ hdis q r X hq hX

end NField.Alignment.KorolevCanonicalBlockedPrefix
