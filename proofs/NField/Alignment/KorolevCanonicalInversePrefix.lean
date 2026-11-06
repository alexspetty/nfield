/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalSelectedSum
import NField.Alignment.InverseResidueHarmonicRangeSplit

/-! # The actual centered inverse-residue prefix as a canonical sum plus its bounded omitted set -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalInversePrefix
open KorolevCanonicalTuples KorolevCanonicalSelectedSum DedekindInverseResidueTransform
  DedekindReciprocity InverseResidueHarmonicRangeSplit
open scoped BigOperators Classical

def canonicalPrefix (P Q : Finset ℕ) (q r X : ℕ) : ℝ :=
  ∑ t ∈ (tuples P Q ⌊Real.log (X : ℝ)⌋₊ X).filter (fun t => (value t).Coprime q),
    (rationalSawtooth (r*inverseResidue (value t) q) q : ℝ)

/-- The actual paper prefix has an exact canonical-tuple part and an actual failure-set part. -/
theorem prefix_eq_canonical_add_failure {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hX : 1 ≤ X) :
    inverseResiduePrefix q r X = canonicalPrefix P Q q r X +
      ∑ n ∈ failure (X : ℝ) P Q q, (rationalSawtooth (r*inverseResidue n q) q : ℝ) := by
  have hx : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have h := sum_all_eq_canonical_add_failure hP hQ hdis hx q
    (fun n => (rationalSawtooth (r*inverseResidue n q) q : ℝ))
  simpa only [Nat.floor_natCast, Finset.sum_filter, inverseResiduePrefix, canonicalPrefix] using h

/-- The omitted part of the actual centered prefix costs at most one half per failed representation. -/
theorem prefix_remainder_bound {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hq : 0 < q) (hX : 1 ≤ X) :
    |inverseResiduePrefix q r X - canonicalPrefix P Q q r X| ≤
      ((failure (X : ℝ) P Q q).card : ℝ)/2 := by
  rw [prefix_eq_canonical_add_failure hP hQ hdis q r X hX, add_sub_cancel_left]
  have h := norm_failure_sum_le (G := ℝ) (X : ℝ) P Q q
    (fun n => (rationalSawtooth (r*inverseResidue n q) q : ℝ)) (1/2) (by
      intro n _
      rw [Real.norm_eq_abs]
      have hc : ((|rationalSawtooth (r*inverseResidue n q) q| : ℚ) : ℝ) ≤
          (((1/2 : ℚ) : ℝ)) := Rat.cast_le.mpr (abs_rationalSawtooth_le_half (x := r*inverseResidue n q) hq)
      simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc)
  simpa only [Real.norm_eq_abs, mul_one_div] using h

end NField.Alignment.KorolevCanonicalInversePrefix
