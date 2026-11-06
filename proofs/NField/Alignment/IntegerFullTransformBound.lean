/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerTransformBounds

/-! # The full transform bound retains every integer frequency -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerFullTransformBound
open DedekindInverseResidueTransform IntegerDedekindTransform

/-- Title: `The full additive transform costs two reciprocal-divisor factors`. -/
theorem integer_full_transform_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (K : ℕ) (t : ℤ),2 ≤ K →
      ‖integerFullTransform K t‖/(K : ℝ) ≤
        C*inverseResidueHarmonicScale K*reciprocalDivisorSum K^2 := by
  obtain ⟨C,hC,hbound⟩ := IntegerTransformBounds.ambient_inverse_bound
  refine ⟨C,hC,?_⟩
  intro K t hK
  have hb (u : ℕ) : ‖fullDedekindTransform K u‖/(K : ℝ) ≤
      C*inverseResidueHarmonicScale K*reciprocalDivisorSum K^2 :=
    norm_fullDedekindTransform_div_le_of_ambient_unit_bound hK le_rfl
      inverseResidueHarmonicScale hC (inverseResidueHarmonicScale_nonneg hK)
      (hbound K)
  cases t with
  | ofNat t =>
      change ‖integerFullTransform K (t : ℤ)‖/(K : ℝ) ≤ _
      rw [integer_full_nat]
      exact hb t
  | negSucc t =>
      change ‖integerFullTransform K (-((t+1 : ℕ) : ℤ))‖/(K : ℝ) ≤ _
      rw [integer_full_neg (by omega),integer_full_nat,norm_neg]
      exact hb (t+1)

end NField.Alignment.IntegerFullTransformBound
