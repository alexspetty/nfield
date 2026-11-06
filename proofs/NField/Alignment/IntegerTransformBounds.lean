/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerDedekindTransform
import NField.Alignment.KorolevRangeEstimate
import NField.Alignment.KloostermanGlobalBound
import NField.Alignment.CompletedPrefixDivisorGrowth

/-! # Unconditional harmonic and transform bounds for signed frequencies -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerTransformBounds
open DedekindInverseResidueTransform IntegerInverseResidue IntegerDedekindTransform
  InverseResiduePrefixCompletion InverseResidueHarmonicRangeSplit

theorem ambient_inverse_bound : KorolevAmbientInverseResidueEstimate :=
  korolevAmbientInverseResidueEstimate_of_partials
    (uniformInverseSawPartialHarmonicEstimate KorolevRangeEstimate.korolev_range_estimate
      (completed_inverse_prefixes KloostermanGlobalBound.weil_estermann_inverse_prefix_estimate)
      CompletedPrefixDivisorGrowth.standard_completed_prefix_divisor_growth)

/-- Title: `Inverse-residue harmonic bound for every integer numerator`. -/
theorem integer_inverse_harmonic_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ (q : ℕ) (r : ℤ), 2≤q → Int.gcd r (q:ℤ)=1 →
      ‖integerInverseSeries q r‖≤C*inverseResidueHarmonicScale q := by
  obtain ⟨C,hC,hbound⟩ := inverse_residue_harmonic_bound ambient_inverse_bound
  refine ⟨C,hC,?_⟩
  intro q r hq hcop
  cases r with
  | ofNat r =>
      change ‖integerInverseSeries q (r:ℤ)‖≤_
      rw [integer_series_nat]
      exact hbound q r hq hcop
  | negSucc r =>
      change ‖integerInverseSeries q (-((r+1:ℕ):ℤ))‖≤_
      rw [integer_series_neg_nat,norm_neg]
      exact hbound q (r+1) hq hcop

/-- Title: `Uniform additive transform bound for integer frequencies`. -/
theorem integer_uniform_transform_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ (k : ℕ) (t : ℤ), 2≤k →
      ‖integerUnitTransform k t‖/(k:ℝ)≤
        C*inverseResidueHarmonicScale k*reciprocalDivisorSum k^3 := by
  obtain ⟨C,hC,hbound⟩ := uniform_additive_transform_bound ambient_inverse_bound
  refine ⟨C,hC,?_⟩
  intro k t hk
  cases t with
  | ofNat t =>
      change ‖integerUnitTransform k (t:ℤ)‖/(k:ℝ)≤_
      rw [integer_unit_nat]
      exact hbound k t hk
  | negSucc t =>
      change ‖integerUnitTransform k (-((t+1:ℕ):ℤ))‖/(k:ℝ)≤_
      rw [integer_unit_neg (by omega),integer_unit_nat,norm_neg]
      exact hbound k (t+1) hk

end NField.Alignment.IntegerTransformBounds
