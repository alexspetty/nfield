/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryFiniteConsequences
import NField.Alignment.EndpointReciprocityBridge

/-! # Literal logarithmic envelopes for the Bernoulli curvature channel -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryCurvatureBounds
open scoped BigOperators
open BernoulliCurvature EndpointReciprocityBridge EndpointReservoirAlias
  SecondaryFiniteConsequences ExactSamplingReservoirBridge

theorem floor_quotient_log_bound (N : ℕ) :
    (∑ k ∈ Finset.Icc 2 N,((N/k : ℕ) : ℝ)) ≤ (N : ℝ)*(1+Real.log (N : ℝ)) := by
  have h : (∑ k ∈ Finset.Icc 2 N,((N/k : ℕ) : ℝ)) ≤ (N : ℝ)*(harmonic N : ℝ) := by
    exact_mod_cast floorQuotientSum_le_harmonic N
  exact h.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg _))

/-- Title: `The curvature reservoir has a logarithmic bound`. -/
theorem curvature_log_bound {p : ℕ} (hp : p.Prime) :
    |(carrierBernoulliCurvature p : ℝ)| ≤ (1+Real.log (p : ℝ))/6 := by
  rw [carrierBernoulliCurvature_eq_harmonic hp]
  push_cast
  have hH : 0 ≤ (harmonic (p-1) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  rw [abs_of_nonneg (by positivity)]
  linarith [harmonic_predecessor_le_log hp.two_le]

/-- Title: `The scaled curvature correction is logarithmic over p squared`. -/
theorem scaled_curvature_log_bound {p : ℕ} (hp : p.Prime) :
    |2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4| ≤
      (1+Real.log (p : ℝ))/(3*(p : ℝ)^2) := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hN : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hH : 0 ≤ (harmonic (p-1) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  rw [carrierBernoulliCurvature_eq_harmonic hp]
  unfold boundarySlope
  push_cast
  rw [abs_of_nonneg (by positivity)]
  have hh := harmonic_predecessor_le_log hp.two_le
  calc
    _ ≤ 2*((p : ℝ)*(p : ℝ))*((1+Real.log (p : ℝ))/6)/(p : ℝ)^4 := by
      gcongr
    _ = _ := by field_simp <;> norm_num

/-- Title: `Endpoint aliasing with the explicit curvature remainder`. -/
theorem endpoint_alias_log_remainder {p : ℕ} (hp : p.Prime) (hpodd : p≠2) :
    |samplingDefect hp-
      (((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2+4*(jumpPhaseReservoir p : ℝ)/(p : ℝ)^2)| ≤
      (1+Real.log (p : ℝ))/(3*(p : ℝ)^2) := by
  rw [exact_endpoint_reservoir_alias_formula hp hpodd]
  have he : ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2+4*(jumpPhaseReservoir p : ℝ)/(p : ℝ)^2-
      2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4-
      (((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2+4*(jumpPhaseReservoir p : ℝ)/(p : ℝ)^2)=
      -(2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4) := by ring
  rw [he,abs_neg]
  exact scaled_curvature_log_bound hp

end NField.Alignment.SecondaryCurvatureBounds
