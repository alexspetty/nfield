/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandCosts
import NField.Alignment.CommonResetDivisorSums

/-! # Summing every inverse frequency in the actual band majorant -/

noncomputable section

namespace NField.Alignment.CommonResetBoxRows

open scoped BigOperators
open CommonResetBandCosts CommonResetBandWeighted CommonResetRootSums CommonResetDivisorSums
open CommonResetSmallConductors CommonResetDivisorFibers DedekindInverseResidueTransform
open CompletedPrefixDivisorGrowth

def rowCost (p m v j : ℕ) : ℝ :=
  ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
    (1/Real.sqrt (j : ℝ))*(1/Real.sqrt (v : ℝ)) +
  ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*rootCube j*rootCube v +
  (4*(p : ℝ)*Real.sqrt (p : ℝ)/(m : ℝ))*(1/(j : ℝ))*(1/(v : ℝ))

theorem rowCost_nonneg (p m v j : ℕ) : 0 ≤ rowCost p m v j := by
  have hj := rootCube_nonneg j
  have hv := rootCube_nonneg v
  unfold rowCost
  positivity

theorem gcd_log_sum {a p : ℕ} (ha : 0 < a) :
    (∑ u ∈ Finset.Icc 1 p, (Real.sqrt (a.gcd u : ℝ)/Real.sqrt (u : ℝ))*Real.log (2*(u : ℝ))) ≤
      4*Real.sqrt (p : ℝ)*(harmonic p : ℝ)*reciprocalSqrtDivisorSum a := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 p,
        (Real.sqrt (a.gcd u : ℝ)/Real.sqrt (u : ℝ))*(2*(harmonic p : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (log_twice_le_harmonic (Finset.mem_Icc.mp hu).1
        (Finset.mem_Icc.mp hu).2) (by positivity)
    _ = (∑ u ∈ Finset.Icc 1 p, Real.sqrt (a.gcd u : ℝ)/Real.sqrt (u : ℝ))*(2*(harmonic p : ℝ)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (2*Real.sqrt (p : ℝ)*reciprocalSqrtDivisorSum a)*(2*(harmonic p : ℝ)) :=
      mul_le_mul_of_nonneg_right (gcd_root_sum ha p) (by have := harmonic_nonneg p; positivity)
    _ = _ := by ring

/-- Title: `Every inverse frequency is included in the band majorant with the exact gcd divisor cost`. -/
theorem sum_inverse_band_cost {p m v j : ℕ} (hm : 0 < m) (hv : 0 < v) (hj : 0 < j) :
    (∑ u ∈ Finset.Icc 1 p, Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j) ≤
      reciprocalSqrtDivisorSum (j*v)*(harmonic p : ℝ)*rowCost p m v j := by
  have ha : 0 < j*v := Nat.mul_pos hj hv
  have h1 := gcd_harmonic_sum ha p
  have h3 := gcd_log_sum (p := p) ha
  have hj0 := rootCube_nonneg j
  have hv0 := rootCube_nonneg v
  calc
    _ = ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
          (1/Real.sqrt (j : ℝ))*(1/Real.sqrt (v : ℝ))*
          (∑ u ∈ Finset.Icc 1 p, Real.sqrt ((j*v).gcd u : ℝ)/(u : ℝ)) +
        ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*rootCube j*rootCube v*
          (∑ u ∈ Finset.Icc 1 p, Real.sqrt ((j*v).gcd u : ℝ)/(u : ℝ)) +
        ((p : ℝ)/m)*(1/(j : ℝ))*(1/(v : ℝ))*
          (∑ u ∈ Finset.Icc 1 p, (Real.sqrt ((j*v).gcd u : ℝ)/Real.sqrt (u : ℝ))*Real.log (2*(u : ℝ))) := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      rw [band_cost_decomposition hm (Finset.mem_Icc.mp hu).1 hv hj]
      ring
    _ ≤ ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
          (1/Real.sqrt (j : ℝ))*(1/Real.sqrt (v : ℝ))*
          ((harmonic p : ℝ)*reciprocalSqrtDivisorSum (j*v)) +
        ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*rootCube j*rootCube v*
          ((harmonic p : ℝ)*reciprocalSqrtDivisorSum (j*v)) +
        ((p : ℝ)/m)*(1/(j : ℝ))*(1/(v : ℝ))*
          (4*Real.sqrt (p : ℝ)*(harmonic p : ℝ)*reciprocalSqrtDivisorSum (j*v)) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h1 (by positivity))) (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = _ := by unfold rowCost; ring

theorem divisor_card_le_pmaximum {p u : ℕ} (hp : 1 ≤ p) (hu : 0 < u) (hup : u ≤ p) :
    u.divisors.card ≤ divisorMaximum p := by
  apply divisor_card_le_maximum hu
  have hpow : p ≤ p^3 := by nlinarith [sq_nonneg (p : ℤ)]
  omega

theorem product_divisor_sum_le_maximum {p v j : ℕ} (hp : 1 ≤ p)
    (hv : 0 < v) (hj : 0 < j) (hvp : v ≤ p) (hjp : j ≤ p) :
    reciprocalSqrtDivisorSum (j*v) ≤ (divisorMaximum p : ℝ) := by
  apply (reciprocal_sqrt_divisor_sum_le_count _).trans
  exact_mod_cast divisor_card_le_maximum (Nat.mul_pos hj hv) (by
    have hjv : j*v ≤ p*p := Nat.mul_le_mul hjp hvp
    have hpow : p*p ≤ p^3 := by nlinarith
    omega)

/-- Title: `The complete inverse-frequency row costs only the squared divisor maximum and one harmonic factor`. -/
theorem sum_complete_band_cost {p m v j : ℕ} (hp : 1 ≤ p) (hm : 0 < m)
    (hv : 0 < v) (hj : 0 < j) (hvp : v ≤ p) (hjp : j ≤ p) :
    (∑ u ∈ Finset.Icc 1 p, (u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j) ≤
      (divisorMaximum p : ℝ)^2*(harmonic p : ℝ)*rowCost p m v j := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 p, (divisorMaximum p : ℝ)*
        (Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j) := by
      apply Finset.sum_le_sum
      intro u hu
      have hU := Finset.mem_Icc.mp hu
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (divisor_card_le_pmaximum hp hU.1 hU.2))
        (mul_nonneg (Real.sqrt_nonneg _) (bandSummandScale_nonneg p m u v j hU.1))
    _ = (divisorMaximum p : ℝ)*(∑ u ∈ Finset.Icc 1 p,
        Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j) := (Finset.mul_sum _ _ _).symm
    _ ≤ (divisorMaximum p : ℝ)*(reciprocalSqrtDivisorSum (j*v)*(harmonic p : ℝ)*rowCost p m v j) :=
      mul_le_mul_of_nonneg_left (sum_inverse_band_cost hm hv hj) (Nat.cast_nonneg _)
    _ ≤ (divisorMaximum p : ℝ)*((divisorMaximum p : ℝ)*(harmonic p : ℝ)*rowCost p m v j) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (rowCost_nonneg p m v j)
      exact mul_le_mul_of_nonneg_right (product_divisor_sum_le_maximum hp hv hj hvp hjp) (harmonic_nonneg p)
    _ = _ := by ring

end NField.Alignment.CommonResetBoxRows
