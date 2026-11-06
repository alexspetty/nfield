/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSawtoothPairIntegral
import NField.Alignment.RealBernoulliBoundaryLimits
import NField.Alignment.SaffariVaughanDistribution
import NField.Alignment.SecondaryCapacityAnalyticInputs
import NField.Alignment.GcdLcmCapacity

/-! # The actual Bernoulli square integral and its secondary coefficient -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealBernoulliCapacityIntegral
open scoped BigOperators Topology Classical
open MeasureTheory Set CollisionDedekindPairing RealSawtoothDistribution
  RealSawtoothPairIntegral RealBernoulliBoundaryLimits GcdLcmCapacity
  SecondaryCapacityLedger SecondaryCapacityAnalyticInputs PrimeSquareCollisionWindow

def integralCapacity (N : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (realBoundary N x)^2

theorem real_boundary_square (N : ℕ) (x : ℝ) :
    (realBoundary N x)^2=4*∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      periodicSawtooth (((i+1:ℕ):ℝ)*x)*periodicSawtooth (((j+1:ℕ):ℝ)*x) := by
  unfold realBoundary
  rw [mul_pow,show (2:ℝ)^2=4 by norm_num,pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem integral_capacity_pair_sum (N : ℕ) :
    integralCapacity N=4*∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, pairIntegral (i+1) (j+1) := by
  unfold integralCapacity
  simp only [real_boundary_square,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · rfl
    · intro j hj
      exact sawtooth_pair_integrable _ _ _ _
  · intro i hi
    have he : (fun x : ℝ => ∑ j ∈ Finset.range N,
        periodicSawtooth (((i+1:ℕ):ℝ)*x)*periodicSawtooth (((j+1:ℕ):ℝ)*x)) =
        ∑ j ∈ Finset.range N, (fun x : ℝ =>
          periodicSawtooth (((i+1:ℕ):ℝ)*x)*periodicSawtooth (((j+1:ℕ):ℝ)*x)) := by
      ext x
      simp
    rw [he]
    exact IntervalIntegrable.sum (Finset.range N)
      (fun j hj => sawtooth_pair_integrable (((i+1:ℕ):ℝ)) (((j+1:ℕ):ℝ)) 0 1)

theorem gcd_lcm_square_sum_ranges (N : ℕ) :
    gcdLcmSquareSum N=∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, gcdLcmKernel (i+1) (j+1) := by
  change (∑ i : Fin N, ∑ j : Fin N, gcdLcmKernel (i.val+1) (j.val+1))=_
  calc
    _ = ∑ i : Fin N, ∑ j ∈ Finset.range N, gcdLcmKernel (i.val+1) (j+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ => gcdLcmKernel (i.val+1) (j+1)) N
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun i : ℕ => ∑ j ∈ Finset.range N, gcdLcmKernel (i+1) (j+1)) N

/-- Title: `Continuous capacity as the Bernoulli square integral`. -/
theorem integral_capacity_eq_continuous_capacity (N : ℕ) :
    (∫ x in (0:ℝ)..1, (realBoundary N x)^2)=continuousCapacity N := by
  change integralCapacity N=_
  have he : 3*integralCapacity N=gcdLcmSquareSum N := by
    rw [integral_capacity_pair_sum,gcd_lcm_square_sum_ranges]
    rw [← mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pairIntegral,sawtooth_pair_integral (by omega) (by omega)]
    unfold gcdLcmKernel
    have hiR : ((i+1:ℕ):ℝ)≠0 := by positivity
    have hjR : ((j+1:ℕ):ℝ)≠0 := by positivity
    field_simp
    ring
  rw [gcdLcmSquareSum_eq_three_continuousCapacity] at he
  linarith

/-- Title: `Secondary term for the actual continuous square integral`. -/
theorem integral_capacity_secondary_coefficient :
    EventualErrorBound integralCapacity continuousCapacityMain secondaryCapacityRemainderScale := by
  have he : integralCapacity=continuousCapacity := funext integral_capacity_eq_continuous_capacity
  rw [he]
  exact SecondaryCapacityAnalyticInputs.continuous_secondary_coefficient
    SaffariVaughanDistribution.saffari_vaughan_distribution

end NField.Alignment.RealBernoulliCapacityIntegral
