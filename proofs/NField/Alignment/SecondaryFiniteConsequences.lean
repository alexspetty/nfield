/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryRealFractionalParts
import NField.Alignment.SquareLockAsymptoticScales
import NField.Alignment.ReciprocalDivisorMomentBound
import NField.Alignment.PrimitiveAdditiveConvolution

/-! # Literal cutoff and correction clauses in the secondary-term paper -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryFiniteConsequences
open scoped BigOperators Topology
open Filter Asymptotics DedekindInverseResidueTransform ExactSamplingReservoirBridge
  EndpointReciprocityBridge PrimeCarrierDamping PrimeSecondaryCoefficient
  SquareLockAsymptoticScales BernoulliCurvature EndpointReservoirAlias

/-- Title: `Reciprocal-divisor moments at real cutoffs`. -/
theorem bounded_reciprocal_divisor_moments (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, reciprocalDivisorSum k^j ≤ C*x := by
  by_cases hj : j=0
  · subst j
    refine ⟨1,by norm_num,?_⟩
    intro x hx
    simpa using Nat.floor_le hx
  · obtain ⟨C,hC,hbound⟩ := ReciprocalDivisorMomentBound.bounded_reciprocal_divisor_moments
      j (Nat.pos_of_ne_zero hj)
    exact ⟨C,hC,fun x hx => (hbound ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hC)⟩

theorem harmonic_predecessor_le_log {p : ℕ} (hp : 2 ≤ p) :
    (harmonic (p-1) : ℝ) ≤ 1+Real.log (p : ℝ) := by
  have hn : 0 < p-1 := by omega
  have hlog : Real.log ((p-1 : ℕ) : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast Nat.sub_le p 1)
  linarith [harmonic_le_one_add_log (p-1)]

/-- Title: `The elementary reservoir has the printed logarithmic bound`. -/
theorem elementary_reservoir_log_bound {p : ℕ} (hp : 2 ≤ p) :
    elementaryRatioReservoir p ≤ (p : ℝ)^2*(1+Real.log p)/2 := by
  have hN : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hh := harmonic_predecessor_le_log hp
  have hH : 0 ≤ (harmonic (p-1) : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  have heq := elementaryRatioReservoir_add_eq_harmonic hp
  calc
    _ ≤ ((p-1 : ℕ) : ℝ)+elementaryRatioReservoir p := by
      linarith [Nat.cast_nonneg (α := ℝ) (p-1)]
    _ = (p : ℝ)*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/2 := heq
    _ ≤ (p : ℝ)*(p : ℝ)*(1+Real.log p)/2 := by gcongr
    _ = _ := by ring

/-- Title: `The exact logarithmic sampling correction`. -/
theorem sampling_correction_bound {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |samplingDefect hp-(((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2-
      lowerModulusReservoir p/(p : ℝ)^2)| ≤ (1+Real.log p)/(3*(p : ℝ)^2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hh := harmonic_predecessor_le_log hp.two_le
  have hH : 0 ≤ (harmonic (p-1) : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  rw [exact_sampling_reservoir_bridge hp hpodd, show
    ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2 - 2/(3*(p : ℝ)^4)*
      (((p-1 : ℕ) : ℝ)+elementaryRatioReservoir p) - lowerModulusReservoir p/(p : ℝ)^2 -
      (((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2-lowerModulusReservoir p/(p : ℝ)^2) =
      -(2/(3*(p : ℝ)^4)*(((p-1 : ℕ) : ℝ)+elementaryRatioReservoir p)) by ring,
      abs_neg, elementaryRatioReservoir_add_eq_harmonic hp.two_le,
      abs_of_nonneg (by positivity)]
  calc
    _ ≤ 2/(3*(p : ℝ)^4)*((p : ℝ)*(p : ℝ)*(1+Real.log p)/2) := by gcongr
    _ = _ := by field_simp

/-- Title: `The primitive convolution is twice the half packet`. -/
theorem primitive_convolution_eq_packet {p X : ℕ} [NeZero X] (hX : 2 ≤ X) :
    PrimitiveAdditiveConvolution.primitiveAdditiveConvolution p X =
      2*ComplementaryPartition.partitionPacket (p^2) X :=
  PrimitiveAdditiveConvolution.primitive_convolution_eq_packet hX

end NField.Alignment.SecondaryFiniteConsequences
