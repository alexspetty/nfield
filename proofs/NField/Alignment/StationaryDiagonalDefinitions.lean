/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionStationaryAgeAsymptotic
import NField.Alignment.SaffariVaughanFiniteReduction
import NField.Alignment.CollisionLogTailKernel

/-! # Literal finite observables for stationary-to-diagonal transfer -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryDiagonalDefinitions
open scoped BigOperators
open CollisionRemainderDynamics CollisionMassReadout

/-- The source uses the raw fractional part, including value minus one half at integers. -/
def psi (u : ℝ) : ℝ := Int.fract u - 1 / 2
def coefficient (k : ℕ) : ℝ := (k : ℝ) * collisionWeight k
def diagonal (n : ℕ) : ℝ := finiteAge collisionWeight n n
def weightPrefix (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, collisionWeight k
def cumulativeWeight (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, coefficient k
def dyadicMean (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  (X : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc X (2 * X), f n

theorem weight_one : collisionWeight 1 = 0 := by
  simp [collisionWeight, SecondaryCapacityLedger.reducedHarmonicStar]

theorem age_as_sum_from_one (M n : ℕ) :
    finiteAge collisionWeight M n =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 1 M, collisionWeight k * centeredRemainder k n := by
  unfold finiteAge
  congr 1
  apply Finset.sum_subset
  · intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  · intro k hk hnot
    have := Finset.mem_Icc.mp hk
    have hk1 : k = 1 := by simp only [Finset.mem_Icc] at hnot; omega
    subst k
    rw [weight_one, zero_mul]

theorem centered_remainder_psi (n : ℕ) {k : ℕ} (hk : 0 < k) :
    centeredRemainder k n = (k : ℝ) * psi ((n : ℝ) / k) + 1 / 2 := by
  unfold centeredRemainder psi
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  ring

/-- Title: `The raw sawtooth equals minus one half at integers`. -/
theorem psi_integer (n : ℤ) : psi n = -1 / 2 := by
  norm_num [psi]

theorem cumulativeWeight_firstMoment (t : ℝ) :
    cumulativeWeight t = CollisionStationaryAgeAsymptotic.firstMoment ⌊t⌋₊ := rfl

end NField.Alignment.StationaryDiagonalDefinitions
