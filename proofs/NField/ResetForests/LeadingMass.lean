/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SourceEnergy
/-! # The leading diagonal and off-diagonal masses in the complete sampled Gram -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RefinedBounds

open scoped BigOperators Topology Matrix
open Filter
open NField.Alignment CommonResetGram
open SourceMetrics GramDecomposition RecordGeometry CostCriteria

def diagonalMass (p : OddPrime) : ℝ := Matrix.trace (sampledGram (p.val - 1) (p.val ^ 2))

def offDiagonalMass (p : OddPrime) : ℝ := offDiagonalSum (sampledGram (p.val - 1) (p.val ^ 2))

theorem complete_mass_split (p : OddPrime) :
    diagonalMass p + offDiagonalMass p = sourceEnergy p.val := by
  rw [diagonalMass, offDiagonalMass, diagonal_and_off_diagonal]
  simp only [sourceEnergy, sourceWork, Matrix.mulVec, dotProduct, one_mul, mul_one]

theorem normalized_diagonal_factor (p : OddPrime) :
    diagonalMass p / (p.val : ℝ) ^ 3 =
      (1 - 1 / (p.val : ℝ)) * (1 - (1 / (p.val : ℝ)) ^ 2) *
        (1 - 2 * (1 / (p.val : ℝ)) ^ 2) / 3 := by
  have hp : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.1.ne_zero
  rw [diagonalMass, prime_square_gram_trace p.property.1,
    Nat.cast_sub p.property.1.one_le, Nat.cast_one]
  field_simp

theorem diagonal_mass_cubic_limit :
    Tendsto (fun p => diagonalMass p / (p.val : ℝ) ^ 3) primeAtTop (𝓝 (1 / 3 : ℝ)) := by
  have h := MagnitudeCubicLimits.reciprocal_base_limit
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h.pow 2)
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((h.pow 2).const_mul 2)
  have ht := ((h1.mul h2).mul h3).div_const 3
  simpa only [← normalized_diagonal_factor, sub_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, one_mul] using ht

theorem normalized_off_diagonal (p : OddPrime) :
    offDiagonalMass p / (p.val : ℝ) ^ 3 =
      sourceEnergy p.val / (p.val : ℝ) ^ 3 - diagonalMass p / (p.val : ℝ) ^ 3 := by
  rw [← complete_mass_split]
  ring

theorem off_diagonal_mass_cubic_limit :
    Tendsto (fun p => offDiagonalMass p / (p.val : ℝ) ^ 3) primeAtTop (𝓝 (2 / 3 : ℝ)) := by
  have ht := source_energy_cubic_limit.sub diagonal_mass_cubic_limit
  have hval : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  simpa only [← normalized_off_diagonal, hval] using ht

theorem source_cubic_error_isBigO :
    Asymptotics.IsBigO primeAtTop (fun p : OddPrime => sourceEnergy p.val - (p.val : ℝ) ^ 3)
      (fun p : OddPrime => (p.val : ℝ) ^ 2 * (Real.log (p.val : ℝ)) ^ 2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨96, Eventually.of_forall ?_⟩
  intro p
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  simpa only [mul_assoc] using source_energy_cubic_error p.property.1 p.property.2

end NField.ResetForests.RefinedBounds
