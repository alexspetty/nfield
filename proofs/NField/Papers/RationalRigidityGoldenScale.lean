/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Golden.WeightedRepetendRigidity
import NField.Golden.FiniteReplicationWeights
import NField.Alignment.CyclicShiftCounts
import NField.Golden.PeriodicRepetendRigidity
import NField.Golden.PeriodicRepetendClosure

/-!
# Repetend Rigidity at the Golden Scale

## Coverage

All numbered mathematical claims are formalized, including cumulative closure
and the rational golden endpoints. Arbitrary-period rigidity concerns rational
weights; the real-weight classification remains one-digit only. The
finite-score statements retain the scale-one exception.

## Scope and assumptions

The least closure is defined from the literal digit stream and its digit sum;
the order formula is a theorem about that definition. Arbitrary-period
rigidity concerns rational weights and the actual modular orbit for coprime
bases. The real-weight classification remains one-digit only. Both
finite-score interpretations retain the scale-one exception and the
rationality converse above scale one. No primality conclusion is inferred.
-/

namespace NField.Papers.RationalRigidityGoldenScale

open Filter
open NField.Alignment NField.Golden
open NField.CollisionDefinition

/-- Supported denominators have a generic integer-modulus block certificate at
a common clearing depth. -/
theorem supported_one_digit_block_profile
    {b q m : ℕ} (hq : 2 ≤ q) (hb : 2 ≤ b) (hmod : b % q = 1)
    (hm : Supported b m) :
    ∃ D : ℕ, m ∣ b ^ D ∧
      (∀ k : ℕ, ClearsAtDepth b q m D k ↔ k % q = 0) ∧
      (∀ k : ℕ,
        MatchesOneDigitReference b q (clearingCofactor b m D) k ↔
          k % q = 1) ∧
      terminatingNumeratorCount q m = m - 1 ∧
      matchingNumeratorCount q m = m ∧
      Nat.count (fun k => k % q ≠ 0 ∧ k % q ≠ 1) (q * m) =
        (q - 2) * m := by
  rcases hm with ⟨D, hD⟩
  exact ⟨D, hD, oneDigit_modulus_certificate (by omega) hb hmod hD⟩

/-- Every nonzero residue class has `m` rows and a constant one-digit tail. -/
theorem one_digit_residue_blocks
    {b q m r : ℕ} (hq : 2 ≤ q) (hmod : b % q = 1) (hr : r < q) :
    residueCount q r m = m ∧
      (∀ j : ℕ, digitAt b q r j = digitBin b q (r % q)) :=
  ⟨residueCount_eq hr, fun j => digitAt_eq_initial_modulus (by omega) hmod⟩

/-- The opening denominator-twelve partition and its weighted score. -/
theorem denominator_twelve_profile (lambda : ℝ) :
    terminatingNumeratorCount 3 4 = 3 ∧
      matchingNumeratorCount 3 4 = 4 ∧
      Nat.count (fun k => k % 3 ≠ 0 ∧ k % 3 ≠ 1) 12 = 4 ∧
      digitBin 10 3 1 = 3 ∧ digitBin 10 3 2 = 6 ∧
      weightedReferenceScore 3 4 lambda = (3 * lambda + 4) / 11 := by
  have hcounts := oneDigit_modulus_block_counts (q := 3) (m := 4) (by norm_num)
  have hscore := weightedReferenceScore_eq (q := 3) (m := 4)
    (by norm_num) lambda
  norm_num at hcounts hscore ⊢
  exact ⟨hcounts.1, hcounts.2.1, hcounts.2.2, rfl, rfl, by linarith⟩

/-- Exact finite score and agreement with the real interpolant. -/
theorem finite_weighted_profile
    {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) (lambda : ℝ) :
    weightedReferenceScore q m lambda =
        (lambda * ((m - 1 : ℕ) : ℝ) + (m : ℝ)) /
          ((q * m - 1 : ℕ) : ℝ) ∧
      weightedReferenceScore q m lambda =
        weightedReferenceInterpolant q lambda m :=
  ⟨weightedReferenceScore_eq (by omega) lambda,
    weightedReferenceScore_eq_interpolant (by omega) hm lambda⟩

/-- Rational weights are ordinary proportions in a finite replicated row
ensemble. -/
theorem finite_replication_model {q m a d : ℕ}
    (hq : 2 ≤ q) (hm : 1 ≤ m) (hd : 0 < d) :
    (((a : ℝ) * ((m - 1 : ℕ) : ℝ) + (d : ℝ) * (m : ℝ)) /
        ((d : ℝ) * ((q * m - 1 : ℕ) : ℝ))) =
      weightedReferenceScore q m ((a : ℝ) / (d : ℝ)) :=
  finiteReplicationProportion_eq (by omega) hm hd

/-- Limit and derivative of the weighted profile. -/
theorem weighted_profile_limit_and_derivative
    {q : ℕ} (hq : 2 ≤ q) (lambda : ℝ) :
    Tendsto (weightedReferenceInterpolant q lambda) atTop
        (nhds ((lambda + 1) / (q : ℝ))) ∧
      ∀ x : ℝ, (q : ℝ) * x - 1 ≠ 0 →
        deriv (weightedReferenceInterpolant q lambda) x =
          (lambda * ((q : ℝ) - 1) - 1) /
            ((q : ℝ) * x - 1) ^ 2 :=
  ⟨weightedReferenceInterpolant_tendsto q (by omega) lambda,
    fun _ hden => weightedReferenceInterpolant_deriv_eq hden⟩

/-- Fibonacci coordinates of reciprocal-golden powers. -/
theorem fibonacci_coordinates (n : ℕ) :
    goldenReciprocal ^ (n + 1) =
      (-1 : ℝ) ^ n *
        ((Nat.fib (n + 1) : ℝ) * goldenReciprocal -
          (Nat.fib n : ℝ)) :=
  goldenReciprocal_power_fibonacci n

/-- Evaluation at a reciprocal golden power is exactly the power equation. -/
theorem interpolated_power_equation
    {q r : ℕ} {lambda : ℝ} (hq : 2 ≤ q) (hr : 1 ≤ r) :
    weightedReferenceInterpolant q lambda
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      goldenReciprocal ^ (r + 1) - lambda * goldenReciprocal ^ r -
        (q : ℝ) * goldenReciprocal + lambda + 1 = 0 := by
  exact weightedInterpolant_goldenPower_iff hq hr

/-- Complete rational classification. -/
theorem rational_weight_classification
    {q r : ℕ} {lambda : ℚ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    weightedReferenceInterpolant q (lambda : ℝ)
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      (q = 2 ∧ lambda = 0 ∧ r = 2) ∨
        (q = 3 ∧ lambda = 1 ∧ r = 2) :=
  weightedInterpolant_rational_classification hq hr hlambda0 hlambda1

/-- Odd integer moduli leave only the full-weight modulus-three endpoint. -/
theorem odd_modulus_rational_endpoint
    {q r : ℕ} {lambda : ℚ} (hq : 2 ≤ q) (hodd : Odd q)
    (hr : 1 ≤ r) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    weightedReferenceInterpolant q (lambda : ℝ)
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      q = 3 ∧ lambda = 1 ∧ r = 2 := by
  rw [rational_weight_classification hq hr hlambda0 hlambda1]
  constructor
  · rintro (⟨rfl, _, _⟩ | hthree)
    · norm_num at hodd
    · exact hthree
  · exact Or.inr

/-- Unique real weight and its exact admissibility window. -/
theorem real_weight_formula_and_window
    {q r : ℕ} (hr : 1 ≤ r) :
    (∀ lambda : ℝ,
      goldenPowerEquation q r lambda = 0 ↔
        lambda = goldenRealWeight q r) ∧
      (goldenRealWeight q r ∈ Set.Icc (0 : ℝ) 1 ↔
        1 + goldenReciprocal ^ (r + 1) ≤
            (q : ℝ) * goldenReciprocal ∧
          (q : ℝ) * goldenReciprocal ≤
            2 - goldenReciprocal ^ (r + 2)) :=
  ⟨fun _ => goldenPowerEquation_zero_iff_realWeight hr,
    goldenRealWeight_mem_unitInterval_iff_window hr⟩

/-- Complete real classification. -/
theorem real_weight_classification
    {q r : ℕ} {lambda : ℝ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    weightedReferenceInterpolant q lambda
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      (q = 2 ∨ q = 3) ∧ 2 ≤ r ∧ lambda = goldenRealWeight q r :=
  weightedInterpolant_real_classification hq hr hlambda

/-- The square endpoints are rational, and every later admissible branch value
is irrational. -/
theorem endpoint_rationality_boundary :
    goldenRealWeight 2 2 = 0 ∧ goldenRealWeight 3 2 = 1 ∧
      (∀ q r : ℕ, (q = 2 ∨ q = 3) → 3 ≤ r →
        Irrational (goldenRealWeight q r)) :=
  ⟨goldenRealWeight_square_endpoints.1,
    goldenRealWeight_square_endpoints.2,
    fun _ _ hq hr => goldenRealWeight_irrational hq hr⟩

/-- First later values, branch directions, and endpoint limits. -/
theorem real_branch_geometry :
    goldenRealWeight 2 3 = goldenReciprocal ^ 3 / 2 ∧
      goldenRealWeight 3 3 = 3 * goldenReciprocal / 2 ∧
      (∀ r : ℕ, 2 ≤ r →
        goldenRealWeight 2 r < goldenRealWeight 2 (r + 1) ∧
          goldenRealWeight 3 (r + 1) < goldenRealWeight 3 r) ∧
      Tendsto (goldenRealWeight 2) atTop
        (nhds (goldenReciprocal ^ 3)) ∧
      Tendsto (goldenRealWeight 3) atTop
        (nhds (3 * goldenReciprocal - 1)) :=
  ⟨goldenRealWeight_first_later_values.1,
    goldenRealWeight_first_later_values.2,
    fun _ hr => goldenRealWeight_branch_directions hr,
    goldenRealWeight_branch_limits.1,
    goldenRealWeight_branch_limits.2⟩

end NField.Papers.RationalRigidityGoldenScale

-- Reuse the original declaration and proof through compiler-resolved references.
#check NField.Alignment.oneDigit_profile_independent_depth
#check NField.Golden.weightedReferenceScore_one
#check NField.Golden.weightedReferenceScore_injective
#check NField.Golden.weightedReferenceScore_irrational_iff

-- Arbitrary coprime bases, with literal canonical digit tails.
#check NField.Alignment.cyclic_shift_block_profile
#check NField.Alignment.cyclic_reference_least_period
#check NField.Alignment.cyclicShiftScore_eq

-- Unit orders, arbitrary-period rigidity, and the actual finite orbit score.
#check NField.Alignment.unit_order_gap
#check NField.Golden.orbit_rational_period_rigidity
#check NField.Golden.cyclicShiftScore_eq_orbitInterpolant
#check NField.Golden.cyclic_shift_finite_weight_interpretation

-- Actual cumulative closure, including phases, binary base and golden endpoints.
#check NField.Alignment.cumulative_closure_length
#check NField.Alignment.cumulative_closure_numerator_and_phase
#check NField.Alignment.cumulative_closure_period_one
#check NField.Alignment.cumulative_closure_base_two
#check NField.Golden.rational_endpoint_cumulative_closure
