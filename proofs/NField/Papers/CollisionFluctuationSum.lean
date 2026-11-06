/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DecimalPrimeMeans
import NField.Alignment.FluctuationSourceDetails
import NField.Alignment.CollisionFluctuationClosure
import NField.Papers.SilentPrimes

/-!
# The Collision Fluctuation Sum

Reader-facing theorem map for the Lean companion to
`papers/collision_fluctuation_sum.tex`.

## Checked here

* The exact zero gate, its width, collision evenness, and the literal
  constructive mean are inherited through their earlier finite proofs.
* The intrinsic lag-one collision count is proved equal to the
  endpoint-corrected diagonal slice count for every admissible base and
  coprime square residue.  The finite table is therefore universal on its
  stated domain, not a decimal regression.
* Complementation proves the floor-table reflection law in every base.  The
  literal unit table has exact mean `-1/2`, while the literal reduced residue
  system modulo `b` has exact remainder mean `1/2-1/b`.
* The constructive correction expansion, sharp finite range, drift
  coefficient, and integrality boundary are proved exactly.
* The forty base-ten unit entries, four class cardinalities, class sums, and
  rational means are kernel-reduced exact certificates.
* A general residual-limit theorem proves the final subtraction step.  When
  the two Mertens-progression component limits used in the manuscript are
  supplied, the coefficient is exactly `-(b-1)/b`.

## Proved analytic inputs and consequences

The fixed-progression prime and Mertens theorems are now proved from pinned
Mathlib and the attributed Tauberian bridge. The actual component sums,
original-cutoff drift, divergence, drift-removed series and absolute
convergence are proved. Exact unit-fiber transport also gives the four
printed limiting prime-class means. The original conditional theorem remains
unchanged, and the observed finite numerical columns retain separate checks.
-/

namespace NField.Papers.CollisionFluctuationSum

open scoped BigOperators Topology
open Filter
open NField.CollisionDefinition
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula
open NField.Alignment.BinDerangements
open NField.Alignment.BinDerangementsClosure
open NField.Alignment.SilentPrimes
open NField.Alignment.SilentPrimesClosure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionPeriodicTable
open NField.Alignment.CollisionFluctuationClosure

/-! ## The collision population -/

/-- The coordinate count used in the manuscript is the intrinsic collision
count, and is exactly twice the positive-comparison count. -/
theorem exact_coordinate_count
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p (by omega) hp.pos) g =
      2 * (positiveComparisonSet b p ((p - 1) / b)
        (gateParameter b p g)).card :=
  NField.Papers.SilentPrimes.collision_coordinate_formula
    hb2 hp hbp hg0 hg1

/-- The exact zero gate and evenness statement used before the prime sum. -/
theorem exact_zero_gate_and_evenness
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    (collisionCount (primeDigitWord b p (by omega) hp.pos) g = 0 ↔
        gateParameter b p g < b) ∧
      Even (collisionCount (primeDigitWord b p (by omega) hp.pos) g) :=
  ⟨NField.Papers.SilentPrimes.zero_gate (by omega) hp hbp hg0 hg1,
    NField.Papers.SilentPrimes.collision_count_even hb2 hp hbp hg0 hg1⟩

/-- Exactly `b-1` nonzero multipliers lie behind the zero gate. -/
theorem exact_zero_gate_width
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] :
    (derangingFamily b p).card = b - 1 :=
  (NField.Papers.SilentPrimes.zero_family_and_width hb2 hp hbp).2

/-- The exact mean over the literal constructive multiplier population. -/
theorem exact_constructive_population_mean {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    ((∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℚ) /
        ((constructiveMultiplierSet b p (by omega) hp).card : ℚ) =
      constructiveMeanValue b Q R :=
  NField.Papers.SilentPrimes.constructive_population_mean
    hb2 hp hbp1 hdivision hR

/-- The two displayed rational forms of the constructive mean agree. -/
theorem exact_constructive_mean_second_form {b Q R : ℕ}
    (hN : 0 < b * (Q - 1) + R) :
    ((Q * (b * (Q - 1) + 2 * R) : ℕ) : ℚ) /
        (b * (Q - 1) + R : ℕ) =
      (Q : ℚ) + (Q * R : ℕ) / (b * (Q - 1) + R : ℕ) :=
  NField.Papers.SilentPrimes.exact_mean_second_form hN

/-- Subtracting the constructive mean gives the manuscript's exact
integer-plus-rational decomposition. -/
theorem exact_fluctuation_decomposition (C Q R N : ℕ) :
    (C : ℚ) - ((Q : ℚ) + (Q * R : ℕ) / N) =
      ((C : ℚ) - Q) - (Q * R : ℕ) / N := by
  ring

/-! ## The finite table -/

/-- The intrinsic collision count is exactly the endpoint-corrected diagonal
slice score. -/
theorem direct_collision_is_diagonal_slice_count
    {b p t a : ℕ} (hb2 : 2 ≤ b) (hp : p = b ^ 2 * t + a)
    (ha1 : 1 ≤ a) (halt : a < b ^ 2) (hcop : a.Coprime (b ^ 2)) :
    (directLagOneCollisionCount b p : ℤ) = sliceCollisionScore b p :=
  directLagOneCollisionCount_eq_sliceCollisionScore hb2 hp ha1 halt hcop

/-- The direct integer deviation is the finite table on every admissible
coprime square progression. -/
theorem direct_finite_table_determination
    {b t a : ℕ} (hb2 : 2 ≤ b) (ha1 : 1 ≤ a)
    (halt : a < b ^ 2) (hcop : a.Coprime (b ^ 2)) :
    directIntegerDeviation b (b ^ 2 * t + a) = fluctuationTable b a :=
  directIntegerDeviation_eq_fluctuationTable hb2 ha1 halt hcop

/-- Exact reflection on every unit coordinate of the finite table. -/
theorem exact_table_reflection {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2) (hcop : a.Coprime (b ^ 2)) :
    fluctuationTable b a + fluctuationTable b (b ^ 2 - a) = -1 :=
  fluctuationTable_reflection hb2 ha halt hcop

/-- The table's sharp finite range on every unit coordinate. -/
theorem exact_table_range {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2) (hcop : a.Coprime (b ^ 2)) :
    -((b : ℤ) - 1) ≤ fluctuationTable b a ∧
      fluctuationTable b a ≤ (b : ℤ) - 2 :=
  sharp_unit_range hb2 ha halt hcop

/-- The exact grand mean on the literal unit table modulo `b^2`. -/
theorem exact_unit_table_grand_mean {b : ℕ} (hb2 : 2 ≤ b) :
    (Fintype.card (PeriodicUnit b) : ℚ)⁻¹ *
      ∑ a : PeriodicUnit b, (fluctuationTable b a : ℚ) = -1 / 2 :=
  periodicUnit_grand_mean hb2

/-- The exact remainder mean on the literal reduced residue system modulo
`b`. -/
theorem exact_remainder_class_mean {b : ℕ} (hb2 : 2 ≤ b) :
    (Fintype.card (BaseUnit b) : ℚ)⁻¹ *
        ∑ u : BaseUnit b, ((u : ℚ) - 1) / b =
      1 / 2 - 1 / b :=
  baseUnit_remainder_mean hb2

/-! ## Correction and coefficient -/

/-- Exact constructive-correction expansion. -/
theorem exact_correction_expansion {b Q R N : ℕ}
    (hb : 0 < b) (hN : 0 < N) (hR : R < b)
    (hrelation : N + b = b * Q + R) :
    ((Q * R : ℕ) : ℚ) / N =
      (R : ℚ) / b + ((R * (b - R) : ℕ) : ℚ) / (b * N) :=
  correction_expansion hb hN hR hrelation

/-- Exact combination of the two finite mean contributions. -/
theorem exact_drift_coefficient (b : ℚ) (hb : b ≠ 0) :
    (-1 / 2) - (1 / 2 - 1 / b) = -(b - 1) / b :=
  drift_coefficient b hb

/-- The base-ten coefficient is exactly `-9/10`. -/
theorem exact_decimal_drift_coefficient :
    (-1 / 2 : ℚ) - (1 / 2 - 1 / 10) = -9 / 10 :=
  decimal_drift_coefficient

/-- Exact integrality boundary for the leading rational correction term. -/
theorem correction_first_term_integral_iff_zero {b R : ℕ}
    (hb : 0 < b) (hR : R < b) :
    (∃ z : ℤ, (z : ℚ) = (R : ℚ) / b) ↔ R = 0 :=
  remainder_term_integral_iff_zero hb hR

/-! ## Exact base-ten table -/

/-- The universal direct theorem specializes to every prime in the earlier
bounded decimal regression set. -/
theorem decimal_direct_table_check :
    ∀ p ∈ decimalRegressionPrimes,
      directIntegerDeviation 10 p = fluctuationTable 10 (p % 100) :=
  decimal_direct_collision_regression

/-- Exact base-ten unit count and grand-table sum. -/
theorem decimal_unit_count_and_grand_sum :
    (reducedResidues 100).card = 40 ∧
      ∑ a ∈ reducedResidues 100, fluctuationTable 10 a = -20 :=
  ⟨decimal_reduced_residue_count, decimal_table_sum⟩

/-- Each displayed final digit has exactly ten unit lifts modulo one hundred. -/
theorem decimal_class_cardinality_check :
    (decimalResidueClass 1).card = 10 ∧
    (decimalResidueClass 3).card = 10 ∧
    (decimalResidueClass 7).card = 10 ∧
    (decimalResidueClass 9).card = 10 :=
  decimal_class_cardinalities

/-- Exact numerators and rational means of the four displayed class rows. -/
theorem decimal_class_sum_and_mean_check :
    ((∑ a ∈ decimalResidueClass 1, fluctuationTable 10 a) = -17 ∧
      (∑ a ∈ decimalResidueClass 3, fluctuationTable 10 a) = -9 ∧
      (∑ a ∈ decimalResidueClass 7, fluctuationTable 10 a) = -1 ∧
      (∑ a ∈ decimalResidueClass 9, fluctuationTable 10 a) = 7) ∧
    (((10 : ℚ)⁻¹ * (-17 : ℚ) = -17 / 10) ∧
      ((10 : ℚ)⁻¹ * (-9 : ℚ) = -9 / 10) ∧
      ((10 : ℚ)⁻¹ * (-1 : ℚ) = -1 / 10) ∧
      ((10 : ℚ)⁻¹ * (7 : ℚ) = 7 / 10)) :=
  ⟨decimal_class_table_sums, decimal_class_table_means⟩

/-! ## Conditional analytic assembly -/

/-- Given the two Mertens-progression residual limits isolated by the
manuscript, their subtraction has exact coefficient `-(b-1)/b`. -/
theorem exact_drift_from_component_limits
    {α : Type*} {l integerPart correction : α → ℝ}
    {κS κR : ℝ} {lfilter : Filter α} (b : ℕ) (hb2 : 2 ≤ b)
    (hS : Tendsto
      (fun x => integerPart x - (-1 / 2) * l x) lfilter (𝓝 κS))
    (hR : Tendsto
      (fun x => correction x - (1 / 2 - 1 / (b : ℝ)) * l x)
      lfilter (𝓝 κR)) :
    Tendsto
      (fun x => (integerPart x - correction x) -
        (-(b - 1 : ℝ) / b) * l x) lfilter (𝓝 (κS - κR)) :=
  collision_drift_limit_from_component_limits b hb2 hS hR

#check exact_coordinate_count
#check exact_zero_gate_and_evenness
#check exact_zero_gate_width
#check exact_constructive_population_mean
#check exact_constructive_mean_second_form
#check exact_fluctuation_decomposition
#check direct_collision_is_diagonal_slice_count
#check direct_finite_table_determination
#check exact_table_reflection
#check exact_table_range
#check exact_unit_table_grand_mean
#check exact_remainder_class_mean
#check exact_correction_expansion
#check exact_drift_coefficient
#check exact_decimal_drift_coefficient
#check correction_first_term_integral_iff_zero
#check decimal_direct_table_check
#check decimal_unit_count_and_grand_sum
#check decimal_class_cardinality_check
#check decimal_class_sum_and_mean_check
#check exact_drift_from_component_limits

end NField.Papers.CollisionFluctuationSum

/-! Analytic results selected from their defining source modules. -/

#check NField.Alignment.ProgressionMertens.real_cutoff_mertens_progression
#check NField.Alignment.CollisionPrimeLimits.lag_one_constructive_prime_drift
#check NField.Alignment.CollisionPrimeLimits.lag_one_drift_removed_limit
#check NField.Alignment.CollisionPrimeLimits.lag_one_prime_sum_tendsto_atBot
#check NField.Alignment.CollisionPrimeLimits.lag_one_raw_prime_drift
#check NField.Alignment.CollisionPrimeLimits.lag_one_correction_prime_drift
#check NField.Alignment.CollisionPrimeLimits.constructive_fluctuation_uniform_bound
#check NField.Alignment.CollisionPrimeLimits.collision_prime_series_absolute_convergence
#check NField.Alignment.CollisionPrimeLimits.decimal_class_prime_mean_limits
#check NField.Alignment.CollisionPrimeLimits.decimal_coarse_constructive_means
#check NField.Alignment.CollisionPrimeLimits.decimal_limiting_means_negative
#check NField.Alignment.CollisionPrimeLimits.raw_collision_uniform_bound
#check NField.Alignment.CollisionPrimeLimits.lag_one_partial_sum_at_one
