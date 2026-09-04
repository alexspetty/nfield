/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPeriodicTableClosure

/-!
# The Collision Periodic Table

Reader-facing theorem map for the Lean companion to
`papers/collision_periodic_table.tex`.

## Checked here

* The direct lag-one collision deviation depends only on the residue modulo
  `b^2`, including the quotient-zero range below `b^2`.
* The complementary floor increments are proved locally at the first,
  interior, and last diagonal slices.  Summing them proves the concrete table
  reflection law `T_b(a) + T_b(b^2-a) = -1` for every unit class.
* Every table value lies in the sharp interval from `-(b-1)` through `b-2`.
  Both endpoint formulas are proved for every base `b >= 2`.
* Complementation is constructed as an involution on the actual finite type
  of unit representatives.  It proves that exactly `phi(b^2)/2` values are
  negative and that the exact grand mean is `-1/2`.
* The complete forty-cell decimal table and all displayed selected-base sign
  counts are checked by exact evaluation.
* A direct digit-collision regression independently compares the original
  collision definition with the finite table for every coprime input `N`
  satisfying `2 ≤ N < 4b^2` in bases two through twelve.

## Proof boundary

The direct-count bijection, endpoint-corrected diagonal-slice score, finite
table reduction, reflection law, extrema, sign balance, and mean are all
encoded for the manuscript's stated domains.  The bounded regression remains
as an independent executable certificate of the direct definitions.

No manuscript claim failed during formalization, and no unchecked declaration
is used here.
-/

namespace NField.Papers.CollisionPeriodicTable

open scoped BigOperators
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionPeriodicTable
open NField.Alignment.CollisionPeriodicTableClosure

/-- The original digit-collision deviation is exactly the table entry selected
by reduction modulo `b^2`. -/
theorem direct_fingerprint_by_residue {b N : ℕ} (hb2 : 2 ≤ b)
    (hN2 : 2 ≤ N) (hcop : N.Coprime b) :
    directIntegerDeviation b N =
      fluctuationTable b (N % (b ^ 2)) :=
  directIntegerDeviation_eq_table_mod_square hb2 hN2 hcop

/-- Exact `b^2` periodicity after reduction to the diagonal slice formula. -/
theorem finite_table_periodicity {b t a : ℕ}
    (hb2 : 2 ≤ b) (ha : 0 < a) (hcop : Nat.Coprime a (b ^ 2)) :
    sliceDeviation b (b ^ 2 * t + a) = fluctuationTable b a :=
  sliceDeviation_eq_fluctuationTable hb2 ha hcop

/-- The concrete finite table has pair sum `-1` on every unit class. -/
theorem exact_table_reflection {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2)
    (hcop : Nat.Coprime a (b ^ 2)) :
    fluctuationTable b a + fluctuationTable b (b ^ 2 - a) = -1 :=
  fluctuationTable_reflection hb2 ha halt hcop

/-- Every unit-class value lies in the manuscript's sharp interval. -/
theorem exact_sharp_range {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2)
    (hcop : Nat.Coprime a (b ^ 2)) :
    -((b : ℤ) - 1) ≤ fluctuationTable b a ∧
      fluctuationTable b a ≤ (b : ℤ) - 2 :=
  sharp_unit_range hb2 ha halt hcop

/-- The upper endpoint is attained by the class `b-1`. -/
theorem upper_endpoint_attained {b : ℕ} (hb2 : 2 ≤ b) :
    fluctuationTable b (b - 1) = (b : ℤ) - 2 :=
  fluctuationTable_at_upper_endpoint hb2

/-- The complementary class attains the lower endpoint. -/
theorem lower_endpoint_attained {b : ℕ} (hb2 : 2 ≤ b) :
    fluctuationTable b (b ^ 2 - (b - 1)) = -((b : ℤ) - 1) :=
  fluctuationTable_at_lower_endpoint hb2

/-- Exactly half of the `phi(b^2)` unit representatives are negative. -/
theorem exact_negative_class_count {b : ℕ} (hb2 : 2 ≤ b) :
    2 * Fintype.card
      {a : PeriodicUnit b // fluctuationTable b a < 0} =
        Nat.totient (b ^ 2) :=
  periodicUnit_negative_count hb2

/-- The exact grand mean over unit representatives is `-1/2`. -/
theorem exact_grand_mean {b : ℕ} (hb2 : 2 ≤ b) :
    (Fintype.card (PeriodicUnit b) : ℚ)⁻¹ *
      ∑ a : PeriodicUnit b, (fluctuationTable b a : ℚ) = -1 / 2 :=
  periodicUnit_grand_mean hb2

/-- The complete displayed decimal table, including every unit coordinate. -/
theorem decimal_table_check :
    decimalDisplayedTable.toFinset =
      (reducedResidues 100).image fun a => (a, fluctuationTable 10 a) :=
  decimal_displayed_table_complete

/-- The seven displayed selected-base sign summaries. -/
theorem selected_base_summary_check :
    ((reducedResidues (3 ^ 2)).card,
      (positiveUnitClasses 3).card, (zeroUnitClasses 3).card,
      (negativeUnitClasses 3).card) = (6, 1, 2, 3) ∧
    ((reducedResidues (5 ^ 2)).card,
      (positiveUnitClasses 5).card, (zeroUnitClasses 5).card,
      (negativeUnitClasses 5).card) = (20, 4, 6, 10) ∧
    ((reducedResidues (6 ^ 2)).card,
      (positiveUnitClasses 6).card, (zeroUnitClasses 6).card,
      (negativeUnitClasses 6).card) = (12, 2, 4, 6) ∧
    ((reducedResidues (7 ^ 2)).card,
      (positiveUnitClasses 7).card, (zeroUnitClasses 7).card,
      (negativeUnitClasses 7).card) = (42, 10, 11, 21) ∧
    ((reducedResidues (8 ^ 2)).card,
      (positiveUnitClasses 8).card, (zeroUnitClasses 8).card,
      (negativeUnitClasses 8).card) = (32, 7, 9, 16) ∧
    ((reducedResidues (10 ^ 2)).card,
      (positiveUnitClasses 10).card, (zeroUnitClasses 10).card,
      (negativeUnitClasses 10).card) = (40, 8, 12, 20) ∧
    ((reducedResidues (12 ^ 2)).card,
      (positiveUnitClasses 12).card, (zeroUnitClasses 12).card,
      (negativeUnitClasses 12).card) = (48, 11, 13, 24) :=
  selected_base_sign_counts

/-- Direct collision/table agreement over the stated bounded verification. -/
theorem small_base_direct_check :
    ∀ b ∈ checkedSmallBases,
      ∀ N ∈ checkedInputs b,
        directIntegerDeviation b N =
          fluctuationTable b (N % (b ^ 2)) :=
  small_base_direct_collision_regression

#check finite_table_periodicity
#check direct_fingerprint_by_residue
#check exact_table_reflection
#check exact_sharp_range
#check upper_endpoint_attained
#check lower_endpoint_attained
#check exact_negative_class_count
#check exact_grand_mean
#check decimal_table_check
#check selected_base_summary_check
#check small_base_direct_check

end NField.Papers.CollisionPeriodicTable
