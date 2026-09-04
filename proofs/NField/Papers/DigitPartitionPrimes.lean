/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.AlignmentLimitClassification
import NField.Alignment.DigitPartitioningClassification

/-!
# Digit-Partitioning Primes and the Alignment Formula

This thin title-level manifest records the exact correspondence between the
manuscript and reusable theorem objects.  Proof implementations are organized
under `NField.Alignment` by mathematical object.
-/

namespace NField.Papers.DigitPartitionPrimes

open NField.Alignment NField.Golden
open NField.Alignment.ThreeTier

/-- The two definitions of a supported denominator, together with the
termination interpretation used by the common clearing clock. -/
theorem supported_denominator_equivalences {b m : ℕ}
    (hb : 0 < b) (hm : 0 < m) :
    (Supported b m ↔ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ b) ∧
      (Supported b m ↔ TerminatesInBase b 1 m) := by
  exact ⟨supported_iff_every_prime_divisor_divides_base hb hm,
    supported_iff_one_terminates_at_some_depth⟩

/-- The digit map, the manuscript's positional separation property, and the
sharp boundary `p <= b+1` are equivalent. -/
theorem digit_partitioning_characterization {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    (DigitPartitioning b p ↔ p ≤ b + 1) ∧
      (PositionSeparated b p ↔ DigitPartitioning b p) := by
  exact ⟨digitPartitioning_iff hb hp hpb,
    positionSeparated_iff_digitPartitioning hp hpb⟩

/-- At the tight endpoint, the digit map is the displayed bijection and the
next remainder and digit are the stated complements. -/
theorem endpoint_complement_structure {b p : ℕ}
    (_hp : p.Prime) (hbp : p = b + 1) (hb : 1 ≤ b) :
    (∀ r, 0 < r → r < p →
      NField.CollisionDefinition.digitBin b p r = r - 1) ∧
      (∀ r, 0 < r → r < p →
        (b * r) % p = p - r ∧
        NField.CollisionDefinition.digitBin b p r +
          NField.CollisionDefinition.digitBin b p (p - r) = b - 1) := by
  constructor
  · intro r hr0 hr
    exact boundary_digit hbp hr0 hr
  · intro r hr0 hr
    exact ⟨boundary_next_remainder_eq_complement hbp hb hr0 hr,
      boundary_digit_complement hbp hb hr0 hr⟩

/-- Exact quotient-group form of the cyclic-family proposition, including
family count, lifted family size, least remainder period, cyclic digit shifts,
and separation of different families. -/
theorem multiplicative_cycle_partition {b p m : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hm : 1 ≤ m) :
    PrimeRemainderCyclePartitionStatement hp hpb m ∧
      (∀ x y : (ZMod p)ˣ,
        ((x : (ZMod p)ˣ ⧸ primeBaseOrbitSubgroup b p hp hpb) = y ↔
          ∃ j < primeBasePeriod b p hp hpb,
            x * (primeBaseUnit b p hp hpb) ^ j = y)) ∧
      (∀ x : (ZMod p)ˣ, ∀ j s : ℕ,
        primeOrbitDigit hp hpb (x * (primeBaseUnit b p hp hpb) ^ s) j =
          primeOrbitDigit hp hpb x (j + s)) ∧
      (∀ x y : (ZMod p)ˣ,
        (x : (ZMod p)ˣ ⧸ primeBaseOrbitSubgroup b p hp hpb) ≠ y →
          ¬∃ j : ℕ, x * (primeBaseUnit b p hp hpb) ^ j = y) := by
  exact ⟨primeRemainderCyclePartition hp hpb hm,
    fun x y => same_primeBaseOrbit_iff hp hpb x y,
    fun x j s => primeOrbitDigit_mul_base_pow hp hpb x j s,
    fun x y => different_primeBaseOrbits_not_power_shift hp hpb x y⟩

/-- The literal full-period average is independent of every valid common
clearing depth and equals the displayed real formula. -/
theorem synchronized_alignment_well_defined {b p m D E : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hle : p ≤ b + 1)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) =
        clearedAlignmentReal b p m E (primeBasePeriod b p hp hpb) ∧
      clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) =
        digitPartitioningAlignmentFormulaReal p m := by
  have hdp := digitPartitioning_of_le hp.pos hpb hle
  exact ⟨clearedAlignmentReal_independent_of_clearing_depth
      hp hpb hm hD hE,
    clearedDigitPartitioningAlignmentReal_eq hp hpb hdp hm hD
      (primeBasePeriod_pos hp hpb)⟩

/-- Exact synchronized class counts and both normalized forms of the alignment
formula on the original denominator clock. -/
theorem exact_alignment_formula {b p m D : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hle : p ≤ b + 1)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    let L := primeBasePeriod b p hp hpb
    let u := clearingCofactor b m D
    terminatingNumeratorCount p m = m - 1 ∧
      matchingNumeratorCount p m = m ∧
      synchronizedFieldAlignedCount b p m u L = 2 * m - 1 ∧
      synchronizedFieldMatchCount b p m u L = (2 * m - 1) * L ∧
      synchronizedRepetendAlignment b p m u L =
        (2 * m - 1 : ℕ) / (p * m - 1 : ℕ) ∧
      clearedAlignmentReal b p m D L =
        digitPartitioningAlignmentFormulaReal p m := by
  dsimp
  have hdp := digitPartitioning_of_le hp.pos hpb hle
  have hu := prime_coprime_clearingCofactor hp hpb hD
  have hL := primeBasePeriod_pos hp hpb
  exact ⟨terminatingNumeratorCount_eq hp.pos,
    matchingNumeratorCount_eq hp.one_lt,
    synchronizedFieldAlignedCount_eq hp hpb hdp hu hm hL,
    synchronizedFieldMatchCount_eq hp hpb hdp hu hm,
    synchronizedRepetendAlignment_eq hp hpb hdp hu hm hL,
    clearedDigitPartitioningAlignmentReal_eq hp hpb hdp hm hD hL⟩

/-- Termination among the original numerators is exactly the zero residue
class, both at a chosen valid depth and at some finite depth. -/
theorem synchronized_termination_class {b p m D k : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (_hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    (TerminatesAtDepth b k (p * m) D ↔ k % p = 0) ∧
      (TerminatesInBase b k (p * m) ↔ k % p = 0) := by
  exact ⟨terminatesAtDepth_iff_residue_zero hp hpb hD,
    terminatesInBase_iff_residue_zero hp hpb ⟨D, hD⟩⟩

/-- Exact finite certificate for the manuscript's binary synchronization
example. -/
theorem binary_common_clock_example :
    (digitAt 2 3 1 0 = 0 ∧ digitAt 2 3 1 1 = 1) ∧
      (clearedDigit 2 6 1 1 0 = 0 ∧ clearedDigit 2 6 1 1 1 = 1) ∧
      (clearedDigit 2 6 2 1 0 = 1 ∧ clearedDigit 2 6 2 1 1 = 0) ∧
      (clearedDigit 2 6 4 1 0 = 0 ∧ clearedDigit 2 6 4 1 1 = 1) :=
  binary_synchronized_tail_example

/-- The alignment limit is `2/p` along every supported family tending to
infinity. -/
theorem supported_alignment_limit
    {ι : Type*} {l : Filter ι} {b p : ℕ} {m : ι → ℕ}
    (hp : 0 < p) (hsupported : ∀ i, Supported b (m i))
    (hm : Filter.Tendsto m l Filter.atTop) :
    Filter.Tendsto (fun i => digitPartitioningAlignmentFormulaReal p (m i)) l
      (nhds ((2 : ℝ) / p)) :=
  digitPartitioningAlignment_tendsto_along_supported hp hsupported hm

/-- The six selected-base prime lists and every printed three-place limit are
exactly certified. -/
theorem displayed_base_table :
    (digitPartitioningPrimeSet 4 = {3, 5} ∧
      digitPartitioningPrimeSet 6 = {5, 7} ∧
      digitPartitioningPrimeSet 8 = {3, 5, 7} ∧
      digitPartitioningPrimeSet 10 = {3, 7, 11} ∧
      digitPartitioningPrimeSet 12 = {5, 7, 11, 13} ∧
      digitPartitioningPrimeSet 16 = {3, 5, 7, 11, 13, 17}) ∧
    (WithinThreeDecimalRounding (2 / 3) (667 / 1000) ∧
      WithinThreeDecimalRounding (2 / 5) (400 / 1000) ∧
      WithinThreeDecimalRounding (2 / 7) (286 / 1000) ∧
      WithinThreeDecimalRounding (2 / 11) (182 / 1000) ∧
      WithinThreeDecimalRounding (2 / 13) (154 / 1000) ∧
      WithinThreeDecimalRounding (2 / 17) (118 / 1000)) :=
  ⟨selected_base_digitPartitioningPrimeSets,
    selected_base_limit_decimal_roundings⟩

/-- In base ten, the admissible digit-partitioning primes are exactly three,
seven, and eleven. -/
theorem base_ten_digit_partitioning_primes {p : ℕ} (hp : p.Prime) :
    (¬p ∣ 10 ∧ DigitPartitioning 10 p) ↔ p = 3 ∨ p = 7 ∨ p = 11 := by
  rw [← mem_digitPartitioningPrimeSet_iff (by norm_num) hp,
    selected_base_digitPartitioningPrimeSets.2.2.2.1]
  simp

/-- The one-digit, primitive full-orbit, and complement-pair mechanisms in
base ten have the exact periods and separation asserted in the manuscript. -/
theorem decimal_structural_cases :
    primeBasePeriod 10 3 (by norm_num) (by norm_num) = 1 ∧
      primeBasePeriod 10 7 (by norm_num) (by norm_num) = 6 ∧
      primeBasePeriod 10 11 (by norm_num) (by norm_num) = 2 ∧
      PositionSeparated 10 7 ∧
      (∀ r, 0 < r → r < 11 →
        (10 * r) % 11 = 11 - r ∧
        NField.CollisionDefinition.digitBin 10 11 r +
          NField.CollisionDefinition.digitBin 10 11 (11 - r) = 9) :=
  decimal_digitPartitioning_structures

/-- The exact cyclic word at decimal prime seven and its distinct digits. -/
theorem decimal_seven_repetend :
    [digitAt 10 7 1 0, digitAt 10 7 1 1, digitAt 10 7 1 2,
      digitAt 10 7 1 3, digitAt 10 7 1 4, digitAt 10 7 1 5] =
        [1, 4, 2, 8, 5, 7] ∧
      [digitAt 10 7 1 0, digitAt 10 7 1 1, digitAt 10 7 1 2,
        digitAt 10 7 1 3, digitAt 10 7 1 4, digitAt 10 7 1 5].Nodup :=
  decimal_seven_cyclic_word

/-- The opening decimal comparison is exact at both columns of eleven and at
the first collided column of thirteen. -/
theorem opening_decimal_boundary :
    [digitAt 10 11 1 0, digitAt 10 11 2 0, digitAt 10 11 3 0,
      digitAt 10 11 4 0, digitAt 10 11 5 0, digitAt 10 11 6 0,
      digitAt 10 11 7 0, digitAt 10 11 8 0, digitAt 10 11 9 0,
      digitAt 10 11 10 0] =
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] ∧
      [digitAt 10 11 1 1, digitAt 10 11 2 1, digitAt 10 11 3 1,
        digitAt 10 11 4 1, digitAt 10 11 5 1, digitAt 10 11 6 1,
        digitAt 10 11 7 1, digitAt 10 11 8 1, digitAt 10 11 9 1,
        digitAt 10 11 10 1] =
          [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] ∧
      [digitAt 10 13 1 0, digitAt 10 13 2 0, digitAt 10 13 3 0,
        digitAt 10 13 4 0, digitAt 10 13 5 0, digitAt 10 13 6 0,
        digitAt 10 13 7 0, digitAt 10 13 8 0, digitAt 10 13 9 0,
        digitAt 10 13 10 0, digitAt 10 13 11 0,
        digitAt 10 13 12 0] =
          [0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9] :=
  decimal_boundary_digit_columns

/-- Within the admissible class and among primes at least three, the
reciprocal-golden threshold selects exactly prime three, present exactly when
three does not divide the base. -/
theorem reciprocal_golden_selection_by_base {b p : ℕ}
    (hb : 2 ≤ b) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (¬p ∣ b ∧ DigitPartitioning b p ∧
        goldenReciprocal < (2 : ℝ) / p) ↔
      p = 3 ∧ ¬3 ∣ b :=
  golden_selects_prime_three_in_base hb hp hp3

/-- The prime-two exception in odd bases is admissible and has alignment one
at every positive multiplicity. -/
theorem prime_two_degenerate_branch {b : ℕ}
    (hb : 2 ≤ b) (hodd : Odd b) :
    ¬2 ∣ b ∧ DigitPartitioning b 2 ∧
      ∀ m, 1 ≤ m → digitPartitioningAlignmentFormulaReal 2 m = 1 :=
  prime_two_odd_base_degenerate hb hodd

/-- The cited beyond-boundary result in unconditional literal-clock form. -/
theorem beyond_digit_partitioning_uniform_bound {b p m D : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) <
        (3 : ℝ) / 5 ∧
      clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) <
        goldenReciprocal := by
  have hthree := clearedAlignmentReal_lt_three_fifths hp hp5 hpb hb hm hD
    (primeBasePeriod_pos hp hpb)
  exact ⟨hthree, lt_trans hthree
    NField.Alignment.three_fifths_lt_goldenReciprocal⟩

end NField.Papers.DigitPartitionPrimes
