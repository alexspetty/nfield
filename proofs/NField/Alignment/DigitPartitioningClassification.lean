/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DigitPartitionedField
import NField.Alignment.MultiplicativeRemainderOrbits
import NField.Alignment.SynchronizedOneDigitAlignment
import NField.Golden.Threshold

/-!
# Classification data for digit-partitioning primes

This module contains the finite base tables, boundary complement structure,
supported-subsequence limit, and reciprocal-golden selection attached to the
exact digit-partitioning boundary.
-/

namespace NField.Alignment

open NField.Golden
open NField.Alignment.ThreeTier

/-- The literal denominator-clock average equals the closed formula at every
positive synchronized window for a digit-partitioning prime. -/
theorem clearedDigitPartitioningAlignmentReal_eq
    {b p m D L : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hm : 1 ≤ m)
    (hD : m ∣ b ^ D) (hL : 0 < L) :
    clearedAlignmentReal b p m D L =
      digitPartitioningAlignmentFormulaReal p m := by
  rw [clearedAlignmentReal_eq_canonicalRoughAlignmentReal hp.pos hm hD]
  unfold canonicalRoughAlignmentReal
  rw [if_neg hp.ne_one]
  have hformula := synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    hp hpb hdp (prime_coprime_clearingCofactor hp hpb hD) hm hL
  simpa [NField.Golden.alignmentFormulaReal,
    digitPartitioningAlignmentFormulaReal] using hformula

/-- The finite set of primes allowed by the exact digit-partitioning boundary
in base `b`. -/
def digitPartitioningPrimeSet (b : ℕ) : Finset ℕ :=
  (Finset.range (b + 2)).filter fun p => p.Prime ∧ ¬p ∣ b

/-- Membership in the finite classification is exactly admissible digit
partitioning. -/
theorem mem_digitPartitioningPrimeSet_iff {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) :
    p ∈ digitPartitioningPrimeSet b ↔ ¬p ∣ b ∧ DigitPartitioning b p := by
  simp only [digitPartitioningPrimeSet, Finset.mem_filter, Finset.mem_range,
    hp, true_and]
  constructor
  · rintro ⟨hle, hpb⟩
    exact ⟨hpb, digitPartitioning_of_le hp.pos hpb (by omega)⟩
  · rintro ⟨hpb, hdp⟩
    exact ⟨by
      have := (digitPartitioning_iff hb hp hpb).mp hdp
      omega, hpb⟩

/-- Exact selected-base prime lists printed in the manuscript table. -/
theorem selected_base_digitPartitioningPrimeSets :
    digitPartitioningPrimeSet 4 = {3, 5} ∧
      digitPartitioningPrimeSet 6 = {5, 7} ∧
      digitPartitioningPrimeSet 8 = {3, 5, 7} ∧
      digitPartitioningPrimeSet 10 = {3, 7, 11} ∧
      digitPartitioningPrimeSet 12 = {5, 7, 11, 13} ∧
      digitPartitioningPrimeSet 16 = {3, 5, 7, 11, 13, 17} := by
  decide

/-- A displayed three-place decimal is valid when it lies within half a unit
in the third decimal place. -/
def WithinThreeDecimalRounding (value displayed : ℚ) : Prop :=
  |value - displayed| ≤ 1 / 2000

/-- Every numerical limit printed in the selected-base table is correctly
rounded to three decimal places. -/
theorem selected_base_limit_decimal_roundings :
    WithinThreeDecimalRounding (2 / 3) (667 / 1000) ∧
      WithinThreeDecimalRounding (2 / 5) (400 / 1000) ∧
      WithinThreeDecimalRounding (2 / 7) (286 / 1000) ∧
      WithinThreeDecimalRounding (2 / 11) (182 / 1000) ∧
      WithinThreeDecimalRounding (2 / 13) (154 / 1000) ∧
      WithinThreeDecimalRounding (2 / 17) (118 / 1000) := by
  norm_num [WithinThreeDecimalRounding, abs_of_nonneg, abs_of_nonpos]

/-- The exact limit holds along every net of supported multiplicities that
tends to infinity. -/
theorem digitPartitioningAlignment_tendsto_along_supported
    {ι : Type*} {l : Filter ι} {b p : ℕ} {m : ι → ℕ}
    (hp : 0 < p) (_hsupported : ∀ i, Supported b (m i))
    (hm : Filter.Tendsto m l Filter.atTop) :
    Filter.Tendsto (fun i => digitPartitioningAlignmentFormulaReal p (m i)) l
      (nhds ((2 : ℝ) / p)) :=
  (digitPartitioningAlignmentFormulaReal_tendsto hp).comp hm

/-- The binary example distinguishing a common denominator clock from a reset
repetend phase.  The first pair is the reset word for `1/6` and `1/3`; the
remaining pairs are all read after one common base-two digit. -/
theorem binary_synchronized_tail_example :
    (digitAt 2 3 1 0 = 0 ∧ digitAt 2 3 1 1 = 1) ∧
      (clearedDigit 2 6 1 1 0 = 0 ∧ clearedDigit 2 6 1 1 1 = 1) ∧
      (clearedDigit 2 6 2 1 0 = 1 ∧ clearedDigit 2 6 2 1 1 = 0) ∧
      (clearedDigit 2 6 4 1 0 = 0 ∧ clearedDigit 2 6 4 1 1 = 1) := by
  norm_num [digitAt, clearedDigit, NField.CollisionDefinition.digitBin]

/-- At the endpoint `p=b+1`, multiplication by the base sends each nonzero
remainder to its complementary remainder. -/
theorem boundary_next_remainder_eq_complement {b p r : ℕ}
    (hp : p = b + 1) (hb : 1 ≤ b) (hr0 : 0 < r) (hr : r < p) :
    (b * r) % p = p - r := by
  have hp0 : 0 < p := by omega
  have hcast : ((b * r : ℕ) : ZMod p) = ((p - r : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hr)]
    have hbcast : ((b : ℕ) : ZMod p) = -1 := by
      rw [show b = p - 1 by omega, Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    rw [hbcast]
    simp
  exact Nat.mod_eq_of_modEq
    ((ZMod.natCast_eq_natCast_iff' (b * r) (p - r) p).mp hcast)
    (by omega)

/-- The two digits attached to complementary endpoint remainders sum to the
maximal digit `b-1`. -/
theorem boundary_digit_complement {b p r : ℕ}
    (hp : p = b + 1) (hb : 1 ≤ b) (hr0 : 0 < r) (hr : r < p) :
    NField.CollisionDefinition.digitBin b p r +
        NField.CollisionDefinition.digitBin b p (p - r) = b - 1 := by
  have hcomp0 : 0 < p - r := by omega
  have hcomplt : p - r < p := by omega
  rw [boundary_digit hp hr0 hr, boundary_digit hp hcomp0 hcomplt]
  omega

/-- The three base-ten mechanisms are certified by their exact periods and
the boundary complement law. -/
theorem decimal_digitPartitioning_structures :
    primeBasePeriod 10 3 (by norm_num) (by norm_num) = 1 ∧
      primeBasePeriod 10 7 (by norm_num) (by norm_num) = 6 ∧
      primeBasePeriod 10 11 (by norm_num) (by norm_num) = 2 ∧
      PositionSeparated 10 7 ∧
      (∀ r, 0 < r → r < 11 →
        (10 * r) % 11 = 11 - r ∧
        NField.CollisionDefinition.digitBin 10 11 r +
          NField.CollisionDefinition.digitBin 10 11 (11 - r) = 9) := by
  constructor
  · rw [primeBasePeriod, ← orderOf_units, ZMod.coe_unitOfCoprime]
    change orderOf (10 : ZMod 3) = 1
    have h : (10 : ZMod 3) = 1 := by decide
    rw [h, orderOf_one]
  constructor
  · rw [primeBasePeriod, ← orderOf_units, ZMod.coe_unitOfCoprime]
    rw [orderOf_eq_iff (by norm_num : 0 < 6)]
    constructor
    · decide
    · intro q hq hq0
      interval_cases q <;> decide
  constructor
  · rw [primeBasePeriod, ← orderOf_units, ZMod.coe_unitOfCoprime]
    rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    constructor
    · decide
    · intro q hq hq0
      interval_cases q
      decide
  constructor
  · exact (positionSeparated_iff_digitPartitioning
      (b := 10) (p := 7) (by norm_num) (by norm_num)).2
      ((digitPartitioning_iff (b := 10) (p := 7)
        (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num))
  · intro r hr0 hr
    exact ⟨boundary_next_remainder_eq_complement
        (b := 10) (p := 11) (r := r) rfl (by norm_num) hr0 hr,
      boundary_digit_complement
        (b := 10) (p := 11) (r := r) rfl (by norm_num) hr0 hr⟩

/-- The full base-ten repetend of `1/7` is the displayed six-digit cyclic word
and its digits are pairwise distinct. -/
theorem decimal_seven_cyclic_word :
    [digitAt 10 7 1 0, digitAt 10 7 1 1, digitAt 10 7 1 2,
      digitAt 10 7 1 3, digitAt 10 7 1 4, digitAt 10 7 1 5] =
        [1, 4, 2, 8, 5, 7] ∧
      [digitAt 10 7 1 0, digitAt 10 7 1 1, digitAt 10 7 1 2,
        digitAt 10 7 1 3, digitAt 10 7 1 4, digitAt 10 7 1 5].Nodup := by
  norm_num [digitAt, NField.CollisionDefinition.digitBin]

/-- The exact decimal columns that mark the last injective prime and the first
collided prime.  The two columns for eleven are permutations of all ten digits;
the first column for thirteen repeats exactly three and six. -/
theorem decimal_boundary_digit_columns :
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
          [0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9] := by
  norm_num [digitAt, NField.CollisionDefinition.digitBin]

/-- Across all bases, reciprocal-golden selection inside the admissible
digit-partitioning class is exactly prime three, and it is present precisely
when the base is not divisible by three. -/
theorem golden_selects_prime_three_in_base {b p : ℕ}
    (hb : 2 ≤ b) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (¬p ∣ b ∧ DigitPartitioning b p ∧
        goldenReciprocal < (2 : ℝ) / p) ↔
      p = 3 ∧ ¬3 ∣ b := by
  constructor
  · rintro ⟨hpb, _hdp, hgolden⟩
    have hp_eq : p = 3 := by
      by_contra hne
      have hp5 : 5 ≤ p := by
        have hpne4 : p ≠ 4 := by
          intro hp4
          subst p
          norm_num at hp
        omega
      have hpReal : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hle : (2 : ℝ) / p ≤ 2 / 5 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpReal
      exact (not_lt_of_ge hle) (lt_trans two_fifths_lt_goldenReciprocal hgolden)
    subst p
    exact ⟨rfl, hpb⟩
  · rintro ⟨rfl, h3b⟩
    refine ⟨h3b, digitPartitioning_of_le (by norm_num) h3b (by omega), ?_⟩
    exact goldenReciprocal_lt_two_thirds

/-- Prime two is the odd-base degenerate branch: it is admissible and its
finite alignment formula is identically one. -/
theorem prime_two_odd_base_degenerate {b : ℕ}
    (hb : 2 ≤ b) (hodd : Odd b) :
    ¬2 ∣ b ∧ DigitPartitioning b 2 ∧
      ∀ m, 1 ≤ m → digitPartitioningAlignmentFormulaReal 2 m = 1 := by
  have h2b : ¬2 ∣ b := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  refine ⟨h2b, digitPartitioning_of_le (by norm_num) h2b (by omega), ?_⟩
  intro m hm
  unfold digitPartitioningAlignmentFormulaReal
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : (2 : ℝ) * m - 1 ≠ 0 := by nlinarith
  apply (div_eq_one_iff_eq hden).2
  ring

end NField.Alignment
