/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CanonicalThreeTierClassification

/-!
# The Three-Tier Theorem

Thin manuscript-facing theorem map.  Reusable mathematics lives in modules
named after the supported-rough decomposition, synchronized alignment, radix
complement, and canonical classification objects.
-/

namespace NField.Papers.ThreeTierTheorem

open Filter NField.Alignment NField.Alignment.ThreeTier NField.Golden

/-- Manuscript definition of the largest supported divisor and complementary
rough part, including maximality. -/
theorem canonical_supported_rough_decomposition {b n : ℕ} (hn : 0 < n) :
    Supported b (supportedPart b n) ∧
      supportedPart b n ∣ n ∧
      roughPart b n * supportedPart b n = n ∧
      Nat.Coprime (roughPart b n) b ∧
      ∀ d : ℕ, Supported b d → d ∣ n → d ≤ supportedPart b n := by
  exact ⟨supportedPart_supported hn, supportedPart_dvd hn,
    roughPart_mul_supportedPart hn, roughPart_coprime_base hn,
    fun d hd hdn => supportedDivisor_le_supportedPart hn hd hdn⟩

/-- The supported-coprime factorization is the canonical one and is unique. -/
theorem canonical_decomposition_uniqueness {b n t m : ℕ}
    (hn : n = t * m) (ht : 0 < t) (hm : 0 < m)
    (hmSupported : Supported b m) (hcop : Nat.Coprime t b) :
    supportedPart b n = m ∧ roughPart b n = t :=
  supported_coprime_decomposition_unique hn ht hm hmSupported hcop

/-- A valid common clearing depth exists, the composite rough period is
positive, and the resulting alignment is independent of the chosen depth. -/
theorem synchronized_alignment_well_defined {b n : ℕ} (hn : 2 ≤ n) :
    ∃ D : ℕ, supportedPart b n ∣ b ^ D ∧
      0 < canonicalAlignmentPeriod b n (by omega) ∧
      ∀ E : ℕ, supportedPart b n ∣ b ^ E →
        canonicalSynchronizedAlignmentReal b n D (by omega) =
          canonicalSynchronizedAlignmentReal b n E (by omega) := by
  have hnPos : 0 < n := by omega
  rcases supportedPart_supported (b := b) hnPos with ⟨D, hD⟩
  refine ⟨D, hD, canonicalAlignmentPeriod_pos hnPos, ?_⟩
  intro E hE
  exact canonicalSynchronizedAlignmentReal_independent_of_clearing_depth
    hnPos hD hE

/-- Every reduced rough denominator has a period dividing the full canonical
rough-part period. -/
theorem reduced_rough_period_divides_full_period {b n d : ℕ}
    (hn : 0 < n) (hd : d ∣ roughPart b n) :
    coprimeBasePeriod b d
        (Nat.Coprime.of_dvd_left hd (roughPart_coprime_base (b := b) hn)) ∣
      canonicalAlignmentPeriod b n hn := by
  exact divisor_coprimeBasePeriod_dvd (roughPart_coprime_base (b := b) hn) hd

/-- A numerator terminates exactly when the rough part divides it, and the
literal terminating set has the manuscript's exact cardinality. -/
theorem terminating_fraction_classification {b n k : ℕ} (hn : 0 < n) :
    (TerminatesInBase b k n ↔ roughPart b n ∣ k) ∧
      (canonicalTerminatingNumerators b n).card = supportedPart b n - 1 :=
  ⟨canonicalNumerator_terminates_iff hn,
    canonicalTerminatingNumerators_card hn⟩

/-- Every denominator supported by the base has alignment one. -/
theorem supported_denominator_alignment_one {b n D : ℕ}
    (hn : 0 < n) (hnSupported : Supported b n)
    (hD : supportedPart b n ∣ b ^ D) :
    canonicalSynchronizedAlignmentReal b n D hn = 1 :=
  supportedDenominator_canonicalAlignment_eq_one hn hnSupported hD

/-- The digit complement identity itself is independent of base parity. -/
theorem radix_complement_identity_any_base {b t m k D j : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hm : 0 < m)
    (hD : m ∣ b ^ D) (hcop : Nat.Coprime t b)
    (hk : k < t * m) (hnonterm : ¬t ∣ k) :
    clearedDigit b (t * m) (t * m - k) D j =
      b - 1 - clearedDigit b (t * m) k D j :=
  clearedDigit_complementary_numerators hb ht hm hD hcop hk hnonterm

/-- The literal original-denominator digits of complementary nonterminating
fractions are radix complements; in an even base they cannot both match the
reference, and their total match count is at most one period. -/
theorem literal_complement_pairing {b n D k j L : ℕ}
    (hb : 0 < b) (hbeven : Even b) (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D) (_hkPos : 0 < k) (hk : k < n)
    (hnonterm : ¬TerminatesInBase b k n) :
    ¬TerminatesInBase b (n - k) n ∧
      clearedDigit b n (n - k) D j = b - 1 - clearedDigit b n k D j ∧
      ¬(clearedMatchAt b (roughPart b n) (supportedPart b n) k D j ∧
        clearedMatchAt b (roughPart b n) (supportedPart b n) (n - k) D j) ∧
      clearedNumeratorMatchCount b (roughPart b n) (supportedPart b n) k D L +
        clearedNumeratorMatchCount b (roughPart b n) (supportedPart b n)
          (n - k) D L ≤ L := by
  let t := roughPart b n
  let m := supportedPart b n
  have ht : 0 < t := roughPart_pos hn
  have hm : 0 < m := supportedPart_pos hn
  have hcop : Nat.Coprime t b := roughPart_coprime_base hn
  have hdecomp : t * m = n := by
    simpa [t, m] using roughPart_mul_supportedPart (b := b) hn
  have hnondiv : ¬t ∣ k := by
    intro hdiv
    exact hnonterm ((canonicalNumerator_terminates_iff hn).mpr (by simpa [t] using hdiv))
  have hmateNondiv : ¬t ∣ t * m - k :=
    complementNumerator_nonterminating ht (by simpa [hdecomp] using hk) hnondiv
  have hmateNonterm : ¬TerminatesInBase b (n - k) n := by
    rw [canonicalNumerator_terminates_iff hn]
    simpa [t, hdecomp] using hmateNondiv
  refine ⟨hmateNonterm, ?_, ?_, ?_⟩
  · simpa [hdecomp] using clearedDigit_complementary_numerators
      hb ht hm hD hcop (by simpa [hdecomp] using hk) hnondiv (j := j)
  · simpa [hdecomp] using clearedMatches_complementary_exclusive
      hb ht hm hD hcop hbeven (by simpa [hdecomp] using hk) hnondiv (j := j)
  · simpa [hdecomp] using clearedNumeratorMatchCount_pair_le
      hb ht hm hD hcop hbeven (by simpa [hdecomp] using hk) hnondiv (L := L)

/-- The nonterminating rows have the exact manuscript count, split into
fixed-point-free complementary pairs. -/
theorem nonterminating_complement_pair_inventory {b n : ℕ}
    (hn : 0 < n) (hbeven : Even b) :
    (canonicalNonterminatingNumerators b n).card =
        (roughPart b n - 1) * supportedPart b n ∧
      Even ((canonicalNonterminatingNumerators b n).card) ∧
      (canonicalNonterminatingNumerators b n).card / 2 =
        ((roughPart b n - 1) * supportedPart b n) / 2 ∧
      ∀ k : ℕ,
        roughPart b n * supportedPart b n - k = k → roughPart b n ∣ k := by
  have hpairs := canonicalNonterminatingComplementPairCount (b := b) hn hbeven
  exact ⟨canonicalNonterminatingNumerators_card hn, hpairs.1, hpairs.2,
    fun k hfix => complementNumerator_fixed_implies_terminating hbeven
      (roughPart_coprime_base (b := b) hn) hfix⟩

/-- The exact complement bound and its strict comparison with the rough
ceiling. -/
theorem radix_complement_upper_bound {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (hn : 2 ≤ n)
    (hD : supportedPart b n ∣ b ^ D) (ht : roughPart b n ≠ 1) :
    canonicalSynchronizedAlignmentReal b n D (by omega) ≤
        finiteComplementBoundReal (roughPart b n) (supportedPart b n) ∧
      finiteComplementBoundReal (roughPart b n) (supportedPart b n) <
        roughCeilingReal (roughPart b n) :=
  canonicalSynchronizedAlignmentReal_upper_bound (by omega) hbeven (by omega) hD ht

/-- Rough parts are odd in even bases and are at least five outside the two
distinguished cores. -/
theorem rough_core_arithmetic {b n : ℕ} (hbeven : Even b) (hn : 0 < n)
    (ht1 : roughPart b n ≠ 1) (ht3 : roughPart b n ≠ 3) :
    Odd (roughPart b n) ∧ 5 ≤ roughPart b n := by
  have hcop := roughPart_coprime_base (b := b) hn
  exact ⟨roughPart_odd_of_even_base hcop hbeven,
    roughPart_ge_five (roughPart_pos hn) hcop hbeven ht1 ht3⟩

/-- The exact three-core family, its continuous crossing point, endpoint
tests, and strict finite ceiling. -/
theorem exact_three_core_family {b m D : ℕ}
    (hb : 2 ≤ b) (h3b : ¬3 ∣ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b 3 m D
        (coprimeBasePeriod b 3
          (Nat.prime_three.coprime_iff_not_dvd.mpr h3b)) =
        alignmentFormulaReal 3 m ∧
      ((7 : ℝ) / 11 ≤ alignmentFormulaReal 3 m ↔ 4 ≤ m) ∧
      alignmentFormulaReal 3 m < (2 : ℝ) / 3 ∧
      (alignmentFormulaReal 3 m = (3 : ℝ) / 5 ↔ m = 2) ∧
      (alignmentFormulaReal 3 m = (7 : ℝ) / 11 ↔ m = 4) := by
  exact ⟨threeCoreAlignmentFormula hb h3b hm hD,
    threeCore_ge_seven_elevenths_iff hm,
    threeCore_lt_two_thirds hm,
    threeCore_eq_three_fifths_iff hm,
    threeCore_eq_seven_elevenths_iff hm⟩

/-- The continuous golden crossing is exactly `phi^2`; supported integer
scales skip three when three does not divide the base, so the first is four. -/
theorem exact_golden_crossing {b m : ℕ} (h3b : ¬3 ∣ b)
    (hm : 1 ≤ m) (hmSupported : Supported b m) :
    (∀ x : ℝ, 1 ≤ x →
      ((2 * x - 1) / (3 * x - 1) = goldenReciprocal ↔
        x = goldenRatio ^ 2)) ∧
      (goldenReciprocal ≤ alignmentFormulaReal 3 m ↔ 4 ≤ m) := by
  exact ⟨fun x hx => threeCoreProfile_eq_golden_iff hx,
    threeCore_golden_threshold_supported hm hmSupported h3b⟩

/-- Exact rational enclosure of the reciprocal golden ratio. -/
theorem separating_interval :
    (3 : ℝ) / 5 < goldenReciprocal ∧
      goldenReciprocal < (7 : ℝ) / 11 :=
  reciprocalGolden_separating_interval

/-- The complete three mutually exclusive cases for an arbitrary denominator. -/
theorem three_tier_cases {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    (roughPart b n = 1 ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) = 1) ∨
      (roughPart b n = 3 ∧ 4 ≤ supportedPart b n ∧
        (7 : ℝ) / 11 ≤ canonicalSynchronizedAlignmentReal b n D (by omega) ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) < (2 : ℝ) / 3) ∨
      (roughPart b n ≠ 1 ∧
        ¬(roughPart b n = 3 ∧ 4 ≤ supportedPart b n) ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) ≤ (3 : ℝ) / 5) :=
  canonicalThreeTierCases hb hbeven h3b hn hD

/-- No canonical alignment lies in the open interval between the sharp
endpoints. -/
theorem forbidden_alignment_interval {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    ¬((3 : ℝ) / 5 < canonicalSynchronizedAlignmentReal b n D (by omega) ∧
      canonicalSynchronizedAlignmentReal b n D (by omega) < (7 : ℝ) / 11) :=
  (canonicalThreeTierGapCertificate hb hbeven h3b hn hD).1

/-- The manuscript's final threshold classification stated directly in terms
of the original denominator. -/
theorem reciprocal_golden_classification {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    goldenReciprocal ≤ canonicalSynchronizedAlignmentReal b n D (by omega) ↔
      Supported b n ∨
        ∃ m : ℕ, n = 3 * m ∧ Supported b m ∧ 4 ≤ m :=
  canonicalAlignment_ge_golden_iff_supported_or_three_supported
    hb hbeven h3b hn hD

/-- Both interval endpoints have their claimed unique denominators. -/
theorem unique_endpoint_denominators {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    (canonicalSynchronizedAlignmentReal b n D (by omega) = (3 : ℝ) / 5 ↔
        n = 6) ∧
      (canonicalSynchronizedAlignmentReal b n D (by omega) = (7 : ℝ) / 11 ↔
        n = 12) :=
  ⟨canonicalAlignment_eq_three_fifths_iff_denominator_six
      hb hbeven h3b hn hD,
    canonicalAlignment_eq_seven_elevenths_iff_denominator_twelve
      hb hbeven h3b hn hD⟩

/-- Base ten is the exact decimal specialization of the classification. -/
theorem decimal_classification {n D : ℕ} (hn : 2 ≤ n)
    (hD : supportedPart 10 n ∣ 10 ^ D) :
    goldenReciprocal ≤ canonicalSynchronizedAlignmentReal 10 n D (by omega) ↔
      Supported 10 n ∨
        ∃ m : ℕ, n = 3 * m ∧ Supported 10 m ∧ 4 ≤ m := by
  exact reciprocal_golden_classification (by norm_num) (by norm_num)
    (by norm_num) hn hD

/-- The manuscript's two concrete canonical-decomposition examples. -/
theorem decimal_decomposition_examples :
    supportedPart 10 60 = 20 ∧ roughPart 10 60 = 3 ∧
      supportedPart 10 28 = 4 ∧ roughPart 10 28 = 7 :=
  decimal_supported_rough_examples

/-- Decimal rough cores outside one and three begin at seven, giving the
strict form of the displayed four-sevenths ceiling. -/
theorem decimal_other_core_ceiling {n D : ℕ} (hn : 2 ≤ n)
    (hD : supportedPart 10 n ∣ 10 ^ D)
    (ht1 : roughPart 10 n ≠ 1) (ht3 : roughPart 10 n ≠ 3) :
    7 ≤ roughPart 10 n ∧
      canonicalSynchronizedAlignmentReal 10 n D (by omega) < (4 : ℝ) / 7 :=
  ⟨decimalRoughPart_ge_seven (by omega) ht1 ht3,
    decimalAlignment_le_four_sevenths hn hD ht1 ht3⟩

/-- The only decimal three-core denominators below the second tier are three
and six. -/
theorem decimal_three_core_below_second_tier {n : ℕ} (hn : 0 < n)
    (ht : roughPart 10 n = 3) (hm4 : supportedPart 10 n < 4) :
    n = 3 ∨ n = 6 :=
  decimalThreeCore_below_four hn ht hm4

/-- The exact seven-core family tends to two-sevenths while its deliberately
uniform complement bound tends to four-sevenths. -/
theorem decimal_seven_core_formula_and_limits {m D : ℕ}
    (hm : 1 ≤ m) (hD : m ∣ 10 ^ D) :
    clearedAlignmentReal 10 7 m D (coprimeBasePeriod 10 7 (by norm_num)) =
        alignmentFormulaReal 7 m ∧
      Tendsto (alignmentFormulaReal 7) atTop (nhds ((2 : ℝ) / 7)) ∧
      Tendsto (finiteComplementBoundReal 7) atTop (nhds ((4 : ℝ) / 7)) := by
  refine ⟨decimalSevenCoreAlignmentFormula hm hD,
    decimalSevenCoreFormula_tendsto, ?_⟩
  convert finiteComplementBoundReal_tendsto (t := 7) (by norm_num) using 1
  norm_num [roughCeilingReal]

/-- Exact odd-base obstructions to the even-base complement count. -/
theorem odd_base_obstructions {b m D : ℕ}
    (hb : 2 ≤ b) (hodd : Odd b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    b - 1 - ((b - 1) / 2) = (b - 1) / 2 ∧
      (roughPart 3 2 = 2 ∧ ¬TerminatesInBase 3 1 2 ∧ 2 - 1 = 1) ∧
      clearedAlignmentReal b 2 m D
        (coprimeBasePeriod b 2
          (Nat.prime_two.coprime_iff_not_dvd.mpr
            ((prime_two_odd_base_degenerate hb hodd).1))) = 1 :=
  ⟨oddBase_middleDigit_self_complement hodd,
    oddBase_nonterminating_fixed_point_example,
    oddBase_twoCore_alignment_one hb hodd hm hD⟩

end NField.Papers.ThreeTierTheorem
