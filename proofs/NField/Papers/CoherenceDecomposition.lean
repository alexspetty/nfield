/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SynchronizedPairwiseAlignment
import NField.Alignment.SynchronizedPeriodAlignment

/-!
# The Coherence Decomposition

Thin manuscript-facing correspondence map.  Reusable mathematics is owned by
the synchronized pairwise alignment, supported-rough factorization, digit
partitioning, period, and golden-threshold objects.
-/

namespace NField.Papers.CoherenceDecomposition

open Filter
open NField.Alignment
open NField.Alignment.CoherenceDecomposition
open NField.Alignment.DeficitLattice
open NField.Alignment.SynchronizedPairwiseAlignment
open NField.Golden

/-- The supported part is the unique largest supported divisor and the rough
part is its coprime complement. -/
theorem canonical_supported_rough_factorization {b n : ℕ} (hn : 0 < n) :
    Supported b (supportedPart b n) ∧
      supportedPart b n ∣ n ∧
      roughPart b n * supportedPart b n = n ∧
      Nat.Coprime (roughPart b n) b ∧
      (∀ d : ℕ, Supported b d → d ∣ n → d ≤ supportedPart b n) ∧
      (∀ q s : ℕ, n = q * s → 0 < q → 0 < s → Supported b s →
        Nat.Coprime q b → supportedPart b n = s ∧ roughPart b n = q) :=
  canonicalSupportedRoughFactorization hn

/-- Increasing the common clearing depth merely rotates both rough-residue
streams over a complete period. -/
theorem synchronized_pair_score_independent_of_later_clearing_depth
    {b q s D extra r t length : ℕ} (hD : s ∣ b ^ D)
    (hperiod : b ^ length % q = 1 % q) :
    periodicPairMatchCount b q (clearingCofactor b s (D + extra)) r t length =
      periodicPairMatchCount b q (clearingCofactor b s D) r t length :=
  periodicPairMatchCount_independent_of_later_clearing_depth hD hperiod

/-- Injectivity of the prime digit function is exactly the sharp boundary
`p ≤ b + 1`. -/
theorem digit_partitioning_boundary {b p : ℕ} (hb : 2 ≤ b)
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    DigitPartitioning b p ↔ p ≤ b + 1 :=
  digitPartitioningPrime_iff_le_base_succ hb hp hpb

/-- The literal finite sample space contains the expected total number of
unordered pairs and the exact two class contributions. -/
theorem unordered_pair_class_count {p s : ℕ} (hp : Nat.Prime p) :
    (numeratorPairs p s).card = Nat.choose (p * s - 1) 2 ∧
      (singleResiduePairs p s).card =
        Nat.choose (s - 1) 2 + (p - 1) * Nat.choose s 2 :=
  ⟨numeratorPairs_card p s, singleResiduePairs_card hp.one_lt⟩

/-- The main theorem is computed from the manuscript's literal reference and
distinct-unordered-pair means, on one common positive synchronized window. -/
theorem exact_literal_decomposition
    {b p s length : ℕ} (hb : 2 ≤ b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hle : p ≤ b + 1) (hs : 1 ≤ s)
    (hsupported : Supported b s) (hps : 3 ≤ p * s)
    (hlength : 0 < length) :
    ∃ D : ℕ, s ∣ b ^ D ∧
      synchronizedRepetendAlignment b p s (clearingCofactor b s D) length =
        ((2 : ℚ) * s - 1) / ((p : ℚ) * s - 1) ∧
      synchronizedPairwiseMean b p s (clearingCofactor b s D) length =
        ((s : ℚ) - 1) / ((p : ℚ) * s - 1) ∧
      synchronizedRepetendAlignment b p s (clearingCofactor b s D) length -
          synchronizedPairwiseMean b p s (clearingCofactor b s D) length =
        (s : ℚ) / ((p : ℚ) * s - 1) := by
  rcases hsupported with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  exact literalPrimeCoreDecomposition hp hpb
    ((digit_partitioning_boundary hb hp hpb).mpr hle) hD hs hps hlength

/-- The pairwise background is exactly the terminating contribution to the
reference mean, and the residual is exactly the reference residue class. -/
theorem normalized_class_contributions {p s : ℕ} (hp : Nat.Prime p)
    (hs : 1 ≤ s) (hps : 3 ≤ p * s) :
    ((terminatingNumeratorCount p s : ℕ) : ℚ) /
          (((p * s - 1 : ℕ) : ℚ)) = pairwiseAlignmentFormula p s ∧
      ((residueCount p 1 s : ℕ) : ℚ) /
          (((p * s - 1 : ℕ) : ℚ)) = focusedAlignmentFormula p s :=
  normalizedClassContributionInterpretation hp hs hps

/-- The three limits hold along every unbounded sequence of supported scales,
which states the manuscript's restricted limit literally. -/
theorem three_supported_limits
    {b p : ℕ} (hp : Nat.Prime p) {s : ℕ → ℕ}
    (hsupported : ∀ k, Supported b (s k)) (hs : Tendsto s atTop atTop) :
    Tendsto (fun k => alignmentFormulaReal p (s k)) atTop
        (nhds ((2 : ℝ) / p)) ∧
      Tendsto (fun k => focusedAlignmentFormulaReal p (s k)) atTop
        (nhds ((1 : ℝ) / p)) ∧
      Tendsto (fun k => pairwiseAlignmentFormulaReal p (s k)) atTop
        (nhds ((1 : ℝ) / p)) :=
  supportedScaleLimits hp hsupported hs

/-- Exact reciprocal-golden limiting classification. -/
theorem golden_gap {p : ℕ} (hp : Nat.Prime p) :
    ((1 : ℝ) / p < goldenReciprocal ∧
      goldenReciprocal < (2 : ℝ) / p) ↔ p = 2 ∨ p = 3 :=
  reciprocalGolden_between_limits_iff hp

/-- Prime two gives reference alignment one at every admissible scale. -/
theorem prime_two_degeneracy {s : ℕ} (hs : 1 ≤ s) :
    alignmentFormula 2 s = 1 :=
  primeTwo_reference_degenerate hs

/-- Among odd primes, the reciprocal-golden limiting gap occurs exactly at
the prime three. -/
theorem odd_prime_golden_gap_iff_three {p : ℕ} (hp : Nat.Prime p)
    (hodd : Odd p) :
    ((1 : ℝ) / p < goldenReciprocal ∧
      goldenReciprocal < (2 : ℝ) / p) ↔ p = 3 := by
  rw [golden_gap hp]
  constructor
  · rintro (rfl | rfl)
    · norm_num at hodd
    · rfl
  · exact fun h => Or.inr h

/-- The displayed finite deficit identity is exact and strictly positive. -/
theorem finite_reference_deficit {p s : ℕ} (hp : 3 ≤ p) (hs : 1 ≤ s) :
    (2 : ℝ) / p - alignmentFormulaReal p s =
        (p - 2 : ℝ) / (p * ((p : ℝ) * s - 1)) ∧
      0 < (2 : ℝ) / p - alignmentFormulaReal p s :=
  referenceLimit_sub_finite hp hs

/-- At every finite resolution for a prime core at least five, both finite
statistics lie below the reciprocal-golden threshold. -/
theorem large_prime_finite_threshold_bounds
    {p s : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    0 ≤ focusedAlignmentFormulaReal p s ∧
      focusedAlignmentFormulaReal p s ≤ alignmentFormulaReal p s ∧
      alignmentFormulaReal p s < (2 : ℝ) / p ∧
      (2 : ℝ) / p ≤ (2 : ℝ) / 5 ∧
      (2 : ℝ) / 5 < goldenReciprocal :=
  largePrimeFiniteThresholdCertificate hp hp5 hs

/-- The focused residual alone is below the threshold in every admissible
prime-core case, including prime two. -/
theorem focused_finite_below_threshold
    {b p s : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hsupported : Supported b s) (hps : 3 ≤ p * s) :
    focusedAlignmentFormulaReal p s < goldenReciprocal :=
  focusedAlwaysBelowGolden hp hpb hsupported hps

/-- On the actual positive full-period digit statistic, pairwise alignment is
zero exactly when the prime digit function is injective. -/
theorem zero_pairwise_alignment {b p : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hpb : ¬p ∣ b) :
    primePairwiseAlignment b p (primeBasePeriod b p hp hpb) = 0 ↔
      DigitPartitioning b p :=
  primePairwiseAlignment_eq_zero_iff_digitPartitioning
    hp hp3 hpb (primeBasePeriod_pos hp hpb)

/-- Equivalently, no two distinct nonzero prime residues share a digit at the
same synchronized position. -/
theorem synchronized_position_separation {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    PositionSeparated b p ↔ DigitPartitioning b p :=
  positionSeparated_iff_digitPartitioning hp hpb

/-- For composite rough parts the focused statistic is only the signed
residual identity; no positivity conclusion is asserted. -/
theorem composite_signed_residual_identity (reference pairwise : ℚ) :
    reference = (reference - pairwise) + pairwise :=
  signedResidual_identity reference pairwise

/-- The manuscript's all-terminating convention gives reference and pairwise
alignment one and focused residual zero. -/
theorem entirely_supported_field_statistics {b n : ℕ} (hn : 3 ≤ n)
    (hsupported : Supported b n) :
    allTerminatingReferenceMean n = 1 ∧
      allTerminatingPairwiseMean n = 1 ∧
      allTerminatingReferenceMean n - allTerminatingPairwiseMean n = 0 :=
  fullyTerminatingStatistics hn hsupported

/-- The limiting gap has width exactly `1/p`. -/
theorem limiting_gap_width {p : ℕ} (hp : 0 < p) :
    (2 : ℝ) / p - (1 : ℝ) / p = (1 : ℝ) / p :=
  limitingGapWidth hp

/-- The pairwise term changes the threshold side exactly when the prime core
lies below twice the golden ratio. -/
theorem pairwise_term_changes_threshold_iff {p : ℕ} (hp : 0 < p) :
    (1 : ℝ) / p > goldenReciprocal - (1 : ℝ) / p ↔
      (p : ℝ) < 2 * goldenRatio :=
  gapContributionChangesThreshold_iff hp

end NField.Papers.CoherenceDecomposition
