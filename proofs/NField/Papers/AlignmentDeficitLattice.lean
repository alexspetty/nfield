/-
Author: Alexander S. Petty
-/

import NField.Alignment.DeficitLattice
import NField.Alignment.SupportedPrimeExponentCone
import NField.Alignment.EventuallyPeriodicDigitBlocks

/-!
# The Alignment Deficit Lattice and Musical Tuning

Thin manuscript-facing correspondence map for the canonical JMM round-two
source.  Reusable mathematics lives in modules named after the alignment
deficit, supported prime-exponent cone, and eventually periodic digit-block
objects.
-/

namespace NField.Papers.AlignmentDeficitLattice

open Filter NField.Alignment
open NField.Alignment.DeficitLattice
open NField.Alignment.SupportedPrimeExponentCone
open NField.Alignment.EventuallyPeriodicDigitBlocks

/-- The manuscript's two equivalent definitions of a supported positive
integer. -/
theorem supported_integer_characterization {b m : ℕ} (hb : 0 < b)
    (hm : 0 < m) :
    Supported b m ↔ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ b :=
  supported_iff_prime_divisors hb hm

/-- Positive supported integers are precisely their nonnegative exponent
vectors on the prime divisors of the base, and multiplication is addition of
coordinates. -/
theorem supported_prime_exponent_coordinate {b m n : ℕ} (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) (hsm : Supported b m)
    (hsn : Supported b n) :
    (supportedPrimeExponentEquiv b hb
        ⟨m * n, Nat.mul_pos hm hn, NField.Alignment.supported_mul hsm hsn⟩).1 =
      (supportedPrimeExponentEquiv b hb ⟨m, hm, hsm⟩).1 +
        (supportedPrimeExponentEquiv b hb ⟨n, hn, hsn⟩).1 ∧
      ∀ x y : SupportedPositive b,
        (supportedPrimeExponentEquiv b hb x).1 =
            (supportedPrimeExponentEquiv b hb y).1 → x = y := by
  exact ⟨supportedPrimeExponentEquiv_mul hb hm hn hsm hsn,
    fun x y h => (supportedPrimeExponentEquiv b hb).injective
      (Subtype.ext h)⟩

/-- Integer exponents form the concrete group completion of the supported
cone, and bases twelve and thirty have exactly the two stated generator sets. -/
theorem supported_prime_exponent_group_completion :
    (∀ q : ℕ, q.Prime → (q ∣ 12 ↔ q = 2 ∨ q = 3)) ∧
      (∀ q : ℕ, q.Prime → (q ∣ 30 ↔ q = 2 ∨ q = 3 ∨ q = 5)) ∧
      (∀ b : ℕ, ∀ z : PrimeExponentGroup b,
        ∃ x y : PrimeExponentCone b,
          exponentNatCast x.1 - exponentNatCast y.1 = z.1) ∧
      ∀ m n : ℕ, 0 < m → 0 < n →
        ((naturalExponentValue m.factorization : ℕ) : ℚ) /
            (naturalExponentValue n.factorization : ℕ) =
          (m : ℚ) / n :=
  ⟨baseTwelve_and_baseThirty_prime_supports.1,
    baseTwelve_and_baseThirty_prime_supports.2,
    primeExponentGroup_eq_difference,
    fun _ _ hm hn => prime_exponent_ratio_reconstruction hm hn⟩

/-- A period-`L` tail realizes at most `L` different blocks of every fixed
length, exactly the finite block-count obstruction used in the manuscript. -/
theorem periodic_tail_block_bound {b μ L k : ℕ} {d : ℕ → Fin b}
    (hL : 0 < L) (hperiod : ∀ s : ℕ, d (μ + s + L) = d (μ + s)) :
    ∃ phaseBlock : Fin L → (Fin k → Fin b),
      (∀ t : ℕ, digitBlock d (μ + t) k =
        phaseBlock ⟨t % L, Nat.mod_lt _ hL⟩) ∧
      Fintype.card (Set.range phaseBlock) ≤ L :=
  periodic_tail_blocks_at_most_period hL hperiod

/-- The long-division residue orbit is eventually periodic, and once `b^k`
exceeds the denominator the rational tail omits a length-`k` word. -/
theorem rational_expansion_periodic_not_normal {b n a k : ℕ}
    (hb : 0 < b) (hn : 0 < n) (hcard : n < b ^ k) :
    ∃ μ L : ℕ, 0 < L ∧ μ + L ≤ n ∧
      ∃ word : Fin k → Fin b,
        ∀ t : ℕ,
          digitBlock (rationalDigitFin b n a hb hn) (μ + t) k ≠ word :=
  rational_digit_tail_omits_block hb hn hcard

/-- Every rational expansion in a genuine base has an eventually absent
finite word, without requiring a block length as an input. -/
theorem rational_expansion_omits_some_block {b n a : ℕ}
    (hb : 2 ≤ b) (hn : 0 < n) :
    ∃ k μ L : ℕ, 0 < L ∧ μ + L ≤ n ∧
      ∃ word : Fin k → Fin b,
        ∀ t : ℕ,
          digitBlock (rationalDigitFin b n a (by omega) hn) (μ + t) k ≠ word :=
  rational_digit_tail_omits_some_block hb hn

/-- Under the complete JMM hypotheses, synchronized long division gives the
two exact aligned residue classes and the alignment formula. -/
theorem repetend_alignment_formula {b p m : ℕ}
    (hp : Nat.Prime p) (hb : 2 ≤ b)
    (hmod : b % p = 1) (hm : 1 ≤ m) (hsupported : Supported b m) :
    ∃ D : ℕ,
      m ∣ b ^ D ∧
      (∀ k : ℕ, TerminatesInBase b k (p * m) ↔ p ∣ k) ∧
      (∀ k : ℕ,
        synchronizedAligned b p (clearingCofactor b m D) k ↔
          k % p = 0 ∨
            ∀ j : ℕ,
              digitAt b p ((k * clearingCofactor b m D) % p) j =
                digitAt b p (clearingCofactor b m D % p) j) ∧
      terminatingNumeratorCount p m = m - 1 ∧
      matchingNumeratorCount p m = m ∧
      alignedNumeratorCount p m = 2 * m - 1 ∧
      oneDigitAlignment p m = alignmentFormula p m := by
  have hpb : ¬p ∣ b := by
    intro hdiv
    have hz : b % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  rcases generalPrimeAlignment_certificate hp hb hpb hmod hsupported with
    ⟨D, hD, _hclasses, _halignment⟩
  have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hpb
  have hcofactor : Nat.Coprime p (clearingCofactor b m D) :=
    prime_coprime_clearingCofactor hp hpb hD
  exact ⟨D, hD,
    fun k => terminatesInBase_mul_supported_iff hsupported hcop,
    fun k => synchronizedAligned_iff_terminates_or_all_digits
      hp hb hmod hcofactor,
    terminatingNumeratorCount_eq hp.pos,
    matchingNumeratorCount_eq hp.one_lt,
    alignedNumeratorCount_eq hp.one_lt,
    oneDigitAlignment_eq_alignmentFormula hp hm⟩

/-- Choosing any other valid supported clearing depth leaves the synchronized
alignment classification unchanged. -/
theorem repetend_alignment_independent_of_clearing_depth
    {b p m D E k : ℕ} (hp : Nat.Prime p) (hb : 2 ≤ b)
    (hmod : b % p = 1) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    synchronizedAligned b p (clearingCofactor b m D) k ↔
      synchronizedAligned b p (clearingCofactor b m E) k := by
  have hpb : ¬p ∣ b := by
    intro hdiv
    have hz : b % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  exact synchronizedAligned_independent_of_clearing_depth
    hp hb hpb hmod hD hE

/-- The numerical base-twelve denominator-twenty-two example is exact. -/
theorem base_twelve_denominator_twenty_two_example :
    terminatingNumeratorCount 11 2 = 1 ∧
      matchingNumeratorCount 11 2 = 2 ∧
      alignedNumeratorCount 11 2 = 3 ∧
      oneDigitAlignment 11 2 = (3 : ℚ) / 21 :=
  baseTwelve_twentyTwo_example

/-- The alignment deficit has the manuscript's closed form and is positive. -/
theorem exact_alignment_deficit {p m : ℕ} (hp : 3 ≤ p) (hm : 1 ≤ m) :
    alignmentDeficit p m =
        ((p : ℚ) - 2) / ((p : ℚ) * ((p : ℚ) * m - 1)) ∧
      0 < alignmentDeficit p m :=
  ⟨alignmentDeficit_eq hp hm, alignmentDeficit_pos hp hm⟩

/-- The deficit is strictly order reversing and therefore injective on the
positive supported monoid. -/
theorem deficit_order_reversing_and_injective {p m n : ℕ}
    (hp : 3 ≤ p) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (m < n → alignmentDeficit p n < alignmentDeficit p m) ∧
      (alignmentDeficit p m = alignmentDeficit p n → m = n) :=
  ⟨alignmentDeficit_lt_of_lt hp hm,
    alignmentDeficit_injective_on_positive hp hm hn⟩

/-- The exact two-point deficit-ratio formula. -/
theorem exact_deficit_ratio {p m₁ m₂ : ℕ} (hp : 3 ≤ p)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    alignmentDeficit p m₁ / alignmentDeficit p m₂ =
      ((p : ℚ) * m₂ - 1) / ((p : ℚ) * m₁ - 1) :=
  alignmentDeficit_ratio_eq hp hm₁ hm₂

/-- The scaled ratio, its exact relative error, and its limiting interval all
hold for every positive scale, a stronger domain than only supported scales. -/
theorem scaled_deficit_ratio_and_limit {p u v : ℕ} (hp : 3 ≤ p)
    (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (∀ t : ℕ, 1 ≤ t →
      scaledDeficitRatio p u v t =
          ((p : ℚ) * t * v - 1) / ((p : ℚ) * t * u - 1) ∧
        scaledRelativeError p u v t =
          ((v : ℚ) - u) / ((v : ℚ) * ((p : ℚ) * t * u - 1))) ∧
      Tendsto (scaledDeficitRatioReal p u v) atTop
        (nhds ((v : ℝ) / u)) :=
  scaledFamily_certificate hp hu hv

/-- The exact relative-error profile is strictly increasing with the interval
endpoint above the fixed reference point. -/
theorem finite_relative_error_strictly_increasing {p u v w t : ℕ}
    (hp : 3 ≤ p) (hu : 1 ≤ u) (ht : 1 ≤ t)
    (huv : u ≤ v) (hvw : v < w) :
    scaledRelativeError p u v t < scaledRelativeError p u w t :=
  scaledRelativeError_lt_of_lt hp hu ht huv hvw

/-- Multiplication by one generator has the exact finite correction and tends
to the generator itself. -/
theorem generator_scaling {p q : ℕ} (hp : 3 ≤ p) (hq : 1 ≤ q) :
    (∀ m : ℕ, 1 ≤ m →
      alignmentDeficit p m / alignmentDeficit p (q * m) =
        (q : ℚ) + ((q : ℚ) - 1) / ((p : ℚ) * m - 1)) ∧
      Tendsto (scaledDeficitRatioReal p 1 q) atTop (nhds (q : ℝ)) := by
  exact ⟨fun m hm => generatorScaling_eq hp hq hm,
    generatorScaling_tendsto (by omega)⟩

/-- The Pythagorean-comma inputs are supported, have the stated exact finite
value, and tend to the stated rational interval. -/
theorem pythagorean_comma_certificate :
    Supported 12 (2 ^ 19) ∧ Supported 12 (3 ^ 12) ∧
      scaledDeficitRatio 11 (2 ^ 19) (3 ^ 12) 1 =
        (5845850 : ℚ) / 5767167 ∧
      Tendsto (scaledDeficitRatioReal 11 (2 ^ 19) (3 ^ 12)) atTop
        (nhds (((3 ^ 12 : ℕ) : ℝ) / (2 ^ 19 : ℕ))) ∧
      ((2027285 : ℚ) / 2000000 < (5845850 : ℚ) / 5767167 ∧
        (5845850 : ℚ) / 5767167 < (2027287 : ℚ) / 2000000 ∧
        (2027285 : ℚ) / 2000000 < (3 ^ 12 : ℚ) / (2 ^ 19) ∧
        (3 ^ 12 : ℚ) / (2 ^ 19) < (2027287 : ℚ) / 2000000 ∧
        |((5845850 : ℚ) / 5767167) / ((3 ^ 12 : ℚ) / (2 ^ 19)) - 1| <
          (1 : ℚ) / 1000) :=
  ⟨pythagorean_inputs_supported.1, pythagorean_inputs_supported.2,
    pythagoreanComma_finite, pythagoreanComma_tendsto,
    pythagoreanComma_decimal_window⟩

/-- Bases six, twelve, and twenty-four have the same Pythagorean supported
domain, while base ten has the stated missing-three boundary. -/
theorem base_support_examples {m : ℕ} :
    (Supported 6 m ↔ Supported 12 m) ∧
      (Supported 12 m ↔ Supported 24 m) ∧
      Supported 10 2 ∧ Supported 10 5 ∧ Supported 10 4 ∧
      ¬Supported 10 3 := by
  exact ⟨bases_six_twelve_twentyfour_same_support.1,
    bases_six_twelve_twentyfour_same_support.2,
    base_ten_support_boundary.1,
    base_ten_support_boundary.2.1,
    base_ten_support_boundary.2.2.1,
    base_ten_support_boundary.2.2.2⟩

/-- The eight common-denominator scale points are supported and have exactly
the displayed just-major ratios. -/
theorem just_major_scale_lattice :
    (Supported 30 24 ∧ Supported 30 27 ∧ Supported 30 30 ∧
      Supported 30 32 ∧ Supported 30 36 ∧ Supported 30 40 ∧
      Supported 30 45 ∧ Supported 30 48) ∧
      ((24 : ℚ) / 24 = 1 ∧
      (27 : ℚ) / 24 = 9 / 8 ∧
      (30 : ℚ) / 24 = 5 / 4 ∧
      (32 : ℚ) / 24 = 4 / 3 ∧
      (36 : ℚ) / 24 = 3 / 2 ∧
      (40 : ℚ) / 24 = 5 / 3 ∧
      (45 : ℚ) / 24 = 15 / 8 ∧
      (48 : ℚ) / 24 = 2) :=
  ⟨majorScale_supported, majorScale_exact_ratios⟩

/-- The just-major finite relative errors attain the exact endpoint value and
all satisfy the manuscript's strict bound. -/
theorem just_major_scale_finite_errors :
    |scaledRelativeError 29 24 24 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 27 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 30 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 32 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 36 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 40 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 45 1| < (9 : ℚ) / 12500 ∧
    scaledRelativeError 29 24 48 1 = (1 : ℚ) / 1390 ∧
    |scaledRelativeError 29 24 48 1| < (9 : ℚ) / 12500 :=
  majorScale_relative_errors

/-- Every one of the eight scale points is the exact limiting deficit ratio. -/
theorem just_major_scale_limits (m : ℕ) :
    Tendsto (scaledDeficitRatioReal 29 24 m) atTop
      (nhds ((m : ℝ) / 24)) :=
  majorScale_tendsto m

/-- Twenty-four is forced as the least common denominator by the displayed
denominators eight, four, and three. -/
theorem just_major_scale_least_common_denominator {d : ℕ} (hd : 0 < d)
    (h8 : 8 ∣ d) (h4 : 4 ∣ d) (h3 : 3 ∣ d) :
    0 < d ∧ 4 ∣ d ∧ 24 ∣ d :=
  majorScale_common_denominator_least hd h8 h4 h3

/-- The seven successive diatonic step ratios are exactly the displayed
whole-tone and semitone pattern. -/
theorem diatonic_step_pattern :
    (27 : ℚ) / 24 = 9 / 8 ∧
    (30 : ℚ) / 27 = 10 / 9 ∧
    (32 : ℚ) / 30 = 16 / 15 ∧
    (36 : ℚ) / 32 = 9 / 8 ∧
    (40 : ℚ) / 36 = 10 / 9 ∧
    (45 : ℚ) / 40 = 9 / 8 ∧
    (48 : ℚ) / 45 = 16 / 15 :=
  majorScale_step_ratios

/-- The diatonic list is not the whole five-limit octave: twenty-five is an
additional supported point with ratio `25/24`. -/
theorem additional_five_limit_octave_point :
    Supported 30 25 ∧ (25 : ℚ) / 24 = 25 / 24 ∧
      25 ∉ ({24, 27, 30, 32, 36, 40, 45, 48} : Finset ℕ) :=
  justChromaticSemitone_fixture

/-- Every base divisible by thirty contains the displayed five-limit
submonoid. -/
theorem five_limit_submonoid_in_larger_support {b m : ℕ}
    (hb : 30 ∣ b) (hm : Supported 30 m) : Supported b m :=
  five_limit_submonoid_of_thirty_dvd hb hm

/-- The finite coordinate and its error genuinely depend on which eligible
alignment prime is chosen, even with the base held fixed. -/
theorem alignment_prime_changes_finite_values :
    66 % 5 = 1 ∧ 66 % 13 = 1 ∧ Nat.Prime 5 ∧ Nat.Prime 13 ∧
      alignmentDeficit 5 2 ≠ alignmentDeficit 13 2 ∧
      scaledRelativeError 5 1 2 1 ≠ scaledRelativeError 13 1 2 1 :=
  alignmentPrime_changes_finite_coordinate

/-- The base-210 hypotheses, exact finite formulas, and both seven-limit
limits hold as stated. -/
theorem seven_limit_extension :
    (Nat.Prime 11 ∧ 210 % 11 = 1 ∧
      Supported 210 4 ∧ Supported 210 7 ∧ Supported 210 8) ∧
      (∀ t : ℕ,
        scaledDeficitRatioReal 11 4 7 t =
            ((77 : ℝ) * t - 1) / (44 * t - 1) ∧
        scaledDeficitRatioReal 11 7 8 t =
            ((88 : ℝ) * t - 1) / (77 * t - 1)) ∧
      Tendsto (scaledDeficitRatioReal 11 4 7) atTop
          (nhds ((7 : ℝ) / 4)) ∧
        Tendsto (scaledDeficitRatioReal 11 7 8) atTop
          (nhds ((8 : ℝ) / 7)) :=
  ⟨sevenLimit_hypotheses, sevenLimit_finite_formulas,
    sevenLimit_tendsto.1, sevenLimit_tendsto.2⟩

/-- The thirteen common-denominator chromatic points are supported and have
exactly the displayed interval ratios. -/
theorem chromatic_scale_lattice :
    (Supported 30 480 ∧ Supported 30 512 ∧ Supported 30 540 ∧
      Supported 30 576 ∧ Supported 30 600 ∧ Supported 30 640 ∧
      Supported 30 675 ∧ Supported 30 720 ∧ Supported 30 768 ∧
      Supported 30 800 ∧ Supported 30 864 ∧ Supported 30 900 ∧
      Supported 30 960) ∧
      ((480 : ℚ) / 480 = 1 ∧
      (512 : ℚ) / 480 = 16 / 15 ∧
      (540 : ℚ) / 480 = 9 / 8 ∧
      (576 : ℚ) / 480 = 6 / 5 ∧
      (600 : ℚ) / 480 = 5 / 4 ∧
      (640 : ℚ) / 480 = 4 / 3 ∧
      (675 : ℚ) / 480 = 45 / 32 ∧
      (720 : ℚ) / 480 = 3 / 2 ∧
      (768 : ℚ) / 480 = 8 / 5 ∧
      (800 : ℚ) / 480 = 5 / 3 ∧
      (864 : ℚ) / 480 = 9 / 5 ∧
      (900 : ℚ) / 480 = 15 / 8 ∧
      (960 : ℚ) / 480 = 2) :=
  ⟨chromaticScale_supported, chromaticScale_exact_ratios⟩

/-- All thirteen chromatic errors satisfy the strict bound and the maximum
endpoint has exactly the quoted value. -/
theorem chromatic_scale_finite_errors :
    (|scaledRelativeError 29 480 480 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 512 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 540 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 576 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 600 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 640 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 675 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 720 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 768 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 800 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 864 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 900 1| < (9 : ℚ) / 250000 ∧
    |scaledRelativeError 29 480 960 1| < (9 : ℚ) / 250000) ∧
      scaledRelativeError 29 480 960 1 = (1 : ℚ) / 27838 :=
  ⟨chromaticScale_relative_errors, chromaticEndpoint_relative_error.1⟩

end NField.Papers.AlignmentDeficitLattice
