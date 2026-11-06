/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.AlignmentLimitClassification
import NField.Alignment.DigitHistogramFourierEnergy
import NField.Alignment.DigitPartitioningClassification

/-!
# The Alignment Limit for All Primes

## Coverage

The all-prime alignment formula includes its collision correction, fixed-coset
subsequential limits and global limits under the stated equidistribution or
primitive-root conditions. The decimal prime-fifty-three examples distinguish
different subsequential limits.

## Scope and assumptions

A global limit uses the stated coset-equidistribution hypothesis or
primitive-root condition. General fixed cosets have subsequential limits,
which need not coincide; the prime-fifty-three examples exhibit that
distinction. The finite bound and sharpness family retain their base and prime
conditions. Exact finite tables and the Fourier-energy identities do not
replace the hypotheses needed for a global limit.
-/

namespace NField.Papers.AlignmentLimit

open NField.Alignment NField.Golden
open NField.Alignment.ThreeTier
open NField.CollisionDefinition

/-- A prime dividing the base stays inside the supported denominator monoid,
so every reciprocal terminates and the rough-one alignment is one. -/
theorem supported_prime_case {b p m : ℕ}
    (_hp : p.Prime) (hpb : p ∣ b) (hm : Supported b m) :
    Supported b (p * m) ∧ (∀ k, TerminatesInBase b k (p * m)) ∧
      ∀ u L, canonicalRoughAlignmentReal b 1 (p * m) u L = 1 := by
  have hpm : Supported b (p * m) :=
    supported_mul (supported_of_dvd_base hpb) hm
  rcases hpm with ⟨D, hD⟩
  refine ⟨⟨D, hD⟩, ?_, fun _ _ =>
    canonicalRoughAlignmentReal_eq_one_of_rough_one⟩
  intro k
  exact ⟨D, dvd_mul_of_dvd_right hD k⟩

/-- The common-clock alignment and selected multiplicative coset do not
depend on which valid clearing depth is chosen. -/
theorem synchronized_alignment_well_defined {b p m D E : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hm : 1 ≤ m)
    (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) =
        clearedAlignmentReal b p m E (primeBasePeriod b p hp hpb) ∧
      ((∃ q, clearingCofactor b m E = b ^ q * clearingCofactor b m D) ∨
        ∃ q, clearingCofactor b m D = b ^ q * clearingCofactor b m E) := by
  exact ⟨clearedAlignmentReal_independent_of_clearing_depth hp hpb hm hD hE,
    clearingCofactors_differ_by_base_power hD hE⟩

/-- Exact floor-bin distribution, enlarged-bin count, and square-sum formula. -/
theorem floor_digit_bin_distribution {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    (∀ d < b, digitBinPopulation b p d = (p - 1) / b ∨
      digitBinPopulation b p d = (p - 1) / b + 1) ∧
      (enlargedDigitBins b p).card = (p - 1) % b ∧
      digitBinSquareSum b p =
        b * ((p - 1) / b) ^ 2 +
          ((p - 1) % b) * (2 * ((p - 1) / b) + 1) := by
  exact ⟨fun d hd => digitBinPopulation_eq_quotient_or_succ hb hp hd,
    enlargedDigitBins_card hb hp,
    digitBinSquareSum_eq_quotient_remainder hb hp⟩

/-- The literal numerator-by-position score is exactly the manuscript's
coset total and normalized finite alignment formula. -/
theorem synchronized_exact_alignment_formula {b p m D : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    let L := primeBasePeriod b p hp hpb
    let T := powerOrbitBinSum (L := L) hp hpb
      (prime_coprime_clearingCofactor hp hpb hD)
    clearedFieldMatchTotal b p m D L = cosetTotalMatchCount m L T ∧
      clearedAlignmentReal b p m D L = cosetAlignmentReal p m L T ∧
      clearedAlignmentReal b p m D L =
        ((m : ℝ) - 1 + (m : ℝ) * T / L) / ((p : ℝ) * m - 1) := by
  dsimp
  exact ⟨clearedFieldMatchTotal_eq_cosetTotalMatchCount hp hpb hm hD,
    clearedAlignmentReal_eq_cosetAlignmentReal hp hpb hm hD
      (primeBasePeriod_pos hp hpb),
    by
      rw [clearedAlignmentReal_eq_cosetAlignmentReal hp hpb hm hD
        (primeBasePeriod_pos hp hpb)]
      rfl⟩

/-- The correction is exact, nonnegative, and vanishes precisely on
singleton digit bins visited by the selected orbit. -/
theorem exact_collision_correction {b p m D : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    let L := primeBasePeriod b p hp hpb
    let hu := prime_coprime_clearingCofactor hp hpb hD
    let T := powerOrbitBinSum (L := L) hp hpb hu
    clearedAlignmentReal b p m D L -
        (((2 * m - 1 : ℕ) : ℝ) / (p * m - 1 : ℕ)) =
          (m : ℝ) * ((T : ℝ) - L) /
            ((L : ℝ) * (p * m - 1 : ℕ)) ∧
      0 ≤ clearedAlignmentReal b p m D L -
        (((2 * m - 1 : ℕ) : ℝ) / (p * m - 1 : ℕ)) ∧
      (clearedAlignmentReal b p m D L =
          (((2 * m - 1 : ℕ) : ℝ) / (p * m - 1 : ℕ)) ↔
        ∀ i : Fin L,
          digitBinPopulation b p
            (digitBin b p ((powerReferenceOrbit hp hpb hu).state i)) = 1) := by
  dsimp
  have hL := primeBasePeriod_pos hp hpb
  have hp2 : 2 ≤ p := hp.two_le
  have hclock := clearedAlignmentReal_eq_cosetAlignmentReal hp hpb hm hD hL
  rw [hclock]
  have hcorr := cosetAlignmentReal_correction
    (p := p) (m := m) (L := primeBasePeriod b p hp hpb)
    (T := powerOrbitBinSum (L := primeBasePeriod b p hp hpb) hp hpb
      (prime_coprime_clearingCofactor hp hpb hD)) hp2 hm hL
  have hTL : primeBasePeriod b p hp hpb ≤
      powerOrbitBinSum (L := primeBasePeriod b p hp hpb) hp hpb
        (prime_coprime_clearingCofactor hp hpb hD) :=
    orbitBinSum_ge_length (b := b) (p := p)
      (L := primeBasePeriod b p hp hpb)
      (powerReferenceOrbit hp hpb
        (prime_coprime_clearingCofactor hp hpb hD))
  refine ⟨hcorr, ?_, ?_⟩
  · rw [hcorr]
    have hcast : ((primeBasePeriod b p hp hpb : ℕ) : ℝ) ≤
        powerOrbitBinSum (L := primeBasePeriod b p hp hpb) hp hpb
          (prime_coprime_clearingCofactor hp hpb hD) := by
      exact_mod_cast hTL
    have hden : (0 : ℝ) < (p * m - 1 : ℕ) := by
      have : 2 ≤ p * m := Nat.mul_le_mul hp2 hm
      exact_mod_cast (show 0 < p * m - 1 by omega)
    positivity
  · rw [cosetAlignmentReal_eq_baseline_iff hp2 hm hL]
    simpa only [powerOrbitBinSum] using
      (orbitBinSum_eq_length_iff (b := b) (p := p)
        (L := primeBasePeriod b p hp hpb)
        (powerReferenceOrbit hp hpb
          (prime_coprime_clearingCofactor hp hpb hD)))

/-- A fixed selected coset gives the displayed subsequential limit along any
multiplicity sequence tending to infinity. -/
theorem fixed_coset_subsequential_limit
    {ι : Type*} {l : Filter ι} {p L T : ℕ} {m : ι → ℕ}
    (hp : 0 < p) (hL : 0 < L) (hm : Filter.Tendsto m l Filter.atTop) :
    Filter.Tendsto (fun i => cosetAlignmentReal p (m i) L T) l
      (nhds (((L + T : ℕ) : ℝ) / ((p * L : ℕ) : ℝ))) :=
  cosetAlignmentReal_tendsto_along hp hL hm

/-- Equal normalized bin sums on every selected coset force one global limit
along every supported multiplicity sequence. -/
theorem equidistributed_coset_global_limit
    {ι : Type*} {l : Filter ι} {p L S : ℕ} {m T : ι → ℕ}
    (hp : 1 < p) (hL : 0 < L) (_hsupported : ∀ i, Supported 10 (m i))
    (hm : Filter.Tendsto m l Filter.atTop)
    (hequidist : ∀ i, (T i : ℝ) / L = (S : ℝ) / (p - 1 : ℕ)) :
    Filter.Tendsto (fun i => cosetAlignmentReal p (m i) L (T i)) l
      (nhds ((((p - 1 : ℕ) : ℝ) + S) /
        ((p : ℝ) * (p - 1 : ℕ)))) :=
  equidistributed_cosetAlignmentReal_tendsto_along hp hL hm hequidist

/-- Full multiplicative order makes the equidistribution identity automatic,
independently of the selected starting multiplier. -/
theorem primitive_root_global_limit
    {ι : Type*} {l : Filter ι} {b p : ℕ} {m u : ι → ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1)
    (hm : Filter.Tendsto m l Filter.atTop)
    (hu : ∀ i, Nat.Coprime p (u i)) :
    Filter.Tendsto
      (fun i => cosetAlignmentReal p (m i) (primeBasePeriod b p hp hpb)
        (powerOrbitBinSum (L := primeBasePeriod b p hp hpb)
          hp hpb (hu i))) l
      (nhds ((((p - 1 : ℕ) : ℝ) + digitBinSquareSum b p) /
        ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
  apply equidistributed_cosetAlignmentReal_tendsto_along
    (S := digitBinSquareSum b p)
    (T := fun i => powerOrbitBinSum
      (L := primeBasePeriod b p hp hpb) hp hpb (hu i))
    hp.one_lt (primeBasePeriod_pos hp hpb) hm
  intro i
  rw [powerOrbitBinSum_eq_digitBinSquareSum_of_full_order hp hpb (hu i) hfull,
    hfull]

/-- Prime fifty-three has four genuinely different decimal cosets, two bin
sums, two exact limit values, and explicit infinite subsequences realizing
both sums. -/
theorem decimal_prime_fifty_three_nonunique_limits :
    Nat.card ((ZMod 53)ˣ ⧸ primeBaseOrbitSubgroup 10 53
      (by norm_num) (by norm_num)) = 4 ∧
      Function.Injective (fun a : Fin 4 =>
        (decimalPrimeFiftyThreeSelectedUnit a.val :
          (ZMod 53)ˣ ⧸ primeBaseOrbitSubgroup 10 53
            (by norm_num) (by norm_num))) ∧
      (∀ a, (decimalPrimeFiftyThreeSelectedUnit a :
          (ZMod 53)ˣ ⧸ primeBaseOrbitSubgroup 10 53
            (by norm_num) (by norm_num)) =
        decimalPrimeFiftyThreeSelectedUnit (a + 4)) ∧
      ((((13 + 67 : ℕ) : ℚ) / (53 * 13 : ℕ)) = 80 / 689) ∧
      ((((13 + 69 : ℕ) : ℚ) / (53 * 13 : ℕ)) = 82 / 689) ∧
      (∀ k, computablePowerOrbitBinSum 10 53 (5 ^ (4 * k)) 13 = 67 ∧
        computablePowerOrbitBinSum 10 53 (5 ^ (4 * k + 1)) 13 = 69) := by
  exact ⟨decimalPrimeFiftyThree_orbitFamilyCount,
    decimalPrimeFiftyThree_firstFourCosets_injective,
    decimalPrimeFiftyThree_selectedCoset_period_four,
    decimalPrimeFiftyThree_subsequentialLimits.1,
    decimalPrimeFiftyThree_subsequentialLimits.2,
    decimalPrimeFiftyThree_powerOrbitBinSum_subsequences⟩

/-- The named prime-fifty-three representatives have the manuscript's exact
bin sums, and the actual supported family selects `u=5^a`. -/
theorem decimal_prime_fifty_three_named_cosets :
    computablePowerOrbitBinSum 10 53 1 13 = 67 ∧
      computablePowerOrbitBinSum 10 53 25 13 = 67 ∧
      computablePowerOrbitBinSum 10 53 2 13 = 69 ∧
      computablePowerOrbitBinSum 10 53 5 13 = 69 ∧
      (∀ a, clearingCofactor 10 (2 ^ a) a = 5 ^ a) := by
  exact ⟨decimalPrimeFiftyThree_namedCosetBinSums.1,
    decimalPrimeFiftyThree_namedCosetBinSums.2.1,
    decimalPrimeFiftyThree_namedCosetBinSums.2.2.1,
    decimalPrimeFiftyThree_namedCosetBinSums.2.2.2,
    decimalTwoPower_clearingCofactor⟩

/-- The digit-partitioning regime recovers the earlier exact finite formula,
minimal square sum, and limit `2/p`. -/
theorem digit_partitioning_recovery
    {ι : Type*} {l : Filter ι} {b p m D : ℕ} {ms : ι → ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D)
    (hms : Filter.Tendsto ms l Filter.atTop)
    (hmsSupported : ∀ i, Supported b (ms i)) :
    clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) =
        digitPartitioningAlignmentFormulaReal p m ∧
      digitBinSquareSum b p = p - 1 ∧
      Filter.Tendsto
        (fun i => digitPartitioningAlignmentFormulaReal p (ms i)) l
        (nhds ((2 : ℝ) / p)) := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero fun hb0 => hpb (by simp [hb0])
  exact ⟨clearedDigitPartitioningAlignmentReal_eq hp hpb hdp hm hD
      (primeBasePeriod_pos hp hpb),
    digitBinSquareSum_eq_of_digitPartitioning hbpos hp.pos hdp,
    digitPartitioningAlignment_tendsto_along_supported hp.pos
      hmsSupported hms⟩

/-- Prime two has alignment one in both the terminating even-base branch and
the nonterminating odd-base branch. -/
theorem prime_two_degenerate {b : ℕ} (hb : 2 ≤ b) :
    (Even b → ∀ m, Supported b m →
      Supported b (2 * m) ∧
        ∀ u L, canonicalRoughAlignmentReal b 1 (2 * m) u L = 1) ∧
      (Odd b → ¬2 ∣ b ∧ DigitPartitioning b 2 ∧
        ∀ m, 1 ≤ m → digitPartitioningAlignmentFormulaReal 2 m = 1) := by
  constructor
  · rintro ⟨k, hk⟩ m hm
    have htwo : Supported b 2 := supported_of_dvd_base
      ⟨k, by simpa [two_mul] using hk⟩
    exact ⟨supported_mul htwo hm,
      fun _ _ => canonicalRoughAlignmentReal_eq_one_of_rough_one⟩
  · exact fun hodd => prime_two_odd_base_degenerate hb hodd

/-- The one-position case `b = 1 mod p` is exactly the earlier
digit-partitioning formula. -/
theorem one_digit_orbit_specialization {b p m D : ℕ}
    (hp : p.Prime) (hb : 2 ≤ b) (hpb : ¬p ∣ b) (hmod : b % p = 1)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    primeBasePeriod b p hp hpb = 1 ∧
      clearedAlignmentReal b p m D 1 =
        digitPartitioningAlignmentFormulaReal p m := by
  have hperiod : primeBasePeriod b p hp hpb = 1 := by
    apply primeBasePeriod_eq_of_isLeastPositiveModularPeriod hp hpb
    exact ⟨by norm_num,
      by simpa [Nat.mod_eq_of_lt hp.one_lt] using hmod,
      by omega⟩
  exact ⟨hperiod, by
    rw [clearedOneDigitAlignmentReal_eq hp hb hpb hmod hm hD]
    rfl⟩

/-- Every field of every displayed base-ten row is exact, including period,
square sum, coset sum, reduced value, rounding, and equidistribution flag. -/
theorem decimal_table_certificate :
    ∀ row ∈ decimalAlignmentLimitRows, row.Valid :=
  decimalAlignmentLimitRows_valid

/-- Every finite admissible prime alignment is strictly below three-fifths
and hence strictly below the reciprocal golden ratio. -/
theorem sharp_uniform_finite_bound {b p m D : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) <
        (3 : ℝ) / 5 ∧
      (3 : ℝ) / 5 < goldenReciprocal := by
  exact ⟨clearedAlignmentReal_lt_three_fifths hp hp5 hpb hb hm hD
      (primeBasePeriod_pos hp hpb),
    NField.Alignment.three_fifths_lt_goldenReciprocal⟩

/-- Every fixed-coset limiting value is at most three-fifths. -/
theorem subsequential_limit_bound {b p u : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hu : Nat.Coprime p u) :
    (((primeBasePeriod b p hp hpb +
        powerOrbitBinSum (L := primeBasePeriod b p hp hpb) hp hpb hu : ℕ) : ℝ) /
      ((p * primeBasePeriod b p hp hpb : ℕ) : ℝ)) ≤ (3 : ℝ) / 5 :=
  powerOrbitLimitReal_le_three_fifths hp hp5 hpb hb hu
    (primeBasePeriod_pos hp hpb)

/-- The base-two, prime-five family approaches three-fifths from below, so
the uniform constant is sharp. -/
theorem sharpness_family :
    (∀ a, clearedAlignmentReal 2 5 (2 ^ a) a 4 =
      ((3 : ℝ) * ((2 ^ a : ℕ) : ℝ) - 1) /
        ((5 : ℝ) * ((2 ^ a : ℕ) : ℝ) - 1)) ∧
      Filter.Tendsto (fun a => clearedAlignmentReal 2 5 (2 ^ a) a 4)
        Filter.atTop (nhds ((3 : ℝ) / 5)) :=
  ⟨baseTwoPrimeFive_clearedAlignmentReal,
    baseTwoPrimeFive_clearedAlignmentReal_tendsto⟩

/-- Among non-base-dividing primes at least three, crossing the reciprocal
golden threshold forces the prime to be three. -/
theorem reciprocal_golden_prime_restriction {b p m D : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D)
    (hgold : goldenReciprocal <
      clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb)) :
    p = 3 := by
  by_contra hpne
  have hp5 : 5 ≤ p := by
    rcases hp.odd_of_ne_two (by omega) with ⟨k, hk⟩
    omega
  have hbelow := (sharp_uniform_finite_bound hp hp5 hpb hb hm hD).1
  have hthreshold := NField.Alignment.three_fifths_lt_goldenReciprocal
  linarith

/-- The below-one-hundred decimal scan is exhaustive, and its only failures
of coset-bin-sum equidistribution are 53, 73, 79, and 89. -/
theorem decimal_equidistribution_exceptions_below_one_hundred :
    (List.range 100).filter (fun p => decide (Nat.Prime p ∧ ¬p ∣ 10)) =
        decimalPrimePeriodsBelowOneHundred.map Prod.fst ∧
      (decimalPrimePeriodsBelowOneHundred.filter fun pair =>
        !allOrbitBinSumsEquidistributed pair.1 pair.2
          (computableDigitBinSquareSum 10 pair.1)).map Prod.fst =
        [53, 73, 79, 89] :=
  ⟨decimalPrimePeriodsBelowOneHundred_complete,
    decimalEquidistributionExceptionsBelowOneHundred⟩

/-- The square bin sum is exactly the ordered same-digit collision count. -/
theorem ordered_collision_interpretation {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) :
    digitBinSquareSum b p =
      ∑ r ∈ nonzeroResidues p,
        digitBinPopulation b p (digitBin b p r) :=
  digitBinSquareSum_eq_sum_population_at_residue hb hp

/-- Exact finite Fourier-energy identity for the digit histogram. -/
theorem digit_histogram_fourier_energy {b p : ℕ} [NeZero b] (hb : 0 < b) :
    ((digitBinSquareSum b p : ℕ) : ℂ) =
      (1 / (b : ℂ)) * ∑ j : ZMod b,
        star (digitHistogramFourier b p j) * digitHistogramFourier b p j :=
  digitBinSquareSum_eq_normalized_fourier_energy hb

/-- Fourier energy is minimal exactly when every occupied digit bin is a
singleton, equivalently exactly for digit partitioning. -/
theorem minimum_energy_singleton_characterization {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) :
    digitBinSquareSum b p = p - 1 ↔ DigitPartitioning b p :=
  digitBinSquareSum_minimal_iff_digitPartitioning hb hp

end NField.Papers.AlignmentLimit
