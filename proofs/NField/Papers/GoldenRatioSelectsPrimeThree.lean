/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OneDigitAlignmentLimit
import NField.Alignment.SynchronizedOneDigitAlignment
import NField.Alignment.SynchronizedPeriodAlignment
import NField.Golden.SelfReferentialThreshold

/-!
# Why the Golden Ratio Selects the Prime Three

## Coverage

The alignment formulas, golden threshold and prime-three selection are
formalized, together with the supported-denominator classification,
complementary-digit pairing and exact decimal examples.

## Scope and assumptions

The alignment statements retain their base, primality, divisibility and
clearing-depth hypotheses. The general prime threshold and separating-window
results concern their stated admissible domains; the prime-two obstruction is
a separate case. The displayed decimal alignment table is a finite exact
evaluation.
-/

namespace NField.Papers.GoldenRatioSelectsPrimeThree

open Filter Polynomial
open NField.Alignment NField.CollisionDefinition NField.Golden
open NField.Alignment.ThreeTier

/-- Manuscript definition of supported positive denominators, including the
prime-factor equivalence. -/
theorem supported_denominator_characterization
    {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Supported b m ↔ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ b :=
  supported_iff_every_prime_divisor_divides_base (by omega) (by omega)

/-- The manuscript's equivalence between support and termination of `1/m`. -/
theorem supported_termination_characterization {b m : ℕ} :
    Supported b m ↔ TerminatesInBase b 1 m :=
  supported_iff_one_terminates_at_some_depth

/-- The complete decimal specialization `m = 2^a 5^c`. -/
theorem decimal_supported_denominator_classification
    {m : ℕ} (hm : 1 ≤ m) :
    Supported 10 m ↔ ∃ a c : ℕ, m = 2 ^ a * 5 ^ c :=
  base_ten_supported_iff_two_pow_mul_five_pow (by omega)

/-- Arithmetic meaning of the terminating branch at a common clearing depth. -/
theorem synchronized_termination_characterization
    {b p m D k : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (hsupported : Supported b m) (hm : m ∣ b ^ D) :
    (TerminatesInBase b k (p * m) ↔ k % p = 0) ∧
      (TerminatesAtDepth b k (p * m) D ↔ k % p = 0) :=
  ⟨terminatesInBase_iff_residue_zero hp hpb hsupported,
    terminatesAtDepth_iff_residue_zero hp hpb hm⟩

/-- The synchronized average over the complete multiplicative period is
independent of the valid common clearing depth, before the one-digit
specialization is imposed. -/
theorem synchronized_alignment_clearing_depth_independence
    {b p m D E : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    0 < primeBasePeriod b p hp hpb ∧
      clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) =
        clearedAlignmentReal b p m E (primeBasePeriod b p hp hpb) :=
  ⟨primeBasePeriod_pos hp hpb,
    clearedAlignmentReal_independent_of_clearing_depth hp hpb hm hD hE⟩

/-- Decimal division modulo three really has a one-digit periodic tail. -/
theorem base_ten_one_digit_period (r j : ℕ) :
    digitAt 10 3 r j = digitBin 10 3 (r % 3) :=
  digitAt_eq_initial_of_mod_one (by norm_num) (by norm_num)

/-- Manuscript Lemma `The Three Classes`, including the terminating class,
the aligned reference class, and the nines-complement class. -/
theorem base_ten_three_classes {m : ℕ} (hm : Supported 10 m) :
    ∃ D : ℕ, m ∣ 10 ^ D ∧ ∀ k : ℕ, 1 ≤ k → k < 3 * m →
      (k % 3 = 0 ∧ TerminatesInBase 10 k (3 * m)) ∨
      (k % 3 = 1 ∧ ¬TerminatesInBase 10 k (3 * m) ∧
        digitBin 10 3 ((k * clearingCofactor 10 m D) % 3) =
          digitBin 10 3 (clearingCofactor 10 m D % 3)) ∨
      (k % 3 = 2 ∧ ¬TerminatesInBase 10 k (3 * m) ∧
        digitBin 10 3 ((k * clearingCofactor 10 m D) % 3) +
          digitBin 10 3 (clearingCofactor 10 m D % 3) = 9) := by
  rcases hm with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  intro k _hkpos _hkbound
  have hu : Nat.Coprime 3 (clearingCofactor 10 m D) :=
    prime_coprime_clearingCofactor Nat.prime_three (by norm_num) hD
  have hterm := terminatesInBase_iff_residue_zero Nat.prime_three
    (by norm_num) ⟨D, hD⟩ (k := k)
  have hklt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hcase : k % 3
  · exact Or.inl ⟨rfl, hterm.mpr rfl⟩
  · right; left
    refine ⟨rfl, fun h => by simpa using hterm.mp h, ?_⟩
    have htransport :
        (k * clearingCofactor 10 m D) % 3 =
          clearingCofactor 10 m D % 3 := by
      simp [Nat.mul_mod, hcase]
    rw [htransport]
  · right; right
    refine ⟨rfl, fun h => by simpa using hterm.mp h, ?_⟩
    have htransport :
        (k * clearingCofactor 10 m D) % 3 =
          (2 * clearingCofactor 10 m D) % 3 := by
      simp [Nat.mul_mod, hcase]
    rw [htransport]
    exact base_ten_residue_two_is_nines_complement hu

/-- The universal fraction complement and its base-ten digit realization. -/
theorem complement_pairing
    (k n : ℚ) (hn : n ≠ 0) {u : ℕ} (hu : Nat.Coprime 3 u) :
    k / n + (n - k) / n = 1 ∧
      digitBin 10 3 ((2 * u) % 3) + digitBin 10 3 (u % 3) = 9 :=
  ⟨rationalFractionComplement k n hn,
    base_ten_residue_two_is_nines_complement hu⟩

/-- Manuscript Theorem `Alignment Formula`, now stated for the literal
synchronized average rather than only for its reduced closed form. -/
theorem base_ten_alignment_formula
    {m D : ℕ} (hm : m ∣ 10 ^ D) :
    synchronizedOneDigitAlignment 10 3 m D =
        ((2 * m - 1 : ℕ) : ℚ) / ((3 * m - 1 : ℕ) : ℚ) ∧
      clearedAlignmentReal 10 3 m D 1 = alignmentFormulaReal 3 m := by
  have hmPos : 1 ≤ m := by
    exact Nat.pos_of_dvd_of_pos hm (by positivity)
  exact ⟨synchronizedOneDigitAlignment_eq Nat.prime_three
      (by norm_num) (by norm_num) (by norm_num) hm,
    clearedOneDigitAlignmentReal_eq Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) hmPos hm⟩

/-- Manuscript Corollary following the alignment formula: strict increase from
below and convergence to `2/3`. -/
theorem prime_three_alignment_limit_and_monotonicity :
    StrictMonoOn (alignmentFormulaReal 3) (Set.Ici 1) ∧
    (∀ m : ℕ, 1 ≤ m → alignmentFormulaReal 3 m < (2 : ℝ) / 3) ∧
    Tendsto (alignmentFormulaReal 3) atTop (nhds ((2 : ℝ) / 3)) ∧
    Tendsto (fun D : ℕ => alignmentFormulaReal 3 (10 ^ D)) atTop
      (nhds ((2 : ℝ) / 3)) :=
  ⟨alignmentFormulaReal_three_strictMonoOn,
    fun _ hm => alignmentFormulaReal_three_below_limit hm,
    alignmentFormulaReal_three_tendsto,
    alignmentFormulaReal_three_tendsto_along_decimal_powers⟩

/-- The exact derivative calculation displayed in that corollary. -/
theorem prime_three_alignment_profile_derivative
    {x : ℝ} (hx : 1 ≤ x) :
    deriv (oneDigitAlignmentProfile 3) x = 1 / (3 * x - 1) ^ 2 ∧
      0 < deriv (oneDigitAlignmentProfile 3) x := by
  have hden : 3 * x - 1 ≠ 0 := by nlinarith
  exact ⟨oneDigitAlignmentProfile_three_deriv_eq hden,
    oneDigitAlignmentProfile_three_deriv_pos hx⟩

/-- Manuscript Theorem `Golden Threshold`. -/
theorem golden_threshold {m : ℕ} (hm : 1 ≤ m) :
    (alignmentFormulaReal 3 m ≥ goldenReciprocal ↔
      (m : ℝ) ≥ goldenRatio ^ 2) ∧
    ((m : ℝ) ≥ goldenRatio ^ 2 ↔ 3 ≤ m) ∧
    (2 : ℝ) < goldenRatio ^ 2 ∧ goldenRatio ^ 2 < 3 :=
  ⟨prime_three_golden_threshold_full hm,
    nat_ge_goldenRatio_sq_iff m,
    goldenRatio_sq_gt_two,
    goldenRatio_sq_lt_three⟩

/-- Manuscript decimal classification and its first exact crossing. -/
theorem base_ten_first_golden_crossing {m : ℕ}
    (hmPos : 1 ≤ m) (hm : Supported 10 m) :
    (alignmentFormulaReal 3 m > goldenReciprocal ↔ 4 ≤ m) ∧
      alignmentFormulaReal 3 4 = (7 : ℝ) / 11 :=
  ⟨base_ten_supported_golden_threshold hmPos hm,
    first_base_ten_crossing_value⟩

/-- Manuscript Theorem `General prime threshold`: literal synchronized formula
and exact reciprocal-golden prime selection. -/
theorem general_prime_threshold
    {b p : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1) :
    (∀ m D : ℕ, m ∣ b ^ D →
      synchronizedOneDigitAlignment b p m D =
          ((2 * m - 1 : ℕ) : ℚ) / ((p * m - 1 : ℕ) : ℚ) ∧
        clearedAlignmentReal b p m D 1 = alignmentFormulaReal p m) ∧
    ((∃ m : ℕ, 1 ≤ m ∧ Supported b m ∧
        alignmentFormulaReal p m ≥ goldenReciprocal) ↔
      p = 2 ∨ p = 3) ∧
    (p = 2 → ∀ m : ℕ, 1 ≤ m → alignmentFormulaReal p m = 1) ∧
    (p = 3 → ∀ m : ℕ, 1 ≤ m →
      (alignmentFormulaReal p m ≥ goldenReciprocal ↔ 3 ≤ m)) ∧
    (5 ≤ p → ∀ m : ℕ, 1 ≤ m →
      alignmentFormulaReal p m < goldenReciprocal) :=
  ⟨fun m D hm => by
      have hmPos : 1 ≤ m := Nat.pos_of_dvd_of_pos hm (by positivity)
      exact ⟨synchronizedOneDigitAlignment_eq hp hb hpb hmod hm,
        clearedOneDigitAlignmentReal_eq hp hb hpb hmod hmPos hm⟩,
    supported_prime_golden_selection hp hb hpb hmod,
    fun hp2 m hm => by
      subst p
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hden : (2 : ℝ) * m - 1 ≠ 0 := by nlinarith
      rw [alignmentFormulaReal]
      norm_num only [Nat.cast_ofNat]
      exact div_self hden,
    fun hp3 m hm => by subst p; exact prime_three_golden_threshold hm,
    fun hp5 m hm => large_prime_below_golden hp5 hm⟩

/-- Manuscript Corollary `Threshold window`. -/
theorem threshold_window
    {b p : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1)
    {t : ℝ} (htLower : (2 : ℝ) / 5 < t)
    (htUpper : t < (2 : ℝ) / 3) :
    (∃ m : ℕ, 1 ≤ m ∧ Supported b m ∧
      t ≤ alignmentFormulaReal p m) ↔ p = 2 ∨ p = 3 :=
  supported_prime_threshold_window hp hb hpb hmod htLower htUpper

/-- Manuscript definition of critical resolution, verified by solving the
alignment equation. -/
theorem critical_resolution_equation
    {p : ℕ} {m τ : ℝ} (hden : 2 - (p : ℝ) * τ ≠ 0)
    (halignDen : (p : ℝ) * m - 1 ≠ 0) :
    (2 * m - 1) / ((p : ℝ) * m - 1) = τ ↔
      m = criticalResolution τ p :=
  alignment_eq_threshold_iff_criticalResolution hden halignDen

/-- The reciprocal-square condition is exactly the manuscript's cubic. -/
theorem reciprocal_square_closure_cubic
    {p : ℕ} {τ : ℝ} (hp : 0 < p)
    (hτ : 0 < τ) (hrange : τ < 2 / (p : ℝ)) :
    criticalResolution τ p = 1 / τ ^ 2 ↔
      selfReferentialCubicValue p τ = 0 :=
  criticalResolution_eq_reciprocal_sq_iff hτ hrange hp

/-- Manuscript Lemma `Unique root`, including the sharper location and positive
critical resolution. -/
theorem unique_self_referential_root {p : ℕ} (hp : 3 ≤ p) :
    ∃! τ : ℝ, τ ∈ Set.Ioo 0 1 ∧
      selfReferentialCubicValue p τ = 0 ∧
      τ < 2 / (p : ℝ) ∧ 0 < criticalResolution τ p := by
  rcases exists_unique_selfReferential_root hp with ⟨τ, hτ, hunique⟩
  refine ⟨τ, ⟨hτ.1, hτ.2,
    selfReferential_root_lt_two_div hp hτ.1 hτ.2,
    selfReferential_root_criticalResolution_pos hp hτ.1 hτ.2⟩, ?_⟩
  intro σ hσ
  exact hunique σ ⟨hσ.1, hσ.2.1⟩

/-- The manuscript's separate treatment of the degenerate prime two. -/
theorem prime_two_has_no_admissible_self_reference :
    ∀ τ : ℝ, τ ∈ Set.Ioo 0 1 →
      selfReferentialCubicValue 2 τ ≠ 0 :=
  fun _ hτ => prime_two_no_selfReferential_root hτ

/-- Manuscript Theorem `Cubic factors`. -/
theorem rational_cubic_factorization
    {p : ℕ} (hp : p.Prime) :
    (¬Irreducible (selfReferentialCubic p) ↔
      p = 2 ∨ p = 3 ∨ p = 5) ∧
    selfReferentialCubic 2 = (X - 1) * (X ^ 2 - 2) ∧
    selfReferentialCubic 3 = (X - 2) * (X ^ 2 + X - 1) ∧
    selfReferentialCubic 5 = (X + 2) * (X ^ 2 - 3 * X + 1) ∧
    ((selfReferentialCubic p).eval 1 = 2 - p ∧
      (selfReferentialCubic p).eval (-1) = p ∧
      (selfReferentialCubic p).eval 2 = 6 - 2 * p ∧
      (selfReferentialCubic p).eval (-2) = 2 * p - 10) ∧
    (7 ≤ p → Irreducible (selfReferentialCubic p)) :=
  ⟨selfReferentialCubic_reducible_iff_prime_exception hp,
    selfReferentialCubic_two_factorization,
    selfReferentialCubic_three_factorization,
    selfReferentialCubic_five_factorization,
    selfReferentialCubic_candidate_values p,
    fun hp7 => selfReferentialCubic_irreducible hp7⟩

/-- Manuscript Theorem `Golden field`, with the higher-prime conclusion stated
as absence of every rational relation of degree at most two. -/
theorem golden_field_thresholds :
    selfReferentialCubicValue 3 goldenReciprocal = 0 ∧
    goldenReciprocal = (Real.sqrt 5 - 1) / 2 ∧
    goldenReciprocal = 1 / goldenRatio ∧
    selfReferentialCubicValue 5 (goldenReciprocal ^ 2) = 0 ∧
    goldenReciprocal ^ 2 = (3 - Real.sqrt 5) / 2 ∧
    goldenReciprocal ^ 2 = 1 / goldenRatio ^ 2 ∧
    (∀ τ : ℝ, τ ∈ Set.Ioo 0 1 →
      selfReferentialCubicValue 3 τ = 0 → τ = goldenReciprocal) ∧
    (∀ τ : ℝ, τ ∈ Set.Ioo 0 1 →
      selfReferentialCubicValue 5 τ = 0 → τ = goldenReciprocal ^ 2) ∧
    (∀ p : ℕ, 7 ≤ p → ∀ τ : ℝ,
      selfReferentialCubicValue p τ = 0 →
      (minpoly ℚ τ).natDegree = 3 ∧
      ¬∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 2 ∧ aeval τ q = 0) :=
  ⟨goldenReciprocal_selfReferential_root,
    rfl,
    goldenReciprocal_eq_inv,
    goldenReciprocal_sq_selfReferential_root,
    goldenReciprocal_sq_closed_form,
    goldenReciprocal_sq_eq_goldenRatio_inv_sq,
    fun _ hτ hroot => selfReferential_root_three_eq_goldenReciprocal hτ hroot,
    fun _ hτ hroot => selfReferential_root_five_eq_goldenReciprocal_sq hτ hroot,
    fun _ hp _ hroot => ⟨selfReferential_root_minpoly_natDegree hp hroot,
      selfReferential_root_has_no_quadratic_rational_relation hp hroot⟩⟩

/-- Manuscript Corollary `Unique in the separating window`. -/
theorem unique_self_reference_in_separating_window
    {p : ℕ} (hp : p.Prime) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo 0 1)
    (hroot : selfReferentialCubicValue p τ = 0) :
    τ ∈ Set.Ioo ((2 : ℝ) / 5) (2 / 3) ↔
      p = 3 ∧ τ = goldenReciprocal :=
  selfReferential_root_in_separating_window_iff hp hτ hroot

/-- Exact inequalities behind the manuscript's self-referential hierarchy. -/
theorem self_referential_hierarchy_bounds :
    goldenReciprocal ^ 2 < (2 : ℝ) / 5 ∧
      (2 : ℝ) / 5 < goldenReciprocal ∧
      goldenReciprocal < (2 : ℝ) / 3 ∧
      (∀ p : ℕ, 7 ≤ p → ∀ τ : ℝ,
        τ ∈ Set.Ioo 0 1 → selfReferentialCubicValue p τ = 0 →
          τ < 2 / (p : ℝ)) :=
  ⟨goldenReciprocal_sq_lt_two_fifths,
    two_fifths_lt_goldenReciprocal,
    goldenReciprocal_lt_two_thirds,
    fun _ hp _ hτ hroot =>
      selfReferential_root_lt_two_div (by omega) hτ hroot⟩

/-- Manuscript Corollary `Fourth power`: exact polynomial division,
minimal-polynomial divisibility, and the resulting identity. -/
theorem reciprocal_golden_polynomial_division_and_fourth_power (p : ℕ) :
    goldenReciprocalPolynomial = minpoly ℚ goldenReciprocal ∧
    selfReferentialCubic p =
      (X - 2) * goldenReciprocalPolynomial + C ((3 : ℚ) - p) * X ∧
    (goldenReciprocalPolynomial ∣ selfReferentialCubic p ↔ p = 3) ∧
      goldenReciprocal ^ 4 = 2 - 3 * goldenReciprocal :=
  ⟨goldenReciprocalPolynomial_eq_minpoly,
    goldenReciprocalPolynomial_division p,
    goldenReciprocalPolynomial_dvd_selfReferentialCubic_iff p,
    goldenReciprocal_fourth_power⟩

/-- Manuscript remark on excluding terminating fractions. -/
theorem nonterminating_alignment :
    (∀ m : ℕ, 1 ≤ m →
      nonterminatingOneDigitAlignment 3 m = 1 / 2) ∧
    (∀ p m : ℕ, 1 < p → 1 ≤ m →
      nonterminatingOneDigitAlignment p m =
        1 / ((p - 1 : ℕ) : ℚ)) :=
  ⟨fun _ hm => nonterminatingOneDigitAlignment_prime_three hm,
    fun _ _ hp hm => nonterminatingOneDigitAlignment_eq hp hm⟩

/-- Exact verification of every rational value in the displayed table. -/
theorem displayed_alignment_table :
    oneDigitAlignment 3 1 = 1 / 2 ∧
    oneDigitAlignment 3 2 = 3 / 5 ∧
    oneDigitAlignment 3 4 = 7 / 11 ∧
    oneDigitAlignment 3 5 = 9 / 14 ∧
    oneDigitAlignment 3 8 = 15 / 23 ∧
    oneDigitAlignment 3 10 = 19 / 29 ∧
    oneDigitAlignment 3 16 = 31 / 47 ∧
    oneDigitAlignment 3 32 = 63 / 95 ∧
    oneDigitAlignment 3 100 = 199 / 299 ∧
    oneDigitAlignment 3 256 = 511 / 767 ∧
    (WithinFourDecimalRounding (oneDigitAlignment 3 1) (5000 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 2) (6000 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 4) (6364 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 5) (6429 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 8) (6522 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 10) (6552 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 16) (6596 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 32) (6632 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 100) (6656 / 10000) ∧
      WithinFourDecimalRounding (oneDigitAlignment 3 256) (6662 / 10000)) := by
  rcases prime_three_displayed_alignment_values with
    ⟨h1, h2, h4, h5, h8, h10, h16, h32, h100, h256⟩
  exact ⟨h1, h2, h4, h5, h8, h10, h16, h32, h100, h256,
    prime_three_displayed_decimal_roundings⟩

end NField.Papers.GoldenRatioSelectsPrimeThree
