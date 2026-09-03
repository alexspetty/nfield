/-
Author: Alexander S. Petty
-/

import NField.Alignment.OneDigitPrime
import NField.Alignment.CanonicalSynchronizedAlignment

/-!
# The alignment-deficit lattice

Reusable exact arithmetic for the Lean companion to
"The Alignment Deficit Lattice and Musical Tuning".

The synchronized long-division classification and alignment count are imported
from `NField.Alignment.OneDigitPrime`.  This module starts at the resulting
closed alignment formula, proves the exact deficit and ratio identities, and
then checks the tuning examples using exact rational arithmetic.
-/

namespace NField.Alignment.DeficitLattice

open Filter
open NField.Alignment

/-- The manuscript's exact alignment formula, written without natural-number
subtraction inside the rational field. -/
def alignmentFormula (p m : ℕ) : ℚ :=
  ((2 : ℚ) * m - 1) / ((p : ℚ) * m - 1)

/-- The alignment deficit from the limiting value `2/p`. -/
def alignmentDeficit (p m : ℕ) : ℚ :=
  (2 : ℚ) / p - alignmentFormula p m

/-- The formula used for a pair of points on the supported monoid. -/
def scaledDeficitRatio (p u v t : ℕ) : ℚ :=
  alignmentDeficit p (t * u) / alignmentDeficit p (t * v)

/-- The same finite ratio in the real numbers, convenient for its limit. -/
noncomputable def scaledDeficitRatioReal (p u v t : ℕ) : ℝ :=
  (((p : ℝ) * v) * t - 1) / (((p : ℝ) * u) * t - 1)

/-- Signed additive error from the limiting interval `v/u`. -/
def scaledRatioError (p u v t : ℕ) : ℚ :=
  scaledDeficitRatio p u v t - (v : ℚ) / u

/-- Signed relative error from the limiting interval `v/u`. -/
def scaledRelativeError (p u v t : ℕ) : ℚ :=
  scaledDeficitRatio p u v t / ((v : ℚ) / u) - 1

/-- The residue-count alignment imported from the synchronized clock is exactly
the field-valued formula used by this module. -/
theorem oneDigitAlignment_eq_alignmentFormula {p m : ℕ}
    (hp : Nat.Prime p) (hm : 1 ≤ m) :
    oneDigitAlignment p m = alignmentFormula p m := by
  rw [oneDigitAlignment_eq hp]
  unfold alignmentFormula
  have htwo : 1 ≤ 2 * m := by omega
  have hpm : 1 ≤ p * m := by nlinarith [hp.two_le]
  push_cast [Nat.cast_sub htwo, Nat.cast_sub hpm]
  rfl

/-- Closed form for the alignment deficit. -/
theorem alignmentDeficit_eq {p m : ℕ} (hp : 3 ≤ p) (hm : 1 ≤ m) :
    alignmentDeficit p m =
      ((p : ℚ) - 2) / ((p : ℚ) * ((p : ℚ) * m - 1)) := by
  unfold alignmentDeficit alignmentFormula
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have hden : (p : ℚ) * m - 1 ≠ 0 := by
    have : (1 : ℚ) < (p : ℚ) * m := by
      exact_mod_cast (show 1 < p * m by nlinarith)
    nlinarith
  field_simp
  ring

/-- The deficit is positive on the manuscript domain. -/
theorem alignmentDeficit_pos {p m : ℕ} (hp : 3 ≤ p) (hm : 1 ≤ m) :
    0 < alignmentDeficit p m := by
  rw [alignmentDeficit_eq hp hm]
  have hnum : (0 : ℚ) < (p : ℚ) - 2 :=
    sub_pos.mpr (by exact_mod_cast (show 2 < p by omega))
  have hden : (0 : ℚ) < (p : ℚ) * ((p : ℚ) * m - 1) := by
    have hpq : (0 : ℚ) < p := by positivity
    have hinner : (0 : ℚ) < (p : ℚ) * m - 1 := by
      apply sub_pos.mpr
      exact_mod_cast (show 1 < p * m by nlinarith)
    positivity
  positivity

/-- Increasing the positive monoid coordinate strictly decreases the deficit. -/
theorem alignmentDeficit_lt_of_lt {p m n : ℕ} (hp : 3 ≤ p)
    (hm : 1 ≤ m) (hmn : m < n) :
    alignmentDeficit p n < alignmentDeficit p m := by
  have hn : 1 ≤ n := by omega
  rw [alignmentDeficit_eq hp hn, alignmentDeficit_eq hp hm]
  have hnum : (0 : ℚ) < (p : ℚ) - 2 :=
    sub_pos.mpr (by exact_mod_cast (show 2 < p by omega))
  have hdenm : (0 : ℚ) < (p : ℚ) * ((p : ℚ) * m - 1) := by
    have : (0 : ℚ) < (p : ℚ) * m - 1 := by
      apply sub_pos.mpr
      exact_mod_cast (show 1 < p * m by nlinarith)
    positivity
  have hdenlt :
      (p : ℚ) * ((p : ℚ) * m - 1) <
        (p : ℚ) * ((p : ℚ) * n - 1) := by
    have hpq : (0 : ℚ) < p := by positivity
    have hmnq : (m : ℚ) < n := by exact_mod_cast hmn
    have hmul : (p : ℚ) * m < (p : ℚ) * n :=
      mul_lt_mul_of_pos_left hmnq hpq
    have hinner : (p : ℚ) * m - 1 < (p : ℚ) * n - 1 :=
      sub_lt_sub_right hmul 1
    exact mul_lt_mul_of_pos_left hinner hpq
  exact div_lt_div_of_pos_left hnum hdenm hdenlt

/-- The deficit is injective on positive natural inputs. -/
theorem alignmentDeficit_injective_on_positive {p m n : ℕ} (hp : 3 ≤ p)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (heq : alignmentDeficit p m = alignmentDeficit p n) : m = n := by
  rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
  · exact False.elim ((ne_of_lt (alignmentDeficit_lt_of_lt hp hm hmn)) heq.symm)
  · exact hmn
  · exact False.elim ((ne_of_lt (alignmentDeficit_lt_of_lt hp hn hmn)) heq)

/-- Exact deficit ratio at two positive finite points. -/
theorem alignmentDeficit_ratio_eq {p m₁ m₂ : ℕ} (hp : 3 ≤ p)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    alignmentDeficit p m₁ / alignmentDeficit p m₂ =
      ((p : ℚ) * m₂ - 1) / ((p : ℚ) * m₁ - 1) := by
  rw [alignmentDeficit_eq hp hm₁, alignmentDeficit_eq hp hm₂]
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have hnum : (p : ℚ) - 2 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast (show 2 < p by omega)))
  have hden₁ : (p : ℚ) * m₁ - 1 ≠ 0 := by
    have : (1 : ℚ) < (p : ℚ) * m₁ := by
      exact_mod_cast (show 1 < p * m₁ by nlinarith)
    nlinarith
  have hden₂ : (p : ℚ) * m₂ - 1 ≠ 0 := by
    have : (1 : ℚ) < (p : ℚ) * m₂ := by
      exact_mod_cast (show 1 < p * m₂ by nlinarith)
    nlinarith
  field_simp

/-- Exact ratio after the common supported scaling factor is exposed. -/
theorem scaledDeficitRatio_eq {p u v t : ℕ} (hp : 3 ≤ p)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 1 ≤ t) :
    scaledDeficitRatio p u v t =
      ((p : ℚ) * t * v - 1) / ((p : ℚ) * t * u - 1) := by
  unfold scaledDeficitRatio
  have htu : 1 ≤ t * u := by
    have h := Nat.mul_le_mul ht hu
    norm_num at h ⊢
    exact h
  have htv : 1 ≤ t * v := by
    have h := Nat.mul_le_mul ht hv
    norm_num at h ⊢
    exact h
  rw [alignmentDeficit_ratio_eq hp htu htv]
  push_cast
  ring

/-- The signed finite error from `v/u` has a one-line exact form. -/
theorem scaledRatioError_eq {p u v t : ℕ} (hp : 3 ≤ p)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 1 ≤ t) :
    scaledRatioError p u v t =
      ((v : ℚ) - u) / ((u : ℚ) * ((p : ℚ) * t * u - 1)) := by
  unfold scaledRatioError
  rw [scaledDeficitRatio_eq hp hu hv ht]
  have hu0 : (u : ℚ) ≠ 0 := by positivity
  have hden : (p : ℚ) * t * u - 1 ≠ 0 := by
    have : (1 : ℚ) < (p : ℚ) * t * u := by
      have hpt : 3 * 1 ≤ p * t := Nat.mul_le_mul hp ht
      have hptu : (3 * 1) * 1 ≤ (p * t) * u := Nat.mul_le_mul hpt hu
      exact_mod_cast (show 1 < p * t * u by norm_num at hptu ⊢; omega)
    nlinarith
  field_simp
  ring

/-- Exact relative error used by the finite tuning tables. -/
theorem scaledRelativeError_eq {p u v t : ℕ} (hp : 3 ≤ p)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 1 ≤ t) :
    scaledRelativeError p u v t =
      ((v : ℚ) - u) / ((v : ℚ) * ((p : ℚ) * t * u - 1)) := by
  unfold scaledRelativeError
  rw [scaledDeficitRatio_eq hp hu hv ht]
  have hu0 : (u : ℚ) ≠ 0 := by positivity
  have hv0 : (v : ℚ) ≠ 0 := by positivity
  have hden : (p : ℚ) * t * u - 1 ≠ 0 := by
    have : (1 : ℚ) < (p : ℚ) * t * u := by
      have hpt : 3 * 1 ≤ p * t := Nat.mul_le_mul hp ht
      have hptu : (3 * 1) * 1 ≤ (p * t) * u := Nat.mul_le_mul hpt hu
      exact_mod_cast (show 1 < p * t * u by norm_num at hptu ⊢; omega)
    nlinarith
  field_simp
  ring

/-- For fixed positive parameters, the finite relative error is strictly
increasing in the represented interval endpoint above the reference point. -/
theorem scaledRelativeError_lt_of_lt {p u v w t : ℕ} (hp : 3 ≤ p)
    (hu : 1 ≤ u) (ht : 1 ≤ t) (huv : u ≤ v) (hvw : v < w) :
    scaledRelativeError p u v t < scaledRelativeError p u w t := by
  have hv : 1 ≤ v := le_trans hu huv
  have hw : 1 ≤ w := by omega
  rw [scaledRelativeError_eq hp hu hv ht,
    scaledRelativeError_eq hp hu hw ht]
  have hptu : 1 < p * t * u := by
    have hmul : 3 * 1 * 1 ≤ p * t * u :=
      Nat.mul_le_mul (Nat.mul_le_mul hp ht) hu
    norm_num at hmul ⊢
    omega
  have hcore : (0 : ℚ) < (p : ℚ) * t * u - 1 := by
    have : (1 : ℚ) < (p : ℚ) * t * u := by exact_mod_cast hptu
    linarith
  have hvq : (0 : ℚ) < v := by positivity
  have hwq : (0 : ℚ) < w := by positivity
  rw [div_lt_div_iff₀ (mul_pos hvq hcore) (mul_pos hwq hcore)]
  have huvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hvwq : (v : ℚ) < w := by exact_mod_cast hvw
  have huq : (0 : ℚ) < u := by positivity
  have hbase : ((v : ℚ) - u) * w < ((w : ℚ) - u) * v := by
    have hgap : (0 : ℚ) < (w : ℚ) - v := sub_pos.mpr hvwq
    nlinarith [mul_pos huq hgap]
  convert mul_lt_mul_of_pos_right hbase hcore using 1 <;> ring

/-- The exact finite ratios converge to the represented interval.  The theorem
is stronger than a limit restricted to supported `t`, since it holds along all
positive natural scales. -/
theorem scaledDeficitRatioReal_tendsto {p u v : ℕ}
    (hp : 1 ≤ p) (hu : 1 ≤ u) :
    Tendsto (scaledDeficitRatioReal p u v) atTop
      (nhds ((v : ℝ) / u)) := by
  have hden : (p : ℝ) * u ≠ 0 := by positivity
  convert (tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) ((p : ℝ) * v) (d := (p : ℝ) * u) hden) using 1
  · funext t
    simp only [scaledDeficitRatioReal, sub_eq_add_neg]
    ring
  · field_simp

/-- Scaling by one supported generator converges to that generator. -/
theorem generatorScaling_tendsto {p q : ℕ} (hp : 1 ≤ p) :
    Tendsto (scaledDeficitRatioReal p 1 q) atTop (nhds (q : ℝ)) := by
  simpa using scaledDeficitRatioReal_tendsto (p := p) (u := 1) (v := q)
    hp (by norm_num)

/-- Exact finite generator-scaling identity before taking the limit. -/
theorem generatorScaling_eq {p q m : ℕ} (hp : 3 ≤ p)
    (hq : 1 ≤ q) (hm : 1 ≤ m) :
    alignmentDeficit p m / alignmentDeficit p (q * m) =
      (q : ℚ) + ((q : ℚ) - 1) / ((p : ℚ) * m - 1) := by
  have hqm : 1 ≤ q * m := by
    have h := Nat.mul_le_mul hq hm
    norm_num at h ⊢
    exact h
  rw [alignmentDeficit_ratio_eq hp hm hqm]
  push_cast
  have hden : (p : ℚ) * m - 1 ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    exact_mod_cast (show 1 < p * m by nlinarith)
  field_simp
  ring

/-- One certificate packages the exact finite ratio, exact relative error, and
the limiting interval for a whole scaled family. -/
theorem scaledFamily_certificate {p u v : ℕ} (hp : 3 ≤ p)
    (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (∀ t : ℕ, 1 ≤ t →
      scaledDeficitRatio p u v t =
          ((p : ℚ) * t * v - 1) / ((p : ℚ) * t * u - 1) ∧
        scaledRelativeError p u v t =
          ((v : ℚ) - u) / ((v : ℚ) * ((p : ℚ) * t * u - 1))) ∧
      Tendsto (scaledDeficitRatioReal p u v) atTop
        (nhds ((v : ℝ) / u)) := by
  constructor
  · intro t ht
    exact ⟨scaledDeficitRatio_eq hp hu hv ht,
      scaledRelativeError_eq hp hu hv ht⟩
  · exact scaledDeficitRatioReal_tendsto (by omega) hu

/-- Supported denominators are closed under multiplication. -/
theorem supported_mul {b m n : ℕ} (hm : Supported b m) (hn : Supported b n) :
    Supported b (m * n) := by
  rcases hm with ⟨D, hD⟩
  rcases hn with ⟨E, hE⟩
  refine ⟨D + E, ?_⟩
  rw [pow_add]
  exact Nat.mul_dvd_mul hD hE

/-- Every divisor of a supported denominator is supported. -/
theorem supported_of_dvd {b m n : ℕ} (hmn : m ∣ n) (hn : Supported b n) :
    Supported b m := by
  rcases hn with ⟨D, hD⟩
  exact ⟨D, dvd_trans hmn hD⟩

/-- A prime divisor of the base is one of the supported generators. -/
theorem supported_of_dvd_base {b q : ℕ} (hq : q ∣ b) : Supported b q := by
  exact ⟨1, by simpa using hq⟩

/-- The JMM hypotheses package the synchronized clock, exact alignment, and
closed deficit identity without adding any musical interpretation. -/
theorem alignmentDeficit_certificate {b p m : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hb : 2 ≤ b)
    (hmod : b % p = 1) (hm : 1 ≤ m) (hsupported : Supported b m) :
    ∃ D : ℕ,
      m ∣ b ^ D ∧
      (∀ k : ℕ,
        synchronizedAligned b p (clearingCofactor b m D) k ↔
          k % p = 0 ∨ k % p = 1) ∧
      oneDigitAlignment p m = alignmentFormula p m ∧
      alignmentDeficit p m =
        ((p : ℚ) - 2) / ((p : ℚ) * ((p : ℚ) * m - 1)) := by
  have hpb : ¬p ∣ b := by
    intro hdvd
    have hz : b % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  rcases generalPrimeAlignment_certificate hp hb hpb hmod hsupported with
    ⟨D, hD, hclasses, _halignment⟩
  exact ⟨D, hD, hclasses, oneDigitAlignment_eq_alignmentFormula hp hm,
    alignmentDeficit_eq hp3 hm⟩

/-! ## Exact musical fixtures -/

/-- Both inputs to the Pythagorean-comma example are supported in base twelve. -/
theorem pythagorean_inputs_supported :
    Supported 12 (2 ^ 19) ∧ Supported 12 (3 ^ 12) := by
  constructor
  · exact ⟨19, by norm_num⟩
  · exact ⟨12, by norm_num⟩

/-- Exact finite Pythagorean-comma value quoted in the manuscript. -/
theorem pythagoreanComma_finite :
    scaledDeficitRatio 11 (2 ^ 19) (3 ^ 12) 1 =
      (5845850 : ℚ) / 5767167 := by
  rw [scaledDeficitRatio_eq (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- Both the exact finite ratio and its limiting comma lie in the rounding
window for the manuscript's displayed decimal `1.013643`. -/
theorem pythagoreanComma_decimal_window :
    (2027285 : ℚ) / 2000000 < (5845850 : ℚ) / 5767167 ∧
      (5845850 : ℚ) / 5767167 < (2027287 : ℚ) / 2000000 ∧
      (2027285 : ℚ) / 2000000 < (3 ^ 12 : ℚ) / (2 ^ 19) ∧
      (3 ^ 12 : ℚ) / (2 ^ 19) < (2027287 : ℚ) / 2000000 ∧
      |((5845850 : ℚ) / 5767167) / ((3 ^ 12 : ℚ) / (2 ^ 19)) - 1| <
        (1 : ℚ) / 1000 := by
  norm_num

/-- The base-twelve example has exactly one terminating and two matching
numerators, so its aligned count and normalized value are exactly those stated
in the manuscript. -/
theorem baseTwelve_twentyTwo_example :
    terminatingNumeratorCount 11 2 = 1 ∧
      matchingNumeratorCount 11 2 = 2 ∧
      alignedNumeratorCount 11 2 = 3 ∧
      oneDigitAlignment 11 2 = (3 : ℚ) / 21 := by
  constructor
  · norm_num [terminatingNumeratorCount_eq]
  constructor
  · norm_num [matchingNumeratorCount_eq]
  constructor
  · norm_num [alignedNumeratorCount_eq]
  · rw [oneDigitAlignment_eq (by norm_num)]
    norm_num

/-- The Pythagorean-comma deficit ratio converges to `3^12/2^19`. -/
theorem pythagoreanComma_tendsto :
    Tendsto (scaledDeficitRatioReal 11 (2 ^ 19) (3 ^ 12)) atTop
      (nhds (((3 ^ 12 : ℕ) : ℝ) / (2 ^ 19 : ℕ))) := by
  exact scaledDeficitRatioReal_tendsto (by norm_num) (by norm_num)

/-- Every integer used for the just major scale is supported in base thirty. -/
theorem majorScale_supported :
    Supported 30 24 ∧ Supported 30 27 ∧ Supported 30 30 ∧
    Supported 30 32 ∧ Supported 30 36 ∧ Supported 30 40 ∧
    Supported 30 45 ∧ Supported 30 48 := by
  repeat' apply And.intro
  all_goals exact ⟨5, by norm_num⟩

/-- The eight scale points have exactly the classical just-major ratios. -/
theorem majorScale_exact_ratios :
    (24 : ℚ) / 24 = 1 ∧
    (27 : ℚ) / 24 = 9 / 8 ∧
    (30 : ℚ) / 24 = 5 / 4 ∧
    (32 : ℚ) / 24 = 4 / 3 ∧
    (36 : ℚ) / 24 = 3 / 2 ∧
    (40 : ℚ) / 24 = 5 / 3 ∧
    (45 : ℚ) / 24 = 15 / 8 ∧
    (48 : ℚ) / 24 = 2 := by
  norm_num

/-- The successive diatonic steps are the classical whole-tone/semitone
pattern quoted in the manuscript. -/
theorem majorScale_step_ratios :
    (27 : ℚ) / 24 = 9 / 8 ∧
    (30 : ℚ) / 27 = 10 / 9 ∧
    (32 : ℚ) / 30 = 16 / 15 ∧
    (36 : ℚ) / 32 = 9 / 8 ∧
    (40 : ℚ) / 36 = 10 / 9 ∧
    (45 : ℚ) / 40 = 9 / 8 ∧
    (48 : ℚ) / 45 = 16 / 15 := by
  norm_num

/-- The finite relative errors for every just-major point satisfy the stated
strict `7.2e-4` bound. -/
theorem majorScale_relative_errors :
    |scaledRelativeError 29 24 24 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 27 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 30 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 32 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 36 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 40 1| < (9 : ℚ) / 12500 ∧
    |scaledRelativeError 29 24 45 1| < (9 : ℚ) / 12500 ∧
    scaledRelativeError 29 24 48 1 = (1 : ℚ) / 1390 ∧
    |scaledRelativeError 29 24 48 1| < (9 : ℚ) / 12500 := by
  repeat' apply And.intro
  all_goals
    rw [scaledRelativeError_eq (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    norm_num

/-- Each just-major point is the limit of its exact deficit-ratio sequence. -/
theorem majorScale_tendsto (m : ℕ) :
    Tendsto (scaledDeficitRatioReal 29 24 m) atTop
      (nhds ((m : ℝ) / 24)) := by
  exact scaledDeficitRatioReal_tendsto (by norm_num) (by norm_num)

/-- The manuscript's common denominator 24 is minimal among positive common
denominators for all eight displayed just-major ratios. -/
theorem majorScale_common_denominator_least {d : ℕ} (hd : 0 < d)
    (h9 : (8 : ℕ) ∣ d) (h5 : 4 ∣ d) (h4 : 3 ∣ d) :
    0 < d ∧ 4 ∣ d ∧ 24 ∣ d := by
  exact ⟨hd, h5, Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (by norm_num : Nat.Coprime 8 3) h9 h4⟩

/-- Twenty-five is another supported lattice point in the same octave and has
the stated chromatic-semitone ratio. -/
theorem justChromaticSemitone_fixture :
    Supported 30 25 ∧ (25 : ℚ) / 24 = 25 / 24 ∧
      25 ∉ ({24, 27, 30, 32, 36, 40, 45, 48} : Finset ℕ) := by
  exact ⟨⟨2, by norm_num⟩, rfl, by norm_num⟩

/-- One base with two eligible alignment primes exhibits different finite
coordinates and finite approximation errors for those primes. -/
theorem alignmentPrime_changes_finite_coordinate :
    66 % 5 = 1 ∧ 66 % 13 = 1 ∧ Nat.Prime 5 ∧ Nat.Prime 13 ∧
      alignmentDeficit 5 2 ≠ alignmentDeficit 13 2 ∧
      scaledRelativeError 5 1 2 1 ≠ scaledRelativeError 13 1 2 1 := by
  norm_num [alignmentDeficit, alignmentFormula, scaledRelativeError,
    scaledDeficitRatio]

/-- Exact seven-limit finite formulas in base 210 with alignment prime 11. -/
theorem sevenLimit_finite_formulas (t : ℕ) :
    scaledDeficitRatioReal 11 4 7 t =
        ((77 : ℝ) * t - 1) / (44 * t - 1) ∧
      scaledDeficitRatioReal 11 7 8 t =
        ((88 : ℝ) * t - 1) / (77 * t - 1) := by
  constructor <;> unfold scaledDeficitRatioReal <;> norm_num

/-- The two named seven-limit intervals are the exact limiting ratios. -/
theorem sevenLimit_tendsto :
    Tendsto (scaledDeficitRatioReal 11 4 7) atTop (nhds ((7 : ℝ) / 4)) ∧
      Tendsto (scaledDeficitRatioReal 11 7 8) atTop (nhds ((8 : ℝ) / 7)) := by
  exact ⟨scaledDeficitRatioReal_tendsto (by norm_num) (by norm_num),
    scaledDeficitRatioReal_tendsto (by norm_num) (by norm_num)⟩

/-- The complete base-210 hypotheses and supported inputs behind the two
seven-limit applications. -/
theorem sevenLimit_hypotheses :
    Nat.Prime 11 ∧ 210 % 11 = 1 ∧
      Supported 210 4 ∧ Supported 210 7 ∧ Supported 210 8 := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · exact ⟨2, by norm_num⟩
  constructor
  · exact ⟨1, by norm_num⟩
  · exact ⟨3, by norm_num⟩

/-- The worst chromatic endpoint error is the exact value and strict bound
quoted in the round-two manuscript. -/
theorem chromaticEndpoint_relative_error :
    scaledRelativeError 29 480 960 1 = (1 : ℚ) / 27838 ∧
      |scaledRelativeError 29 480 960 1| < (9 : ℚ) / 250000 := by
  constructor
  · rw [scaledRelativeError_eq (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    norm_num
  · rw [scaledRelativeError_eq (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    norm_num

/-- All thirteen common-denominator points in the stated five-limit chromatic
scale are supported in base thirty. -/
theorem chromaticScale_supported :
    Supported 30 480 ∧ Supported 30 512 ∧ Supported 30 540 ∧
    Supported 30 576 ∧ Supported 30 600 ∧ Supported 30 640 ∧
    Supported 30 675 ∧ Supported 30 720 ∧ Supported 30 768 ∧
    Supported 30 800 ∧ Supported 30 864 ∧ Supported 30 900 ∧
    Supported 30 960 := by
  repeat' apply And.intro
  all_goals exact ⟨9, by norm_num⟩

/-- The common-denominator chromatic points have exactly the thirteen ratios
listed in the round-two manuscript. -/
theorem chromaticScale_exact_ratios :
    (480 : ℚ) / 480 = 1 ∧
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
    (960 : ℚ) / 480 = 2 := by
  norm_num

/-- Every chromatic point satisfies the stated strict relative-error bound;
the endpoint equality is recorded separately above. -/
theorem chromaticScale_relative_errors :
    |scaledRelativeError 29 480 480 1| < (9 : ℚ) / 250000 ∧
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
    |scaledRelativeError 29 480 960 1| < (9 : ℚ) / 250000 := by
  repeat' apply And.intro
  all_goals
    rw [scaledRelativeError_eq (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    norm_num

end NField.Alignment.DeficitLattice
