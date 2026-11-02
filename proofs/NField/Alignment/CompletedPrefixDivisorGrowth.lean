/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.InverseResidueHarmonicRangeSplit
import NField.Alignment.DivisorSmallPowerBound

/-!
# Subpower growth of the completed inverse-prefix scale

The divisor and logarithmic factors in the printed completed-prefix bound
cost an arbitrarily small positive power. This proves SEC-04 from the
elementary divisor-count theorem; the Weil--Estermann and Korolev estimates
remain separate inputs.
-/

set_option autoImplicit false

namespace NField.Alignment.CompletedPrefixDivisorGrowth

open scoped BigOperators
open Filter
open DedekindInverseResidueTransform InverseResidueHarmonicRangeSplit

theorem reciprocal_sqrt_divisor_sum_nonneg (q : ℕ) :
    0 ≤ reciprocalSqrtDivisorSum q := by
  unfold reciprocalSqrtDivisorSum
  positivity

theorem reciprocal_sqrt_divisor_sum_le_count (q : ℕ) :
    reciprocalSqrtDivisorSum q ≤ (q.divisors.card : ℝ) := by
  unfold reciprocalSqrtDivisorSum
  calc
    _ ≤ ∑ d ∈ q.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.pos_of_mem_divisors hd
      exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hd1)
    _ = _ := by simp

theorem log_two_mul_small_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      Real.log (2 * (q : ℝ)) ≤ 2 * (q : ℝ) ^ ε := by
  have hsmall := (isLittleO_log_rpow_atTop hε).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop 2] with q hb hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  simp only [Function.comp_apply, Real.norm_eq_abs, one_mul,
    abs_of_nonneg hlog, abs_of_nonneg (Real.rpow_nonneg hqpos.le ε)] at hb
  calc
    Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
      Real.log_mul (by norm_num) hqpos.ne'
    _ ≤ 2 * Real.log (q : ℝ) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hq : (2 : ℝ) ≤ q)
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

/-- The literal scale in the completed-prefix lemma is
`O(q^(1/2+ε))` for every positive ε, with a single constant and threshold
independent of q. No inverse-residue estimate is assumed. -/
theorem completed_prefix_scale_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ threshold : ℕ, ∀ q, threshold ≤ q →
      completedInversePrefixScale q ≤ C * (q : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨D, hD, hdiv⟩ :=
    DivisorSmallPowerBound.divisor_count_small_power (ε / 4) (by positivity)
  have hlog := log_two_mul_small_power (ε / 4) (by positivity)
  obtain ⟨threshold, ht⟩ := eventually_atTop.1 hlog
  refine ⟨4 * D ^ 2, by positivity, max threshold 2, ?_⟩
  intro q hq
  have hq2 : 2 ≤ q := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have htq := ht q ((le_max_left _ _).trans hq)
  have hd := hdiv q (by omega)
  have hs := (reciprocal_sqrt_divisor_sum_le_count q).trans hd
  have hs0 := reciprocal_sqrt_divisor_sum_nonneg q
  have hlog0 : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith)
  calc
    completedInversePrefixScale q ≤
        (q : ℝ).sqrt * (D * (q : ℝ) ^ (ε / 4)) *
          (D * (q : ℝ) ^ (ε / 4)) * (2 * (q : ℝ) ^ (ε / 4)) ^ 2 := by
      unfold completedInversePrefixScale
      gcongr
    _ = (4 * D ^ 2) * (q : ℝ) ^ (1 / 2 + ε) := by
      rw [Real.sqrt_eq_rpow]
      have hpow : ((q : ℝ) ^ (ε / 4)) ^ 4 = (q : ℝ) ^ ε := by
        rw [← Real.rpow_mul_natCast hqpos.le]
        congr 1
        ring
      calc
        _ = (4 * D ^ 2) * ((q : ℝ) ^ (1 / 2 : ℝ) *
            ((q : ℝ) ^ (ε / 4)) ^ 4) := by ring
        _ = _ := by rw [hpow, ← Real.rpow_add hqpos]

/-- The fixed exponent required by the existing harmonic range split. -/
theorem standard_completed_prefix_divisor_growth :
    StandardCompletedPrefixDivisorGrowth := by
  obtain ⟨C, hC, threshold, hbound⟩ :=
    completed_prefix_scale_small_power (1 / 28) (by norm_num)
  refine ⟨C, hC.le, threshold, ?_⟩
  intro q hq
  convert hbound q hq using 1
  norm_num

/-- The `q^(1/2+o(1))` conclusion for the actual inverse-residue prefixes,
uniform in numerator and length. Only the completed-prefix estimate is an
input; divisor growth is proved above. -/
theorem completed_inverse_prefix_small_power
    (hcompletion : CompletedInversePrefixEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ q r X,
      threshold ≤ q → 2 ≤ q → r.Coprime q → 1 ≤ X → X ≤ q →
      |inverseResiduePrefix q r X| ≤ C * (q : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨A, hA, hprefix⟩ := hcompletion
  obtain ⟨D, hD, threshold, hscale⟩ := completed_prefix_scale_small_power ε hε
  refine ⟨A * D, mul_nonneg hA hD.le, threshold, ?_⟩
  intro q r X hq hq2 hr hX hXq
  calc
    |inverseResiduePrefix q r X| ≤ A * completedInversePrefixScale q := by
      simpa only [completedInversePrefixScale, mul_assoc] using hprefix q r X hq2 hr hX hXq
    _ ≤ A * (D * (q : ℝ) ^ (1 / 2 + ε)) :=
      mul_le_mul_of_nonneg_left (hscale q hq) hA
    _ = _ := by ring

end NField.Alignment.CompletedPrefixDivisorGrowth
