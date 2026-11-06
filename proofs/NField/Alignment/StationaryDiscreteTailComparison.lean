/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationarySmoothTailFunctional
import NField.Alignment.StationaryTailFunctionalBound
import NField.Alignment.StationaryCumulativeWeight

/-! # Uniform discrete-to-smooth comparison with all reciprocal jumps retained -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryDiscreteTailComparison
open scoped BigOperators
open MeasureTheory Set StationaryDiagonalDefinitions StationaryWeightConstants
  StationaryCumulativeWeight StationaryReciprocalAbel StationaryTailFunctional
  StationarySmoothTailFunctional StationaryTailFunctionalBound

def mainDensity (t : ℝ) : ℝ := (alpha * Real.log t + beta) / t

theorem cumulativeMain_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt cumulativeMain (mainDensity t) t := by
  have hl := Real.hasDerivAt_log ht
  have hh := ((((hl.pow 2).const_mul alpha).div_const 2).add (hl.const_mul beta)).add_const constantWeight
  convert! hh using 1
  unfold mainDensity
  ring

theorem cumulativeMain_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn cumulativeMain (Icc a b) := by
  intro t ht
  exact (cumulativeMain_hasDerivAt (ne_of_gt (ha.trans_le ht.1))).continuousAt.continuousWithinAt

theorem mainDensity_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn mainDensity (Icc a b) := by
  have hne : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => ne_of_gt (ha.trans_le ht.1)
  exact ((continuousOn_const.mul (continuousOn_id.log hne)).add continuousOn_const).div
    continuousOn_id hne

theorem cumulativeWeight_reciprocal_integrable {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n) :
    IntervalIntegrable (fun t => cumulativeWeight t / t ^ 2) volume (M : ℝ) n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hc : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Icc (M : ℝ) n) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (hMR.trans_le ht.1)))
  have hh := integrableOn_mul_sum_Icc (m := 0) coefficient hMR.le
    (hc.integrableOn_Icc : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Icc (M : ℝ) n) volume)
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hMnR] at hh
  have he : (fun t : ℝ => (1 / t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, coefficient k) =
      (fun t : ℝ => cumulativeWeight t / t ^ 2) := by
    funext t
    change (1 / t ^ 2) * summatory coefficient t = _
    rw [coefficient_summatory]
    ring
  exact he ▸ hh

theorem cumulativeMain_reciprocal_integrable {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n) :
    IntervalIntegrable (fun t => cumulativeMain t / t ^ 2) volume (M : ℝ) n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hMnR]
  exact (cumulativeMain_continuousOn hMR).div (continuousOn_id.pow 2)
    (fun t ht => pow_ne_zero 2 (ne_of_gt (hMR.trans_le ht.1)))

theorem cumulative_remainder_uniform {M n : ℕ} (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (M : ℝ) n) :
    |cumulativeWeight t - cumulativeMain t| ≤
      weightErrorConstant * Real.log (2 * (n : ℝ)) ^ 2 / M := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have ht2 : 2 ≤ t := hMR.trans ht.1
  have hMR0 : (0 : ℝ) < M := by linarith
  have ht0 : 0 < t := by linarith
  have hlog : Real.log (2 * t) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith [ht.2])
  have hs : Real.log (2 * t) ^ 2 ≤ Real.log (2 * (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 2
  calc
    _ ≤ weightErrorConstant * Real.log (2 * t) ^ 2 / t := precise_cumulative_weight ht2
    _ ≤ weightErrorConstant * Real.log (2 * (n : ℝ)) ^ 2 / t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs weightErrorConstant_pos.le) ht0.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity [weightErrorConstant_pos]) hMR0 ht.1

/-- Title: `The discrete sawtooth tail differs from its smooth integral by the exact uniform scale`. -/
theorem discrete_smooth_tail_error {M n : ℕ} (hM : 2 ≤ M) (hMn : M ≤ n) :
    |(∑ k ∈ Finset.Ioc M n, coefficient k * psi ((n : ℝ) / k)) -
      (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t))| ≤
        3 * weightErrorConstant * n * Real.log (2 * (n : ℝ)) ^ 2 / M ^ 2 := by
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hiW := cumulativeWeight_reciprocal_integrable hM0 hMn
  have hiA := cumulativeMain_reciprocal_integrable hM0 hMn
  have hiE : IntervalIntegrable (fun t => (cumulativeWeight t - cumulativeMain t) / t ^ 2)
      volume (M : ℝ) n := by
    simpa only [sub_div] using hiW.sub hiA
  rw [coefficient_tail_functional hM0 hMn,
    smooth_psi_tail_functional hM0 hMn
      (fun t ht => cumulativeMain_hasDerivAt (ne_of_gt (hMR.trans_le ht.1)))
      (mainDensity_continuousOn hMR), ← tailFunctional_sub hiW hiA]
  have hh := tailFunctional_uniform_bound hM0 hMn
    (show 0 ≤ weightErrorConstant * Real.log (2 * (n : ℝ)) ^ 2 / M by positivity [weightErrorConstant_pos])
    hiE (fun t ht => cumulative_remainder_uniform hM ht)
  convert! hh using 1
  ring

end NField.Alignment.StationaryDiscreteTailComparison
