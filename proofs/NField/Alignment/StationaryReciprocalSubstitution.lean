/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryDiscreteTailComparison
import NField.Alignment.StationaryCenteringTail

/-! # Exact reciprocal substitution in the smooth diagonal tail -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryReciprocalSubstitution
open MeasureTheory Set StationaryDiagonalDefinitions StationaryWeightConstants
  StationaryDiscreteTailComparison StationaryCenteringDefinitions StationaryCenteringTail
  StationaryCumulativeWeight

/-- Title: `Reciprocal substitution converts the smooth tail to the actual centering integrals`. -/
theorem smooth_tail_eq_truncatedCentering {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n) :
    (2 / 3 : ℝ) * (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t)) =
      truncatedCentering n ((n : ℝ) / M) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hnR : (0 : ℝ) < n := hMR.trans_le hMnR
  let g : ℝ → ℝ := fun u => ((alpha * Real.log n + beta - alpha * Real.log u) / u) * psi u
  have hpos {t : ℝ} (ht : t ∈ uIcc (M : ℝ) n) : 0 < t := by
    rw [uIcc_of_le hMnR] at ht
    exact hMR.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => (n : ℝ) / t) (uIcc (M : ℝ) n) :=
    continuousOn_const.div continuousOn_id (fun t ht => (hpos ht).ne')
  have hd {t : ℝ} (ht : t ∈ uIcc (M : ℝ) n) :
      HasDerivAt (fun t : ℝ => (n : ℝ) / t) (-(n : ℝ) / t ^ 2) t := by
    convert! (hasDerivAt_const t (n : ℝ)).div (hasDerivAt_id t) (hpos ht).ne' using 1
    simp only [id_eq]
    ring
  have hh := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := g) hc
    (fun t ht => hd (by rw [uIcc_of_le hMnR]; simpa only [min_eq_left hMnR, max_eq_right hMnR] using Ioo_subset_Icc_self ht))
    (fun t ht => by apply div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg t))
  have he : (∫ t in (M : ℝ)..n, (g ∘ fun t : ℝ => (n : ℝ) / t) t * (-(n : ℝ) / t ^ 2)) =
      -(∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 := hpos ht
    dsimp only [Function.comp_apply, g]
    rw [Real.log_div hnR.ne' ht0.ne']
    unfold mainDensity
    field_simp
    ring
  rw [he, div_self hnR.ne'] at hh
  have hr : (∫ u in (n : ℝ) / M..1, g u) = -(∫ u in 1..((n : ℝ) / M), g u) :=
    intervalIntegral.integral_symm 1 ((n : ℝ) / M)
  rw [hr] at hh
  unfold truncatedCentering
  exact congrArg (fun r : ℝ => (2 / 3 : ℝ) * r) (neg_injective hh)

/-- Title: `The smooth tail has the manuscript's logarithmic centering with a uniform endpoint error`. -/
theorem smooth_tail_centering_error {M n : ℕ} (hM : 1 ≤ M) (hMn : M ≤ n) :
    |(2 / 3 : ℝ) * (∫ t in (M : ℝ)..n, mainDensity t * psi ((n : ℝ) / t)) -
        (biasCoefficient * Real.log n + biasConstant)| ≤
      2 * centeringErrorConstant * M * Real.log (2 * (n : ℝ)) / n := by
  have hM0 : 0 < M := hM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hnR : (0 : ℝ) < n := by linarith
  have hMR0 : (0 : ℝ) < M := by linarith
  have ha : (1 : ℝ) ≤ (n : ℝ) / M := (le_div_iff₀ hMR0).mpr (by simpa using hMnR)
  have han : (n : ℝ) / M ≤ n := div_le_self hnR.le hMR
  have hc : 0 ≤ centeringErrorConstant := by unfold centeringErrorConstant; positivity
  rw [smooth_tail_eq_truncatedCentering hM0 hMn]
  calc
    _ ≤ centeringErrorConstant * (1 + Real.log n) / ((n : ℝ) / M) :=
      truncatedCentering_uniform_error ha han
    _ = centeringErrorConstant * M * (1 + Real.log n) / n := by field_simp
    _ ≤ centeringErrorConstant * M * (2 * Real.log (2 * (n : ℝ))) / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      exact mul_le_mul_of_nonneg_left (one_add_log_le_two_log_two_mul (hMR.trans hMnR)) (by positivity)
    _ = _ := by ring

end NField.Alignment.StationaryReciprocalSubstitution
