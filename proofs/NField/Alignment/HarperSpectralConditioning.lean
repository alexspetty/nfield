/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperDirichletParseval
import NField.Alignment.HarperMainConditioning

/-!
# The actual random conditioning reduced to the spectral integral

The proved finite-integral Parseval bound passes through the actual box
weights, including zero-weight boxes. At the manuscript's rounded scales,
the coefficient is exactly (3*x/(2*pi*log(P)))^(3/4). Both the literal and
explicit smoothing remainders are retained. Localization, strengthened
conditioning, and the low-moment saving remain separate obligations.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSpectralConditioning

open MeasureTheory Filter SteinhausMoment HarperDirichletParseval HarperEulerIntegral
  HarperMainIntegral HarperMainConditioning HarperRoughSmoothing HarperSmoothingConditioning
  HarperActualConditioning HarperConditioningFrequencies HarperRoundedCutoff
  HarperSieveScales HarperWeightedConditioning

theorem conditioning_le_spectral {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (P : ℝ) :
    boxConditioning p c1 c2 (smoothInverseIntegral x P y) ≤
      (1/(2*Real.pi))^(3/4 : ℝ) * boxConditioning p c1 c2 (spectralIntegral P (1/2)) := by
  have h := boxConditioning_mono hell c1 c2 (smoothInverseIntegral_integrable hy hyx P)
    ((spectralIntegral_integrable P (by norm_num : (0 : ℝ) < 1/2)).const_mul (1/(2*Real.pi)))
    (smoothInverseIntegral_nonneg hy hyx P) (smoothInverseIntegral_le_spectral hy hyx P)
  rwa [boxConditioning_const_mul hell c1 c2 (by positivity) _
    (spectralIntegral_nonneg P (1/2))] at h

theorem eventual_conditioning_le_spectral : ∀ᶠ p : ℕ in atTop,
    ∀ c1 c2 : Coefficients p,
      boxConditioning p c1 c2
        (smoothInverseIntegral ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1))) ≤
      (1/(2*Real.pi))^(3/4 : ℝ) * boxConditioning p c1 c2
        (spectralIntegral (primeCutoff ((p : ℝ)-1)) (1/2)) := by
  filter_upwards [base_minus_one_tendsto.eventually eventual_cutoff_hierarchy,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hh hell hx
  intro c1 c2
  exact conditioning_le_spectral hell c1 c2 (Real.rpow_pos_of_pos hx _) hh.2.le _

theorem spectral_coefficient {x P : ℝ} (hx : 0 ≤ x) (hP : 0 < Real.log P) :
    (3*x/Real.log P)^(3/4 : ℝ) * (1/(2*Real.pi))^(3/4 : ℝ) =
      (3*x/(2*Real.pi*Real.log P))^(3/4 : ℝ) := by
  rw [← Real.mul_rpow (by positivity : 0 ≤ 3*x/Real.log P) (by positivity)]
  congr 1
  field_simp

theorem eventual_actual_random_spectral_with_error : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      ((3*((p : ℝ)-1)/(2*Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
          (spectralIntegral (primeCutoff ((p : ℝ)-1)) (1/2)) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_main_integral_with_error, eventual_conditioning_le_spectral,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hs hell hx
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have h := hm.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (hs _ _)
      (Real.rpow_nonneg (by positivity) _)) le_rfl) (Real.rpow_nonneg (by norm_num) _))
  rwa [← mul_assoc, spectral_coefficient hx.le hP] at h

theorem eventual_actual_random_spectral : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      ((3*((p : ℝ)-1)/(2*Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
          (spectralIntegral (primeCutoff ((p : ℝ)-1)) (1/2)) +
       (4*((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_main_integral, eventual_conditioning_le_spectral,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hs hell hx
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have h := hm.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (hs _ _)
      (Real.rpow_nonneg (by positivity) _)) le_rfl) (Real.rpow_nonneg (by norm_num) _))
  rwa [← mul_assoc, spectral_coefficient hx.le hP] at h

end NField.Alignment.HarperSpectralConditioning
