/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationarySawtoothIntegrals
import NField.Alignment.StationaryReciprocalKernels

/-! # Conditional improper integrals defined through absolutely convergent Bernoulli remainders -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryConditionalConstants
open MeasureTheory Set Filter StationaryDiagonalDefinitions StationaryBernoulliPrimitive
  StationarySawtoothIntegrals StationaryReciprocalKernels CollisionLogTailKernel

def firstKernel (x : ℝ) : ℝ := firstPrimitive x / x ^ 2
def secondKernel (x : ℝ) : ℝ := firstPrimitive x * (Real.log x - 1) / x ^ 2
/-- The conditional integral is represented by its absolutely convergent integration-by-parts remainder. -/
def integralZero : ℝ := -1 / 12 + ∫ x in Ioi 1, firstKernel x
/-- This is the conditional logarithmic integral, not a Bochner integral of its nonabsolute integrand. -/
def integralOne : ℝ := ∫ x in Ioi 1, secondKernel x

theorem firstKernel_norm_bound (x : ℝ) : ‖firstKernel x‖ ≤ (1 / 12 : ℝ) * inverseSquare x := by
  rw [Real.norm_eq_abs, firstKernel, abs_div, abs_of_nonneg (sq_nonneg x)]
  calc
    _ ≤ (1 / 12 : ℝ) / x ^ 2 := div_le_div_of_nonneg_right (firstPrimitive_abs_bound x) (sq_nonneg x)
    _ = _ := by unfold inverseSquare; ring

theorem secondKernel_norm_bound {x : ℝ} (hx : 1 ≤ x) :
    ‖secondKernel x‖ ≤ (1 / 12 : ℝ) * logarithmicSquare x := by
  have hl := Real.log_nonneg hx
  have hd : |Real.log x - 1| ≤ 1 + Real.log x := by
    have h := abs_sub (Real.log x) 1
    rw [abs_of_nonneg hl, abs_one] at h
    linarith
  rw [Real.norm_eq_abs, secondKernel, abs_div, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc
    _ ≤ ((1 / 12 : ℝ) * (1 + Real.log x)) / x ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul (firstPrimitive_abs_bound x) hd (abs_nonneg _) (by norm_num)) (sq_nonneg x)
    _ = _ := by unfold logarithmicSquare; ring

theorem firstKernel_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn firstKernel (Ioi a) := by
  apply ((inverseSquare_integrable ha).const_mul (1 / 12 : ℝ)).mono'
  · exact (firstPrimitive_continuous.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable
  · exact Eventually.of_forall firstKernel_norm_bound

theorem secondKernel_integrable {a : ℝ} (ha : 1 ≤ a) : IntegrableOn secondKernel (Ioi a) := by
  apply ((logarithmicSquare_integrable ha).const_mul (1 / 12 : ℝ)).mono'
  · exact ((firstPrimitive_continuous.measurable.mul (Real.measurable_log.sub measurable_const)).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact secondKernel_norm_bound (ha.trans hx.le)

theorem firstKernel_integral_bound {a : ℝ} (ha : 0 < a) :
    |∫ x in Ioi a, firstKernel x| ≤ 1 / (12 * a) := by
  calc
    _ ≤ ∫ x in Ioi a, ‖firstKernel x‖ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (firstKernel) (μ := volume.restrict (Ioi a))
    _ ≤ ∫ x in Ioi a, (1 / 12 : ℝ) * inverseSquare x :=
      integral_mono ((firstKernel_integrable ha).norm) ((inverseSquare_integrable ha).const_mul _) firstKernel_norm_bound
    _ = _ := by rw [integral_const_mul, inverseSquare_integral ha]; ring

theorem secondKernel_integral_bound {a : ℝ} (ha : 1 ≤ a) :
    |∫ x in Ioi a, secondKernel x| ≤ (Real.log a + 2) / (12 * a) := by
  calc
    _ ≤ ∫ x in Ioi a, ‖secondKernel x‖ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (secondKernel) (μ := volume.restrict (Ioi a))
    _ ≤ ∫ x in Ioi a, (1 / 12 : ℝ) * logarithmicSquare x := by
      apply integral_mono_ae ((secondKernel_integrable ha).norm) ((logarithmicSquare_integrable ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact secondKernel_norm_bound (ha.trans hx.le)
    _ = _ := by rw [integral_const_mul, logarithmicSquare_integral ha]; ring

theorem integralZero_remainder {a : ℝ} (ha : 1 ≤ a) :
    integralZero - (∫ x in 1..a, psi x / x) =
      -firstPrimitive a / a + ∫ x in Ioi a, firstKernel x := by
  rw [reciprocal_psi_integral (by norm_num) ha]
  have hs := intervalIntegral.integral_Ioi_sub_Ioi (firstKernel_integrable (by norm_num : (0 : ℝ) < 1)) ha
  unfold integralZero
  have hB : firstPrimitive 1 = 1 / 12 := by simpa using firstPrimitive_integer 1
  rw [hB, div_one]
  change (∫ x in Ioi 1, firstKernel x) - (∫ x in Ioi a, firstKernel x) =
    ∫ x in 1..a, firstPrimitive x / x ^ 2 at hs
  rw [← hs]
  ring

theorem integralOne_remainder {a : ℝ} (ha : 1 ≤ a) :
    integralOne - (∫ x in 1..a, psi x * Real.log x / x) =
      -firstPrimitive a * Real.log a / a + ∫ x in Ioi a, secondKernel x := by
  rw [logarithmic_psi_integral (by norm_num) ha]
  have hs := intervalIntegral.integral_Ioi_sub_Ioi (secondKernel_integrable (by norm_num : (1 : ℝ) ≤ 1)) ha
  unfold integralOne
  simp only [Real.log_one, mul_zero, zero_div, sub_zero]
  change (∫ x in Ioi 1, secondKernel x) - (∫ x in Ioi a, secondKernel x) =
    ∫ x in 1..a, firstPrimitive x * (Real.log x - 1) / x ^ 2 at hs
  rw [← hs]
  ring

/-- Title: `The conditional reciprocal sawtooth integral has an inverse-linear tail`. -/
theorem integralZero_tail_bound {a : ℝ} (ha : 1 ≤ a) :
    |integralZero - (∫ x in 1..a, psi x / x)| ≤ 1 / (6 * a) := by
  have ha0 : 0 < a := by linarith
  rw [integralZero_remainder ha]
  calc
    _ ≤ |-firstPrimitive a / a| + |∫ x in Ioi a, firstKernel x| := abs_add_le _ _
    _ ≤ (1 / 12 : ℝ) / a + 1 / (12 * a) := by
      apply add_le_add _ (firstKernel_integral_bound ha0)
      rw [abs_div, abs_neg, abs_of_pos ha0]
      exact div_le_div_of_nonneg_right (firstPrimitive_abs_bound a) ha0.le
    _ = _ := by ring

/-- Title: `The conditional logarithmic sawtooth integral has its logarithmic inverse-linear tail`. -/
theorem integralOne_tail_bound {a : ℝ} (ha : 1 ≤ a) :
    |integralOne - (∫ x in 1..a, psi x * Real.log x / x)| ≤ (1 + Real.log a) / (6 * a) := by
  have ha0 : 0 < a := by linarith
  have hl := Real.log_nonneg ha
  rw [integralOne_remainder ha]
  calc
    _ ≤ |-firstPrimitive a * Real.log a / a| + |∫ x in Ioi a, secondKernel x| := abs_add_le _ _
    _ ≤ (1 / 12 : ℝ) * Real.log a / a + (Real.log a + 2) / (12 * a) := by
      apply add_le_add _ (secondKernel_integral_bound ha)
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hl, abs_of_pos ha0]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (firstPrimitive_abs_bound a) hl) ha0.le
    _ = _ := by ring

/-- Title: `The first source improper integral converges as a limit of finite integrals`. -/
theorem integralZero_tendsto : Tendsto (fun a : ℝ => ∫ x in 1..a, psi x / x) atTop (nhds integralZero) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have ht : Tendsto (fun a : ℝ => 1 / (6 * a)) atTop (nhds 0) := by
    simpa [div_mul_eq_div_div] using
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun a : ℝ => (1 / 6 : ℝ) / a) atTop (nhds 0))
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  simpa only [abs_sub_comm] using integralZero_tail_bound ha

/-- Title: `The logarithmic source improper integral converges as a limit of finite integrals`. -/
theorem integralOne_tendsto : Tendsto (fun a : ℝ => ∫ x in 1..a, psi x * Real.log x / x) atTop (nhds integralOne) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have ht : Tendsto (fun a : ℝ => (1 + Real.log a) / (6 * a)) atTop (nhds 0) := by
    have hh := ((tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun a : ℝ => 1 / a) atTop (nhds 0)).add
      (logPower_div_linear_tendsto 1)).const_mul (1 / 6 : ℝ)
    norm_num only [zero_add, mul_zero] at hh
    convert! hh using 1
    funext a
    simp only [pow_one]
    ring
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  simpa only [abs_sub_comm] using integralOne_tail_bound ha

end NField.Alignment.StationaryConditionalConstants
