/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryCubicKernels
import NField.Alignment.StationaryConditionalConstants

/-! # Shifted endpoint kernels retain the logarithm of the cutoff -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryBoundaryKernel
open MeasureTheory Set Filter StationaryBernoulliPrimitive StationaryConditionalConstants
  StationaryCubicKernels

def boundaryKernel (A C a x : ℝ) : ℝ := (C + A - A * Real.log (x / a)) / x ^ 2
def boundaryKernelDeriv (A C a x : ℝ) : ℝ := (-2 * C - 3 * A + 2 * A * Real.log (x / a)) / x ^ 3
def boundaryMajorant (A C a x : ℝ) : ℝ :=
  (2 * |C| + 3 * |A|) * inverseCube x + 2 * |A| * logRatioCube a x
def boundaryRemainder (A C a : ℝ) : ℝ := ∫ x in Ioi a, firstPrimitive x * boundaryKernel A C a x

theorem boundaryKernel_hasDerivAt (A C : ℝ) {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (boundaryKernel A C a) (boundaryKernelDeriv A C a x) x := by
  have hl := (Real.hasDerivAt_log (div_ne_zero hx.ne' ha.ne')).comp x
    ((hasDerivAt_id x).div_const a)
  have hh := ((hasDerivAt_const x (C + A)).sub (hl.const_mul A)).div
    ((hasDerivAt_id x).pow 2) (by
      simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 2 hx.ne')
  convert! hh using 1
  unfold boundaryKernelDeriv
  simp only [id_eq, Pi.pow_apply, Pi.sub_apply, Function.comp_apply]
  field_simp
  ring

theorem boundaryKernel_tendsto (A C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (boundaryKernel A C a) atTop (nhds 0) := by
  have hh := (inverseSquare_tendsto.const_mul (C + A + A * Real.log a)).sub
    (log_div_square_tendsto.const_mul A)
  simp only [mul_zero, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold boundaryKernel
  rw [Real.log_div hx.ne' ha.ne']
  ring

theorem firstPrimitive_boundaryKernel_split (A C : ℝ) {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    firstPrimitive x * boundaryKernel A C a x =
      (C + A * Real.log a) * firstKernel x - A * secondKernel x := by
  unfold boundaryKernel firstKernel secondKernel
  rw [Real.log_div hx.ne' ha.ne']
  ring

theorem firstPrimitive_boundaryKernel_integrable (A C : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun x => firstPrimitive x * boundaryKernel A C a x) (Ioi a) := by
  have ha0 : 0 < a := by linarith
  apply (((firstKernel_integrable ha0).const_mul (C + A * Real.log a)).sub
    ((secondKernel_integrable ha).const_mul A)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (firstPrimitive_boundaryKernel_split A C ha0 (ha0.trans hx)).symm

theorem boundaryRemainder_split (A C : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    boundaryRemainder A C a = (C + A * Real.log a) * (∫ x in Ioi a, firstKernel x) -
      A * (∫ x in Ioi a, secondKernel x) := by
  have ha0 : 0 < a := by linarith
  unfold boundaryRemainder
  have he : (∫ x in Ioi a, firstPrimitive x * boundaryKernel A C a x) =
      ∫ x in Ioi a, (C + A * Real.log a) * firstKernel x - A * secondKernel x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact firstPrimitive_boundaryKernel_split A C ha0 (ha0.trans hx)
  rw [he, integral_sub ((firstKernel_integrable ha0).const_mul _)
    ((secondKernel_integrable ha).const_mul _), integral_const_mul, integral_const_mul]

theorem boundaryKernelDeriv_norm_bound (A C : ℝ) {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    ‖boundaryKernelDeriv A C a x‖ ≤ boundaryMajorant A C a x := by
  have hx : 0 < x := ha.trans_le hax
  have hl : 0 ≤ Real.log (x / a) := Real.log_nonneg ((le_div_iff₀ ha).mpr (by simpa using hax))
  have habs : |-2 * C - 3 * A + 2 * A * Real.log (x / a)| ≤
      2 * |C| + 3 * |A| + 2 * |A| * Real.log (x / a) := by
    calc
      _ ≤ |-2 * C - 3 * A| + |2 * A * Real.log (x / a)| := abs_add_le _ _
      _ ≤ (|-2 * C| + |3 * A|) + |2 * A * Real.log (x / a)| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = _ := by simp only [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg hl]
  rw [Real.norm_eq_abs, boundaryKernelDeriv, abs_div, abs_of_pos (pow_pos hx 3)]
  calc
    _ ≤ (2 * |C| + 3 * |A| + 2 * |A| * Real.log (x / a)) / x ^ 3 :=
      div_le_div_of_nonneg_right habs (by positivity)
    _ = _ := by unfold boundaryMajorant inverseCube logRatioCube; ring

theorem boundaryMajorant_integrable (A C : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (boundaryMajorant A C a) (Ioi a) :=
  ((inverseCube_integrable ha).const_mul _).add ((logRatioCube_integrable ha).const_mul _)

theorem secondPrimitive_boundaryKernelDeriv_norm_bound (A C : ℝ) {a x : ℝ}
    (ha : 0 < a) (hax : a ≤ x) :
    ‖boundaryKernelDeriv A C a x * secondPrimitive x‖ ≤ boundaryMajorant A C a x := by
  rw [norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ ‖boundaryKernelDeriv A C a x‖ * 1 :=
      mul_le_mul_of_nonneg_left (secondPrimitive_abs_bound x) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using boundaryKernelDeriv_norm_bound A C ha hax

theorem secondPrimitive_boundaryKernelDeriv_integrable (A C : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => boundaryKernelDeriv A C a x * secondPrimitive x) (Ioi a) := by
  have hm : Measurable (fun x => boundaryKernelDeriv A C a x * secondPrimitive x) := by
    have hd : Measurable (boundaryKernelDeriv A C a) := by
      unfold boundaryKernelDeriv
      fun_prop
    exact hd.mul secondPrimitive_continuous.measurable
  apply (boundaryMajorant_integrable A C ha).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact secondPrimitive_boundaryKernelDeriv_norm_bound A C ha hx.le

theorem boundaryMajorant_integral (A C : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi a, boundaryMajorant A C a x) = (|C| + 2 * |A|) / a ^ 2 := by
  unfold boundaryMajorant
  rw [integral_add ((inverseCube_integrable ha).const_mul _)
    ((logRatioCube_integrable ha).const_mul _), integral_const_mul, integral_const_mul,
    inverseCube_integral ha, logRatioCube_integral ha]
  ring

theorem boundaryDerivative_integral_bound (A C : ℝ) {a : ℝ} (ha : 0 < a) :
    |∫ x in Ioi a, boundaryKernelDeriv A C a x * secondPrimitive x| ≤ (|C| + 2 * |A|) / a ^ 2 := by
  calc
    _ ≤ ∫ x in Ioi a, ‖boundaryKernelDeriv A C a x * secondPrimitive x‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => boundaryKernelDeriv A C a x * secondPrimitive x) (μ := volume.restrict (Ioi a))
    _ ≤ ∫ x in Ioi a, boundaryMajorant A C a x := by
      apply integral_mono_ae (secondPrimitive_boundaryKernelDeriv_integrable A C ha).norm
        (boundaryMajorant_integrable A C ha)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact secondPrimitive_boundaryKernelDeriv_norm_bound A C ha hx.le
    _ = _ := boundaryMajorant_integral A C ha

end NField.Alignment.StationaryBoundaryKernel
