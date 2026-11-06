/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryReciprocalKernels

/-! # Exact shifted logarithmic cubic tails for the Bernoulli boundary error -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryCubicKernels
open MeasureTheory Set Filter CollisionLogTailKernel

def inverseCube (x : ℝ) : ℝ := 1 / x ^ 3
def logRatioCube (a x : ℝ) : ℝ := Real.log (x / a) / x ^ 3
def logRatioPrimitive (a x : ℝ) : ℝ := -(2 * Real.log (x / a) + 1) / (4 * x ^ 2)

theorem inverseSquare_tendsto : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (nhds 0) := by
  have hh := (tendsto_const_nhds.div_atTop tendsto_id :
    Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0)).pow 2
  simpa only [div_pow, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hh

theorem log_div_square_tendsto : Tendsto (fun x : ℝ => Real.log x / x ^ 2) atTop (nhds 0) := by
  have hh := (logPower_div_linear_tendsto 1).div_atTop tendsto_id
  simpa only [pow_one, div_div, pow_two, id_eq] using hh

theorem inverseCube_primitive_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => -1 / (2 * x ^ 2)) (inverseCube x) x := by
  have hh := (hasDerivAt_const x (-1 : ℝ)).div
    (((hasDerivAt_id x).pow 2).const_mul 2) (by
      simpa only [Pi.pow_apply, id_eq] using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hx))
  convert! hh using 1
  unfold inverseCube
  simp only [Pi.pow_apply, id_eq]
  field_simp
  ring

theorem inverseCube_primitive_tendsto :
    Tendsto (fun x : ℝ => -1 / (2 * x ^ 2)) atTop (nhds 0) := by
  convert! inverseSquare_tendsto.const_mul (-1 / 2 : ℝ) using 1
  · funext x
    ring
  · ring

theorem inverseCube_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn inverseCube (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => inverseCube_primitive_hasDerivAt (ne_of_gt (ha.trans_le hx)))
    (fun x hx => by have hx0 : 0 < x := ha.trans hx; unfold inverseCube; positivity)
    inverseCube_primitive_tendsto

theorem inverseCube_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi a, inverseCube x) = 1 / (2 * a ^ 2) := by
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => inverseCube_primitive_hasDerivAt (ne_of_gt (ha.trans_le hx)))
    (fun x hx => by have hx0 : 0 < x := ha.trans hx; unfold inverseCube; positivity)
    inverseCube_primitive_tendsto
  convert! hh using 1
  ring

theorem logRatioPrimitive_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (logRatioPrimitive a) (logRatioCube a x) x := by
  have hl := (Real.hasDerivAt_log (div_ne_zero hx.ne' ha.ne')).comp x
    ((hasDerivAt_id x).div_const a)
  have hh := (((hl.const_mul 2).add_const 1).neg).div
    (((hasDerivAt_id x).pow 2).const_mul 4) (by
      simpa only [Pi.pow_apply, id_eq] using mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 hx.ne'))
  convert! hh using 1
  unfold logRatioCube
  simp only [id_eq, Pi.neg_apply, Pi.pow_apply, Function.comp_apply]
  field_simp
  ring

theorem logRatioPrimitive_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (logRatioPrimitive a) atTop (nhds 0) := by
  have hh := (log_div_square_tendsto.const_mul (-1 / 2 : ℝ)).add
    (inverseSquare_tendsto.const_mul ((2 * Real.log a - 1) / 4))
  simp only [mul_zero, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold logRatioPrimitive
  rw [Real.log_div hx.ne' ha.ne']
  ring

theorem logRatioCube_nonneg {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) : 0 ≤ logRatioCube a x := by
  have hx : 0 < x := ha.trans_le hax
  unfold logRatioCube
  exact div_nonneg (Real.log_nonneg ((le_div_iff₀ ha).mpr (by simpa using hax))) (by positivity)

theorem logRatioCube_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn (logRatioCube a) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => logRatioPrimitive_hasDerivAt ha (ha.trans_le hx))
    (fun x hx => logRatioCube_nonneg ha hx.le)
    (logRatioPrimitive_tendsto ha)

/-- Title: `The shifted logarithmic cubic tail has its exact inverse-square integral`. -/
theorem logRatioCube_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi a, logRatioCube a x) = 1 / (4 * a ^ 2) := by
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => logRatioPrimitive_hasDerivAt ha (ha.trans_le hx))
    (fun x hx => logRatioCube_nonneg ha hx.le)
    (logRatioPrimitive_tendsto ha)
  simpa only [logRatioPrimitive, div_self ha.ne', Real.log_one, mul_zero, zero_add,
    zero_sub, neg_div, neg_neg] using hh

end NField.Alignment.StationaryCubicKernels
