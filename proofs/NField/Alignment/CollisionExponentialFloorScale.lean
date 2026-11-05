/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmSharpOrders
import NField.Alignment.CollisionTailCutoffScales

/-!
# The exact exponential-floor scale for lower tails

The floor is retained throughout. Its logarithm differs from the exponent
by at most log(2) eventually, which proves the precise scale needed when
the sharp lcm alignment asymptotic is composed with a growing threshold.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionExponentialFloorScale

open Filter Asymptotics CollisionTailCutoffScales

theorem log_exp_floor_ge {z : ℝ} (hz : 4 ≤ z) :
    z-Real.log 2 ≤ Real.log (⌊Real.exp z⌋₊ : ℝ) := by
  have h := Real.log_le_log (div_pos (Real.exp_pos z) (by norm_num)) (exp_floor_bounds hz).2.1
  rwa [Real.log_div (Real.exp_ne_zero z) (by norm_num : (2 : ℝ) ≠ 0),Real.log_exp] at h

theorem log_exp_floor_error {z : ℝ} (hz : 4 ≤ z) :
    |Real.log (⌊Real.exp z⌋₊ : ℝ)-z| ≤ Real.log 2 := by
  apply abs_le.mpr
  have hl := log_exp_floor_ge hz
  have hu := log_exp_floor_le hz
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  constructor <;> linarith

theorem log_exp_floor_asymptotic :
    (fun z : ℝ => Real.log (⌊Real.exp z⌋₊ : ℝ)) ~[atTop] (fun z : ℝ => z) := by
  have hO : (fun z : ℝ => Real.log (⌊Real.exp z⌋₊ : ℝ)-z) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply isBigO_iff.mpr
    refine ⟨Real.log 2,?_⟩
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with z hz
    simpa only [Real.norm_eq_abs,abs_one,mul_one] using log_exp_floor_error hz
  exact hO.trans_isLittleO (isLittleO_const_id_atTop 1)

theorem tail_exponent_tendsto {d : ℝ} (hd : 0 < d) :
    Tendsto (fun H : ℝ => d*Real.sqrt H) atTop atTop := Real.tendsto_sqrt_atTop.const_mul_atTop hd

theorem tailCutoff_tendsto {d : ℝ} (hd : 0 < d) : Tendsto (tailCutoff d) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp (tail_exponent_tendsto hd))

theorem log_tailCutoff_asymptotic {d : ℝ} (hd : 0 < d) :
    (fun H : ℝ => Real.log (tailCutoff d H)) ~[atTop] (fun H : ℝ => d*Real.sqrt H) :=
  log_exp_floor_asymptotic.comp_tendsto (tail_exponent_tendsto hd)

theorem log_tailCutoff_square_asymptotic {d : ℝ} (hd : 0 < d) :
    (fun H : ℝ => (Real.log (tailCutoff d H))^2) ~[atTop] (fun H : ℝ => d^2*H) := by
  have h := (log_tailCutoff_asymptotic hd).mul (log_tailCutoff_asymptotic hd)
  have hsq : (fun H : ℝ => (Real.log (tailCutoff d H))^2) ~[atTop]
      (fun H : ℝ => (d*Real.sqrt H)^2) := by
    convert! h using 1 <;> funext H <;> dsimp only [Pi.mul_apply] <;> ring
  apply hsq.congr_right
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  rw [mul_pow,Real.sq_sqrt hH]

end NField.Alignment.CollisionExponentialFloorScale
