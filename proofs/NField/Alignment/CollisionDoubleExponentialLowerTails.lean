/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDoubleExponentialComparison
import NField.Alignment.CollisionPotentialSupport

/-!
# The sharp double-exponential stationary lower tail

The actual lcm cylinder has conditional mean below minus H by at least
one. Its probability lower bound is controlled by the sharp attained
alignment coefficient and the unconditional logarithmic lcm asymptotic.
The strict gap between cutoff exponents absorbs the second moment.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDoubleExponentialLowerTails

open Filter MeasureTheory
open CollisionDoubleExponentialComparison CollisionLowerTailCutoffAlignment
open CollisionTailCutoffScales CollisionLimitingPrimeProduct CollisionCylinderMeans
open CollisionOdometerRecurrence CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionCylinderTailLowerBound CollisionPotentialSupport ProfiniteRemainderMeasure
open CollisionCylinderOne

theorem stationary_negative_tail_lower {d : ℝ} (hd : 1/Real.sqrt alignmentGamma < d) :
    ∀ᶠ H : ℝ in atTop, Real.exp (-Real.exp (d*Real.sqrt H)) ≤
      phaseHaar.real {x | collisionPotential x < -H} := by
  obtain ⟨d0,hd0,hgap⟩ := exists_between hd
  have hd0pos : 0 < d0 := (alignment_scale_coefficient_gt_one hd0).1
  have hV : 0 < ‖collisionPotential‖^2 :=
    (by norm_num : (0 : ℝ) < 1/144).trans_le collisionPotential_variance_lower
  filter_upwards [cutoff_alignment_excess hd0,lower_tail_modulus_log_bound hd0pos,
    exponential_scale_domination hd0pos hgap (Real.log (‖collisionPotential‖^2)),
    eventually_ge_atTop (0 : ℝ)] with H hC hL hscale hH
  let L := cutoffPeriod (tailCutoff d0 H)
  have hLpos : 0 < L := cutoffPeriod_pos _
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hLpos
  have hexcess : 1 ≤ alignmentConstant L-H := by dsimp only [L]; linarith
  have hHC : H < alignmentConstant L := by linarith
  have hlog : 2*Real.log (L : ℝ)+Real.log (‖collisionPotential‖^2) ≤
      Real.exp (d*Real.sqrt H) := by dsimp only [L]; linarith
  calc
    _ ≤ 1/((L : ℝ)^2*‖collisionPotential‖^2) :=
      double_exponential_below_reciprocal hLpos hV hlog
    _ ≤ (alignmentConstant L-H)^2/((L : ℝ)^2*‖collisionPotential‖^2) := by
      apply div_le_div_of_nonneg_right _ (mul_pos (sq_pos_of_pos hLR) hV).le
      nlinarith
    _ ≤ _ := cylinder_tail_lower_bound hLpos hH hHC

theorem stationary_double_exponential_lower_tails {d : ℝ}
    (hd : 1/Real.sqrt alignmentGamma < d) :
    ∀ᶠ H : ℝ in atTop,
      phaseHaar.real {x | H < collisionPotential x}=
        phaseHaar.real {x | collisionPotential x < -H} ∧
      Real.exp (-Real.exp (d*Real.sqrt H)) ≤
        phaseHaar.real {x | collisionPotential x < -H} := by
  filter_upwards [stationary_negative_tail_lower hd] with H hH
  exact ⟨potential_tail_symmetry H,hH⟩

end NField.Alignment.CollisionDoubleExponentialLowerTails
