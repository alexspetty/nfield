/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Growing
/-! # Fixed windows and the printed unbounded window -/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open Filter Asymptotics
open scoped Topology

theorem constant_growing_window (L : ℕ) : GrowingReturnWindow (fun _ => L) := by
  have ht := Real.tendsto_sqrt_atTop.comp loglog_nat_tendsto
  apply (isLittleO_iff_tendsto' ?_).mpr (ht.const_div_atTop (L : ℝ))
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with p hp
  exact fun hz => False.elim (hp.ne' hz)

def cubicRootWindow (p : ℕ) : ℕ :=
  max 3 ⌊(Real.log (Real.log (p : ℝ)))^(1/3 : ℝ)⌋₊

theorem cubic_root_window_minimum (p : ℕ) : 3 ≤ cubicRootWindow p := le_max_left _ _

theorem cubic_root_window_unbounded : Tendsto cubicRootWindow atTop atTop := by
  have ht : Tendsto (fun p : ℕ => (Real.log (Real.log (p : ℝ)))^(1/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp loglog_nat_tendsto
  exact tendsto_atTop_mono (fun p => le_max_right _ _) (tendsto_nat_floor_atTop.comp ht)

theorem cubic_root_window_growing : GrowingReturnWindow cubicRootWindow := by
  have hY := loglog_nat_tendsto
  have hs := Real.tendsto_sqrt_atTop.comp hY
  have hratio : Tendsto (fun p : ℕ =>
      (3 : ℝ)/Real.sqrt (Real.log (Real.log (p : ℝ)))+
        (Real.log (Real.log (p : ℝ)))^(-1/6 : ℝ)) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/6)).comp hY
    simpa only [Function.comp_apply, neg_div, one_div, add_zero]
      using (hs.const_div_atTop (3 : ℝ)).add hp
  have he : ∀ᶠ p : ℕ in atTop, Real.sqrt (Real.log (Real.log (p : ℝ)))=0 →
      (cubicRootWindow p : ℝ)=0 := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with p hp
    exact fun hz => False.elim (hp.ne' hz)
  apply (isLittleO_iff_tendsto' he).mpr
  apply squeeze_zero' (Eventually.of_forall (fun p => by positivity)) _ hratio
  filter_upwards [hY.eventually (eventually_gt_atTop (0 : ℝ))] with p hp
  have hmax : (cubicRootWindow p : ℝ) ≤ 3+(Real.log (Real.log (p : ℝ)))^(1/3 : ℝ) := by
    unfold cubicRootWindow
    rw [Nat.cast_max, Nat.cast_ofNat]
    apply max_le
    · exact le_add_of_nonneg_right (Real.rpow_nonneg hp.le _)
    · exact (Nat.floor_le (Real.rpow_nonneg hp.le _)).trans (by linarith)
  calc
    _ ≤ (3+(Real.log (Real.log (p : ℝ)))^(1/3 : ℝ))/
        Real.sqrt (Real.log (Real.log (p : ℝ))) :=
      div_le_div_of_nonneg_right hmax (Real.sqrt_nonneg _)
    _ = _ := by
      rw [add_div]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hp]
      norm_num

end NField.ResetForests.ReturnWindows
