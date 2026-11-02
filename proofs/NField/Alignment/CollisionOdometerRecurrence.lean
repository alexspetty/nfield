/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProfiniteOdometerErgodic
import NField.Alignment.CollisionPotentialCutoff
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Quantitative return times for the collision odometer

The least common multiple of the finite periods fixes every finite cutoff.
The actual infinite potential therefore returns at the proved cutoff rate.
Its increment covariance returns to its strictly positive zero-shift value.
The separate Ramanujan formula and negative covariance at shift one are
not asserted in this file.
-/

noncomputable section

namespace NField.Alignment.CollisionOdometerRecurrence

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary CollisionPotentialCutoff
open ProfiniteOdometerErgodic

def cutoffPeriod (M : ℕ) : ℕ := (Finset.Icc 1 M).lcm id

theorem dvd_cutoffPeriod {k M : ℕ} (hk : 1 ≤ k) (hM : k ≤ M) : k ∣ cutoffPeriod M :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk, hM⟩)

theorem centered_periodic {k h : ℕ} (hk : 0 < k) (hh : k ∣ h) (x : Phase) :
    centered k (CollisionPotentialCoboundary.translate (h : ℤ) x) = centered k x := by
  letI : NeZero k := ⟨hk.ne'⟩
  have hz : ((h : ℤ) : ZMod k) = 0 := by
    simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff h k).mpr hh
  rw [centered_eq, centered_eq, residue_translate, hz, zero_add]

theorem remainderVector_periodic {k h : ℕ} (hk : 0 < k) (hh : k ∣ h) :
    shift (h : ℤ) (remainderVector k) = remainderVector k := by
  apply Lp.ext
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (remainderMap k)
  have ht := (translate_measurePreserving (h : ℤ)).quasiMeasurePreserving.ae
    (p := fun x => remainderVector k x = centered k x) hr
  filter_upwards [shift_coe (h : ℤ) (remainderVector k), hr, ht] with x hs hx htx
  change remainderVector k x = centered k x at hx
  rw [hs, htx, centered_periodic hk hh, hx]

theorem finitePotential_periodic (v : ℕ → ℝ) (M : ℕ) :
    shift (cutoffPeriod M : ℤ) (finitePotential v M) = finitePotential v M := by
  simp only [finitePotential, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hb := Finset.mem_Icc.mp hk
  rw [remainderVector_periodic (by omega : 0 < k) (dvd_cutoffPeriod (by omega) hb.2)]

theorem potential_recurrence_norm (M : ℕ) :
    ‖shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential‖ ≤
      2 * ‖collisionPotential - finitePotential collisionWeight M‖ := by
  have he : shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential =
      shift (cutoffPeriod M : ℤ) (collisionPotential - finitePotential collisionWeight M) -
        (collisionPotential - finitePotential collisionWeight M) := by
    rw [map_sub, finitePotential_periodic]
    abel
  rw [he]
  calc
    _ ≤ ‖shift (cutoffPeriod M : ℤ) (collisionPotential - finitePotential collisionWeight M)‖ +
        ‖collisionPotential - finitePotential collisionWeight M‖ := norm_sub_le _ _
    _ = _ := by rw [(shift (cutoffPeriod M : ℤ)).norm_map]; ring

theorem potential_recurrence_bound {M : ℕ} (hM : 1 ≤ M) :
    ‖shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential‖ ≤
      2 * cutoffConstant * (1 + Real.log (2 * (M : ℝ))) / Real.sqrt (M : ℝ) := by
  have h := (potential_recurrence_norm M).trans
    (mul_le_mul_of_nonneg_left (collisionPotential_cutoff_bound hM) (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2 * (cutoffConstant * (1 + Real.log (2 * (M : ℝ))) / Real.sqrt (M : ℝ)) := h
    _ = _ := by ring

theorem potential_recurrence_isBigO :
    (fun M : ℕ => shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential) =O[atTop]
      (fun M : ℕ => Real.log (2 * (M : ℝ)) / Real.sqrt (M : ℝ)) := by
  have h : (fun M : ℕ => shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential)
      =O[atTop] (fun M : ℕ => collisionPotential - finitePotential collisionWeight M) :=
    Asymptotics.IsBigO.of_bound 2 (Filter.Eventually.of_forall potential_recurrence_norm)
  exact h.trans collisionPotential_cutoff_isBigO

theorem potential_recurrence_norm_tendsto_zero :
    Tendsto (fun M => ‖shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential‖)
      atTop (nhds 0) := by
  have ht := ((tendsto_const_nhds (x := collisionPotential)).sub tendsto_collisionPotential).norm
  simp only [sub_self, norm_zero] at ht
  have hb := ht.const_mul 2
  simp only [mul_zero] at hb
  exact squeeze_zero (fun M => norm_nonneg _) potential_recurrence_norm hb

theorem increment_recurrence_norm (M : ℕ) :
    ‖shift (cutoffPeriod M : ℤ) incrementVector - incrementVector‖ ≤
      2 * ‖shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential‖ := by
  have hc (h : ℤ) : shift h (shift (-1) collisionPotential) =
      shift (-1) (shift h collisionPotential) := by
    rw [← shift_add, add_comm h (-1), shift_add]
  have he : shift (cutoffPeriod M : ℤ) incrementVector - incrementVector =
      (shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential) -
        shift (-1) (shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential) := by
    simp only [incrementVector, map_sub, hc]
    abel
  rw [he]
  calc
    _ ≤ ‖shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential‖ +
        ‖shift (-1) (shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential)‖ :=
      norm_sub_le _ _
    _ = _ := by rw [(shift (-1)).norm_map]; ring

theorem increment_recurrence :
    Tendsto (fun M => shift (cutoffPeriod M : ℤ) incrementVector) atTop (nhds incrementVector) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := potential_recurrence_norm_tendsto_zero.const_mul 2
  simp only [mul_zero] at h
  exact squeeze_zero (fun M => norm_nonneg _) increment_recurrence_norm h

def incrementCovariance (h : ℤ) : ℝ := inner ℝ incrementVector (shift h incrementVector)

theorem incrementCovariance_integral (h : ℤ) :
    incrementCovariance h = ∫ x, increment x *
      increment (CollisionPotentialCoboundary.translate h x) ∂phaseHaar := by
  rw [incrementCovariance, L2.inner_def]
  apply integral_congr_ae
  have ht := (translate_measurePreserving h).quasiMeasurePreserving.ae
    (p := fun x => incrementVector x = increment x) incrementVector_coe
  filter_upwards [incrementVector_coe, shift_coe h incrementVector, ht] with x hx hs ht
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hs, ht]
  ring

theorem incrementVector_ne_zero : incrementVector ≠ 0 := by
  intro hz
  have he : collisionPotential - shift (-1) collisionPotential =
      (0 : HaarL2) - shift (-1) 0 := by
    simpa only [incrementVector, map_zero, sub_self] using hz
  have hm : (∫ x, (0 : HaarL2) x ∂phaseHaar) = 0 := by
    rw [← mean_inner_eq_integral, inner_zero_right]
  exact collisionPotential_ne_zero
    (mean_zero_coboundary_unique collisionPotential 0 collisionPotential_mean_zero hm he)

theorem incrementCovariance_zero_pos : 0 < incrementCovariance 0 := by
  rw [incrementCovariance, shift_zero, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr incrementVector_ne_zero)

theorem incrementCovariance_recurrence :
    Tendsto (fun M => incrementCovariance (cutoffPeriod M : ℤ)) atTop
      (nhds (incrementCovariance 0)) := by
  have h := Filter.Tendsto.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := incrementVector)) increment_recurrence
  simpa only [incrementCovariance, shift_zero] using h

end NField.Alignment.CollisionOdometerRecurrence
