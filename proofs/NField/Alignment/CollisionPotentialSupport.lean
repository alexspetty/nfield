/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderTailLowerBound
import Mathlib.MeasureTheory.Measure.Support

/-!
# Unbounded support in both directions

The zero-cylinder alignment constants already tend to infinity. The
proved cylinder lower bound therefore makes every stationary tail
positive. Reflection gives the equal tail on the opposite side, and
the actual pushforward measure has support unbounded above and below.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialSupport

open scoped Classical ENNReal
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionPotentialReflection CollisionCylinderMeans CollisionPositionTheorem
open CollisionOdometerRecurrence CollisionCylinderOne CollisionCylinderTailLowerBound

theorem potential_tail_symmetry (H : ℝ) :
    phaseHaar.real {x | H < collisionPotential x}=
      phaseHaar.real {x | collisionPotential x < -H} := by
  have hY := (Lp.aestronglyMeasurable collisionPotential).aemeasurable
  have hNeg : AEMeasurable (fun x => -collisionPotential x) phaseHaar := hY.neg
  have h := congrArg (fun μ : Measure ℝ => μ (Set.Ioi H)) collisionPotential_law_symmetric
  rw [Measure.map_apply_of_aemeasurable hNeg (show MeasurableSet (Set.Ioi H) from measurableSet_Ioi),
    Measure.map_apply_of_aemeasurable hY (show MeasurableSet (Set.Ioi H) from measurableSet_Ioi)] at h
  have he : (fun x => -collisionPotential x) ⁻¹' Set.Ioi H=
      {x | collisionPotential x < -H} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Ioi,Set.mem_setOf_eq]
    constructor <;> intro hx <;> linarith
  rw [he] at h
  exact congrArg ENNReal.toReal h.symm

theorem potential_negative_tail_positive_nonnegative {H : ℝ} (hH : 0 ≤ H) :
    0 < phaseHaar.real {x | collisionPotential x < -H} := by
  have hC : ∀ᶠ M : ℕ in atTop, H < alignmentConstant (cutoffPeriod M) :=
    alignment_cutoff_tendsto_atTop.eventually (eventually_gt_atTop H)
  obtain ⟨M,hCM⟩ := hC.exists
  have hLp : (0 : ℝ) < cutoffPeriod M := by exact_mod_cast cutoffPeriod_pos M
  have hV : 0 < ‖collisionPotential‖^2 :=
    (by norm_num : (0 : ℝ) < 1/144).trans_le collisionPotential_variance_lower
  have hpos : 0 < (alignmentConstant (cutoffPeriod M)-H)^2/
      ((cutoffPeriod M : ℝ)^2*‖collisionPotential‖^2) :=
    div_pos (sq_pos_of_pos (sub_pos.mpr hCM)) (mul_pos (sq_pos_of_pos hLp) hV)
  exact hpos.trans_le (cylinder_tail_lower_bound (cutoffPeriod_pos M) hH hCM)

theorem potential_negative_tail_positive (H : ℝ) :
    0 < phaseHaar.real {x | collisionPotential x < -H} := by
  have hp := potential_negative_tail_positive_nonnegative (H := max H 0) (le_max_right _ _)
  apply hp.trans_le
  refine measureReal_mono ?_ (measure_ne_top phaseHaar _)
  intro x hx
  have ht : H ≤ max H 0 := le_max_left _ _
  change collisionPotential x < -(max H 0) at hx
  change collisionPotential x < -H
  linarith

theorem potential_both_tails_positive (H : ℝ) :
    0 < phaseHaar.real {x | H < collisionPotential x} ∧
      0 < phaseHaar.real {x | collisionPotential x < -H} := by
  rw [potential_tail_symmetry]
  exact ⟨potential_negative_tail_positive H,potential_negative_tail_positive H⟩

theorem potential_law_tails_positive (H : ℝ) :
    0 < (Measure.map collisionPotential phaseHaar).real (Set.Ioi H) ∧
      0 < (Measure.map collisionPotential phaseHaar).real (Set.Iio H) := by
  have hY := (Lp.aestronglyMeasurable collisionPotential).aemeasurable
  simp only [Measure.real,Measure.map_apply_of_aemeasurable hY measurableSet_Ioi,
    Measure.map_apply_of_aemeasurable hY measurableSet_Iio]
  exact ⟨(potential_both_tails_positive H).1,by
    simpa only [neg_neg,Measure.real,Set.preimage,Set.mem_Iio] using potential_negative_tail_positive (-H)⟩

theorem potential_support_unbounded :
    ¬ BddAbove (Measure.map collisionPotential phaseHaar).support ∧
      ¬ BddBelow (Measure.map collisionPotential phaseHaar).support := by
  constructor
  · rintro ⟨H,hH⟩
    have hsub : Set.Ioi H ⊆ (Measure.map collisionPotential phaseHaar).supportᶜ := by
      intro x hx hs
      exact (not_lt_of_ge (hH hs)) hx
    have hz : (Measure.map collisionPotential phaseHaar) (Set.Ioi H)=0 :=
      le_antisymm ((measure_mono hsub).trans_eq Measure.measure_compl_support) bot_le
    have hp := (potential_law_tails_positive H).1
    simp only [Measure.real,hz,ENNReal.toReal_zero,lt_self_iff_false] at hp
  · rintro ⟨H,hH⟩
    have hsub : Set.Iio H ⊆ (Measure.map collisionPotential phaseHaar).supportᶜ := by
      intro x hx hs
      exact (not_lt_of_ge (hH hs)) hx
    have hz : (Measure.map collisionPotential phaseHaar) (Set.Iio H)=0 :=
      le_antisymm ((measure_mono hsub).trans_eq Measure.measure_compl_support) bot_le
    have hp := (potential_law_tails_positive H).2
    simp only [Measure.real,hz,ENNReal.toReal_zero,lt_self_iff_false] at hp

end NField.Alignment.CollisionPotentialSupport
