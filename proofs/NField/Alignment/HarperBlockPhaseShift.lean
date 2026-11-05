/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGoodEventUnion
import NField.Alignment.HarperPhaseShift

/-!
# Frequency shifts of actual Euler blocks and weighted path events

The existing Haar-preserving phase translation moves every literal prime
factor and block frequency by the same amount. Shifting by -t turns the
whole-product energy at t into the energy at zero and subtracts t from
every block frequency, with the exact Euler normalizer retained.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperBlockPhaseShift
open scoped BigOperators
open MeasureTheory Set SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerSecondMoment HarperEulerLogComparison HarperPrimeBlocks HarperPrimeBlockLaw
  HarperPrimeBlockPath HarperPhaseShift HarperTiltedMeasure HarperSmoothCount

theorem primeTerm_shift {q : ℕ} (hq : q.Prime) (t v : ℝ) (ω : PhaseSpace) :
    primeTerm q t (phaseShift v ω) = primeTerm q (t+v) ω := by
  unfold primeTerm
  rw [steinhaus_prime_shift hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have he : -linePoint (1/2) (t+v) = (-(v : ℂ)*Complex.I)+(-linePoint (1/2) t) := by
    simp only [linePoint,Complex.ofReal_add]
    ring
  simp only [div_eq_mul_inv,← Complex.cpow_neg,HarperEulerIncrement.twist]
  simp only [div_eq_mul_inv] at he
  rw [he,Complex.cpow_add _ _ hqC]
  ring

theorem blockProduct_shift (x : ℝ) (l : ℕ) (t v : ℝ) (ω : PhaseSpace) :
    blockProduct x l t (phaseShift v ω) = blockProduct x l (t+v) ω := by
  apply Finset.prod_congr rfl
  intro q hq
  rw [primeTerm_shift (primeBlock_mem.mp hq).1]

theorem blockLog_shift (x : ℝ) (l : ℕ) (t v : ℝ) (ω : PhaseSpace) :
    blockLog x l t (phaseShift v ω) = blockLog x l (t+v) ω := by
  simp only [blockLog,blockProduct_shift]

theorem blockPathEvent_shift {n : ℕ} (x : ℝ) (l : Fin n → ℕ)
    (t u v : Fin n → ℝ) (s : ℝ) :
    phaseShift s ⁻¹' blockPathEvent x l t u v = blockPathEvent x l (fun i => t i+s) u v := by
  ext ω
  simp only [blockPathEvent,Set.mem_preimage,blockLog_shift]

theorem weighted_event_shift (P t : ℝ) {A : Set PhaseSpace} (hA : MeasurableSet A) :
    (∫ ω in A, ‖eulerProduct P (linePoint (1/2) t) ω‖^2 ∂phaseMeasure) =
      ∫ ω in phaseShift (-t) ⁻¹' A, ‖eulerProduct P (linePoint (1/2) 0) ω‖^2 ∂phaseMeasure := by
  rw [← integral_indicator hA,← integral_indicator (hA.preimage (phaseShift (-t)).measurable)]
  rw [← phaseShift_integral (-t) (A.indicator (fun ω => ‖eulerProduct P (linePoint (1/2) t) ω‖^2))]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases h : phaseShift (-t) ω ∈ A
  · simp only [Set.indicator_of_mem h,Set.indicator_of_mem (show ω ∈ phaseShift (-t) ⁻¹' A from h),
      eulerProduct_shift,add_neg_cancel]
  · simp only [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show ω ∉ phaseShift (-t) ⁻¹' A from h)]

theorem critical_weighted_event (P : ℝ) {A : Set PhaseSpace} (hA : MeasurableSet A) :
    (∫ ω in A, ‖eulerProduct P (linePoint (1/2) 0) ω‖^2 ∂phaseMeasure) =
      shiftedProduct P 1*(tiltedMeasure P (linePoint (1/2) 0)).real A := by
  have h := tiltedMeasure_event P (s := linePoint (1/2) 0) (by norm_num [linePoint]) hA
  have hp := shiftedProduct_pos P (show (0 : ℝ) < 1 by norm_num)
  norm_num only [linePoint_re,show (2 : ℝ)*(1/2)=1 by norm_num] at h
  exact (div_eq_iff (ne_of_gt hp)).mp h.symm |>.trans (mul_comm _ _)

theorem weighted_path_tilted {n : ℕ} (P x t : ℝ) (l : Fin n → ℕ)
    (s u v : Fin n → ℝ) :
    (∫ ω in blockPathEvent x l s u v, ‖eulerProduct P (linePoint (1/2) t) ω‖^2 ∂phaseMeasure) =
      shiftedProduct P 1*(tiltedMeasure P (linePoint (1/2) 0)).real
        (blockPathEvent x l (fun i => s i-t) u v) := by
  rw [weighted_event_shift P t (blockPathEvent_measurable x l s u v),blockPathEvent_shift]
  simpa only [sub_eq_add_neg] using critical_weighted_event P
    (blockPathEvent_measurable x l (fun i => s i+(-t)) u v)

end NField.Alignment.HarperBlockPhaseShift
