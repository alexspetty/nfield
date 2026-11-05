/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGoodAllowance

/-!
# Restricted critical energy and the actual tilted barrier

The global good event is first restricted to one frequency, shifted by
the existing Haar automorphism, and bounded by the actual source-path
probability. The exact second-moment normalizer is retained. The finite
frequency integral is interchanged only after joint integrability of the
indicator-weighted energy has been proved.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRestrictedEnergy
open scoped BigOperators
open MeasureTheory Set SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerSecondMoment HarperFrequencyIntervals HarperPrimeBlocks HarperPrimeBlockPath
  HarperCriticalGoodEvent HarperFrequencyMesh HarperReversedGoodPath HarperGoodAllowance
  HarperBlockPhaseShift HarperRoundedSourcePath HarperSourceBarrierBound HarperTiltedMeasure
  HarperSmoothCount CollisionMertensInput

theorem restricted_frequency_energy :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ M : ℕ, X₀ ≤ blockUpper x M →
      ∀ a : ℝ, 0 ≤ a → ∀ t : ℝ, |t| ≤ 1/2 →
      (∫ ω in sourceGoodEvent x M a,
        ‖eulerProduct (sourceCutoff x) (linePoint (1/2) t) ω‖^2 ∂phaseMeasure) ≤
      inversePrimeProduct (sourceCutoff x)*sourceBarrierConstant 11*
        min 1 (pathAmplitude x M a/Real.sqrt ((M+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := actual_rounded_source_barrier (show (0 : ℝ) ≤ 11 by norm_num)
  refine ⟨max X₀ (Real.exp (Real.exp 1)),fun x hx M hfirst a ha t ht => ?_⟩
  have hL : Real.exp 1 ≤ logScale x M := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) ((le_max_right _ _).trans hfirst)
    simpa only [Real.log_exp,logScale] using h
  have hc : 1 ≤ terminalLogScale x M := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp,terminalLogScale] using h
  have hprob := hX₀ x hx M (reverseIndex M) (reverseIndex_strictAnti M)
    (by simpa only [reverseIndex_zero] using (le_max_left _ _).trans hfirst) t
    (fun i => -sourceAllowance x a (reverseIndex M i))
    (fun i => sourceAllowance x a (reverseIndex M i)) (pathAmplitude x M a)
    (pathAmplitude_ge_one M ha hc) (sourceAllowance_lower hx M hc a)
    (fun i => by simpa only [add_comm (pathAmplitude x M a)] using sourceAllowance_upper hx M hc a i)
  calc
    _ ≤ ∫ ω in fixedGoodPath x M t a,
        ‖eulerProduct (sourceCutoff x) (linePoint (1/2) t) ω‖^2 ∂phaseMeasure :=
      setIntegral_mono_set
        (eulerProduct_norm_sq_integrable (sourceCutoff x) (show 0 < (linePoint (1/2) t).re by norm_num [linePoint])).integrableOn
        (ae_of_all _ (fun _ => sq_nonneg _)) (ae_of_all _ (sourceGoodEvent_subset_fixed M ht))
    _ = shiftedProduct (sourceCutoff x) 1*(tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
        (blockPathEvent x (reverseIndex M) (fun i => approximation x t (reverseIndex M i)-t)
          (fun i => -sourceAllowance x a (reverseIndex M i))
          (fun i => sourceAllowance x a (reverseIndex M i))) :=
      weighted_path_tilted _ _ _ _ _ _ _
    _ ≤ _ := by
      rw [shiftedProduct_one]
      have hm := mul_le_mul_of_nonneg_left hprob (inversePrimeProduct_pos (sourceCutoff x)).le
      simpa only [mul_assoc] using hm

theorem restricted_interval_fubini (P α β : ℝ) {A : Set PhaseSpace} (hA : MeasurableSet A) :
    (∫ ω in A, intervalEnergy P (1/2) α β ω ∂phaseMeasure) =
      ∫ t in Ioc α β, ∫ ω in A, verticalEnergy P (1/2) (t,ω) ∂phaseMeasure := by
  let f : ℝ × PhaseSpace → ℝ := (Prod.snd ⁻¹' A).indicator (verticalEnergy P (1/2))
  have hi : Integrable f ((volume.restrict (Ioc α β)).prod phaseMeasure) :=
    (verticalEnergy_integrable P α β (show (0 : ℝ) < 1/2 by norm_num)).indicator
      (hA.preimage measurable_snd)
  calc
    _ = ∫ ω, (∫ t in Ioc α β, f (t,ω)) ∂phaseMeasure := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases hω : ω ∈ A
      · simp [f,hω,intervalEnergy]
      · simp [f,hω]
    _ = ∫ t in Ioc α β, ∫ ω, f (t,ω) ∂phaseMeasure :=
      (integral_integral_swap (f := fun t ω => f (t,ω)) hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      change (∫ ω, A.indicator (fun ω => verticalEnergy P (1/2) (t,ω)) ω ∂phaseMeasure) = _
      exact integral_indicator hA

theorem restricted_fiber_integrable (P α β : ℝ) {A : Set PhaseSpace} (hA : MeasurableSet A) :
    Integrable (fun t => ∫ ω in A, verticalEnergy P (1/2) (t,ω) ∂phaseMeasure)
      (volume.restrict (Ioc α β)) := by
  have hi := ((verticalEnergy_integrable P α β (show (0 : ℝ) < 1/2 by norm_num)).indicator
    (hA.preimage measurable_snd)).integral_prod_left
  apply hi.congr
  filter_upwards [] with t
  change (∫ ω, A.indicator (fun ω => verticalEnergy P (1/2) (t,ω)) ω ∂phaseMeasure) = _
  exact integral_indicator hA

theorem restricted_unitEnergy_le (P K : ℝ) {A : Set PhaseSpace} (hA : MeasurableSet A)
    (hK : ∀ t : ℝ, |t| ≤ 1/2 → (∫ ω in A, verticalEnergy P (1/2) (t,ω) ∂phaseMeasure) ≤ K) :
    (∫ ω in A, unitEnergy P 0 ω ∂phaseMeasure) ≤ K := by
  have he : unitEnergy P 0 = intervalEnergy P (1/2) (-(1/2)) (1/2) := by
    simp only [unitEnergy,Int.cast_zero,zero_sub,zero_add]
  rw [he,restricted_interval_fubini P _ _ hA]
  calc
    _ ≤ ∫ _t in Ioc (-(1/2 : ℝ)) (1/2), K := by
      apply integral_mono_ae (restricted_fiber_integrable P _ _ hA) (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hK t (abs_le.mpr ⟨ht.1.le,ht.2⟩)
    _ = K := by norm_num

theorem actual_restricted_unitEnergy :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ M : ℕ, X₀ ≤ blockUpper x M →
      ∀ a : ℝ, 0 ≤ a →
      (∫ ω in sourceGoodEvent x M a, unitEnergy (sourceCutoff x) 0 ω ∂phaseMeasure) ≤
      inversePrimeProduct (sourceCutoff x)*sourceBarrierConstant 11*
        min 1 (pathAmplitude x M a/Real.sqrt ((M+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := restricted_frequency_energy
  refine ⟨X₀,fun x hx M hfirst a ha => ?_⟩
  exact restricted_unitEnergy_le _ _ (sourceGoodEvent_measurable x M a) (hX₀ x hx M hfirst a ha)

end NField.Alignment.HarperRestrictedEnergy
