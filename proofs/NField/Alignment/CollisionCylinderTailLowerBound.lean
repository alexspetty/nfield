/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialMoments
import NField.Alignment.CollisionPositionTheorem
import NField.Alignment.CollisionPotentialReflection

/-!
# Cylinder excess and the stationary lower tail

The negative conditional mean on the zero residue cylinder forces a
positive excess below a threshold. This is an integral of the actual
Haar potential; no value of its L2 representative at an integer is used.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCylinderTailLowerBound

open scoped Classical ENNReal
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialMoments CollisionCylinderMeans
open CollisionDivisibilityCovariance CollisionPositionTheorem CollisionPotentialReflection
open CollisionOdometerRecurrence CollisionCylinderOne CollisionJordanVariance

theorem cylinder_zero_integral {L : ℕ} (hL : 0 < L) :
    (∫ x in residueEvent L 0, collisionPotential x ∂phaseHaar)=
      -alignmentConstant L/(L : ℝ) := by
  have h := cylinderFunctional_integral L 0 collisionPotential
  change cylinderMean L 0=(L : ℝ)*(∫ x in residueEvent L 0, collisionPotential x ∂phaseHaar) at h
  have hz : cylinderMean L 0 = -alignmentConstant L := by
    have hg := cylinderMean_gap hL 0
    simp only [ageTerm,Nat.zero_mod,Nat.cast_zero,mul_zero,tsum_zero] at hg
    linarith
  rw [hz] at h
  apply (eq_div_iff (show (L : ℝ) ≠ 0 by exact_mod_cast (show L ≠ 0 by omega))).mpr
  linarith

theorem cylinder_excess_integral {L : ℕ} (hL : 0 < L) (H : ℝ) :
    (∫ x in residueEvent L 0, -collisionPotential x-H ∂phaseHaar)=
      (alignmentConstant L-H)/(L : ℝ) := by
  have hY := memLp_one_iff_integrable.mp (potential_memLp_finite 1 (by simp))
  have hYn : IntegrableOn (fun x => -collisionPotential x) (residueEvent L 0) phaseHaar :=
    hY.neg.integrableOn
  have hH : IntegrableOn (fun _ : Phase => H) (residueEvent L 0) phaseHaar := integrable_const H
  have hm : (phaseHaar.restrict (residueEvent L 0)).real Set.univ=
      phaseHaar.real (residueEvent L 0) := by simp only [Measure.real,Measure.restrict_apply_univ]
  rw [integral_sub hYn hH,integral_neg,
    cylinder_zero_integral hL,integral_const,smul_eq_mul,hm,residueEvent_measure (by omega : 0 < L)]
  ring

theorem cylinder_truncated_excess {L : ℕ} (hL : 0 < L) (H : ℝ) :
    (alignmentConstant L-H)/(L : ℝ) ≤
      ∫ x, ((residueEvent L 0)∩{x | collisionPotential x < -H}).indicator
        (fun x => -collisionPotential x-H) x ∂phaseHaar := by
  have hY := memLp_one_iff_integrable.mp (potential_memLp_finite 1 (by simp))
  have hF : Integrable (fun x => -collisionPotential x-H) phaseHaar := hY.neg.sub (integrable_const H)
  have hB : MeasurableSet {x | collisionPotential x < -H} :=
    measurableSet_lt (Lp.stronglyMeasurable collisionPotential).measurable measurable_const
  rw [← cylinder_excess_integral hL H,← integral_indicator (residueEvent_measurable L 0)]
  apply integral_mono (hF.indicator (residueEvent_measurable L 0))
    (hF.indicator ((residueEvent_measurable L 0).inter hB))
  intro x
  by_cases hA : x∈residueEvent L 0
  · by_cases hB' : collisionPotential x < -H
    · simp [hA,hB']
    · have hneg : -collisionPotential x-H ≤ 0 := by linarith [le_of_not_gt hB']
      simpa [hA,hB'] using hneg
  · simp [hA]

theorem integral_abs_on_set_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : Ω → ℝ) (hF : MemLp F 2 μ)
    (B : Set Ω) (hB : MeasurableSet B) :
    (∫ x in B, |F x| ∂μ) ≤
      Real.sqrt (∫ x, (F x)^2 ∂μ)*Real.sqrt (μ.real B) := by
  let G : Ω → ℝ := B.indicator (fun _ => 1)
  have hG : MemLp G (ENNReal.ofReal (2 : ℝ)) μ := by
    exact (memLp_const (1 : ℝ)).indicator hB
  have hGnon (x : Ω) : 0 ≤ G x := by
    by_cases hx : x∈B <;> simp [G,hx]
  have hGsq (x : Ω) : (G x)^2=G x := by
    by_cases hx : x∈B <;> simp [G,hx]
  have h := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    (by simpa using hF) hG
  simp only [Real.norm_eq_abs,abs_of_nonneg (hGnon _),Real.rpow_two,sq_abs,hGsq] at h
  have hleft : (∫ x, |F x| * G x ∂μ)=(∫ x in B, |F x| ∂μ) := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈B <;> simp [G,hx]
  have hright : (∫ x, G x ∂μ)=μ.real B := by
    dsimp only [G]
    rw [integral_indicator hB]
    simp
  rw [hleft,hright] at h
  simpa only [Real.sqrt_eq_rpow] using h

theorem cylinder_excess_upper {L : ℕ} (hL : 0 < L) {H : ℝ} (hH : 0 ≤ H) :
    (alignmentConstant L-H)/(L : ℝ) ≤
      ‖collisionPotential‖*Real.sqrt (phaseHaar.real {x | collisionPotential x < -H}) := by
  have hY := memLp_one_iff_integrable.mp (potential_memLp_finite 1 (by simp))
  have hB : MeasurableSet {x | collisionPotential x < -H} :=
    measurableSet_lt (Lp.stronglyMeasurable collisionPotential).measurable measurable_const
  have hF : Integrable (fun x => -collisionPotential x-H) phaseHaar := hY.neg.sub (integrable_const H)
  have he : (∫ x, (collisionPotential x)^2 ∂phaseHaar)=‖collisionPotential‖^2 := by
    rw [collisionPotential_second_moment,collisionPotential_variance]
  calc
    _ ≤ ∫ x, ((residueEvent L 0)∩{x | collisionPotential x < -H}).indicator
      (fun x => -collisionPotential x-H) x ∂phaseHaar := cylinder_truncated_excess hL H
    _ ≤ ∫ x, {x | collisionPotential x < -H}.indicator (fun x => |collisionPotential x|) x ∂phaseHaar := by
      apply integral_mono (hF.indicator ((residueEvent_measurable L 0).inter hB)) (hY.abs.indicator hB)
      intro x
      by_cases hA : x∈residueEvent L 0
      · by_cases hB' : collisionPotential x < -H
        · have hx : collisionPotential x ≤ 0 := by linarith
          simpa [hA,hB',abs_of_nonpos hx] using sub_le_self (-collisionPotential x) hH
        · simp [hA,hB']
      · by_cases hB' : collisionPotential x < -H <;> simp [hA,hB',abs_nonneg]
    _ = ∫ x in {x | collisionPotential x < -H}, |collisionPotential x| ∂phaseHaar := integral_indicator hB
    _ ≤ Real.sqrt (∫ x, (collisionPotential x)^2 ∂phaseHaar)*
        Real.sqrt (phaseHaar.real {x | collisionPotential x < -H}) :=
      integral_abs_on_set_le_second_moment collisionPotential (Lp.memLp collisionPotential) _ hB
    _ = _ := by rw [he,Real.sqrt_sq (norm_nonneg _)]

theorem cylinder_tail_lower_bound {L : ℕ} (hL : 0 < L) {H : ℝ} (hH : 0 ≤ H)
    (hHC : H < alignmentConstant L) :
    (alignmentConstant L-H)^2/((L : ℝ)^2*‖collisionPotential‖^2) ≤
      phaseHaar.real {x | collisionPotential x < -H} := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hV : 0 < ‖collisionPotential‖^2 :=
    (by norm_num : (0 : ℝ) < 1/144).trans_le collisionPotential_variance_lower
  have hb := cylinder_excess_upper hL hH
  have ha : 0 < (alignmentConstant L-H)/(L : ℝ) := div_pos (sub_pos.mpr hHC) hLp
  have hroot : (‖collisionPotential‖*Real.sqrt (phaseHaar.real {x | collisionPotential x < -H}))^2=
      ‖collisionPotential‖^2*phaseHaar.real {x | collisionPotential x < -H} := by
    rw [mul_pow,Real.sq_sqrt (measureReal_nonneg)]
  have hs : ((alignmentConstant L-H)/(L : ℝ))^2 ≤
      ‖collisionPotential‖^2*phaseHaar.real {x | collisionPotential x < -H} := by
    rw [← hroot]
    exact pow_le_pow_left₀ ha.le hb 2
  calc
    _ = (((alignmentConstant L-H)/(L : ℝ))^2)/‖collisionPotential‖^2 := by ring
    _ ≤ _ := (div_le_iff₀ hV).mpr (by simpa only [mul_comm] using hs)

end NField.Alignment.CollisionCylinderTailLowerBound
