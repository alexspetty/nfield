/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFractionalEventSplit

/-!
# The actual unit energy normalized by its logarithmic mean bound

Normalization is an explicit division of unitEnergy. One fixed positive
constant from Mertens makes its mean at most one, while the same source
good event retains its restricted saving and exponential failure bound.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperNormalizedEnergy
open Filter MeasureTheory Set SteinhausMoment HarperPrimeBlocks HarperFrequencyIntervals
  HarperCriticalGoodEvent HarperGoodEventCutoff HarperJointGoodEvent HarperRestrictedMoment
  HarperRestrictedLogMoment HarperEulerSecondMoment HarperSmoothDivisor HarperSmoothCount
  CollisionMertensInput

def normalizedEnergy (P K : ℝ) (ω : PhaseSpace) : ℝ := unitEnergy P 0 ω/(K*Real.log P)
def normalizedMoment (P K q : ℝ) : ℝ := ∫ ω, (normalizedEnergy P K ω)^q ∂phaseMeasure

theorem normalizedEnergy_nonneg {P K : ℝ} (hP : 1 ≤ P) (hK : 0 ≤ K) (ω : PhaseSpace) :
    0 ≤ normalizedEnergy P K ω := div_nonneg (unitEnergy_nonneg P 0 ω)
      (mul_nonneg hK (Real.log_nonneg hP))

theorem normalizedEnergy_integrable (P K : ℝ) : Integrable (normalizedEnergy P K) phaseMeasure :=
  (unitEnergy_integrable P 0).div_const _

theorem normalizedEnergy_bound {P K : ℝ} (hP : 1 < P) (hK : 0 < K) (ω : PhaseSpace) :
    normalizedEnergy P K ω ≤ (shiftedProduct P (1/2))^2/(K*Real.log P) :=
  div_le_div_of_nonneg_right (unitEnergy_bound P 0 ω) (mul_pos hK (Real.log_pos hP)).le

theorem normalizedMoment_nonneg {P K : ℝ} (hP : 1 ≤ P) (hK : 0 ≤ K) (q : ℝ) :
    0 ≤ normalizedMoment P K q :=
  integral_nonneg (fun ω => Real.rpow_nonneg (normalizedEnergy_nonneg hP hK ω) q)

theorem normalizedMoment_eq {P K : ℝ} (hP : 1 ≤ P) (hK : 0 ≤ K) (q : ℝ) :
    normalizedMoment P K q =
      (∫ ω, (unitEnergy P 0 ω)^q ∂phaseMeasure)/(K*Real.log P)^q := by
  unfold normalizedMoment normalizedEnergy
  simp_rw [Real.div_rpow (unitEnergy_nonneg P 0 _) (mul_nonneg hK (Real.log_nonneg hP))]
  exact integral_div _ _

theorem normalizedMoment_le_one {P K : ℝ} (hP : 1 ≤ P) (hK : 0 ≤ K)
    (hmean : (∫ ω, normalizedEnergy P K ω ∂phaseMeasure) ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : normalizedMoment P K q ≤ 1 := by
  have h := nonnegative_fractional_jensen (normalizedEnergy_integrable P K)
    (normalizedEnergy_nonneg hP hK) hq0 hq1
  apply h.trans
  simpa only [Real.one_rpow] using Real.rpow_le_rpow
    (integral_nonneg (normalizedEnergy_nonneg hP hK)) hmean hq0

theorem joint_normalized_bounds :
    ∃ B : ℕ, ∃ K C D : ℝ, 0 < K ∧ 0 < C ∧ 0 < D ∧ ∀ᶠ x : ℝ in atTop,
      1 < sourceCutoff x ∧ 0 < Real.sqrt (Real.log (Real.log x)) ∧
      (∫ ω, normalizedEnergy (sourceCutoff x) K ω ∂phaseMeasure) ≤ 1 ∧
      ∀ a : ℝ, 1 ≤ a → ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
        (∫ ω, ((sourceGoodEvent x (terminalBlock B x) a).indicator
          (normalizedEnergy (sourceCutoff x) K) ω)^q ∂phaseMeasure) ≤
            ((C*min 1 (a/Real.sqrt (Real.log (Real.log x))))^q) ∧
        phaseMeasure.real (sourceGoodEvent x (terminalBlock B x) a)ᶜ ≤ D*Real.exp (-2*a) := by
  obtain ⟨B,C,D,hC,hD,hbound⟩ := joint_good_event_bounds
  obtain ⟨K,hK,hprod⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨B,K,C/K,D,hK,div_pos hC hK,hD,?_⟩
  filter_upwards [hbound,sourceCutoff_tendsto.eventually hprod.bound,
    sourceCutoff_tendsto.eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop (0 : ℝ)]
    with x hx hprod hP hY
  have hden : 0 < K*Real.log (sourceCutoff x) := mul_pos hK (Real.log_pos hP)
  have hp : inversePrimeProduct (sourceCutoff x) ≤ K*Real.log (sourceCutoff x) := by
    simpa only [Real.norm_eq_abs,abs_of_pos (inversePrimeProduct_pos _),
      abs_of_nonneg (Real.log_nonneg hP.le)] using hprod
  refine ⟨hP,Real.sqrt_pos.mpr hY,?_,?_⟩
  · unfold normalizedEnergy
    rw [integral_div,unitEnergy_mean,div_le_one hden]
    exact hp
  · intro a ha q hq0 hq1
    refine ⟨?_,(hx a ha).2⟩
    have hG := sourceGoodEvent_measurable x (terminalBlock B x) a
    have hn := normalizedEnergy_nonneg hP.le hK.le
    have hi := (normalizedEnergy_integrable (sourceCutoff x) K).indicator hG
    have hf : ∀ ω, 0 ≤ (sourceGoodEvent x (terminalBlock B x) a).indicator
        (normalizedEnergy (sourceCutoff x) K) ω := Set.indicator_nonneg (fun ω _ => hn ω)
    apply (nonnegative_fractional_jensen hi hf hq0 hq1).trans
    apply Real.rpow_le_rpow (integral_nonneg hf) _ hq0
    rw [integral_indicator hG]
    unfold normalizedEnergy
    rw [integral_div]
    calc
      _ ≤ (C*Real.log (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))))/
          (K*Real.log (sourceCutoff x)) := div_le_div_of_nonneg_right (hx a ha).1 hden.le
      _ = _ := by
        have hl0 := ne_of_gt (Real.log_pos hP)
        field_simp

end NField.Alignment.HarperNormalizedEnergy
