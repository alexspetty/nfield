/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperJointGoodEvent

/-!
# Fractional moments on a measurable event and its complement

Holder is applied to the actual energy power and the event indicator.
Boundedness supplies the required Lp hypotheses; positive exponents
justify every indicator and real-power identity.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperFractionalEventSplit
open scoped ENNReal
open MeasureTheory Set SteinhausMoment HarperRestrictedMoment

theorem indicator_rpow (A : Set PhaseSpace) (f : PhaseSpace → ℝ) {q : ℝ}
    (hq : q ≠ 0) (ω : PhaseSpace) :
    (A.indicator f ω)^q = A.indicator (fun ω => (f ω)^q) ω := by
  classical
  by_cases h : ω ∈ A
  · simp [h]
  · simp [h,Real.zero_rpow hq]

theorem bounded_fractional_memLp {f : PhaseSpace → ℝ}
    (hi : Integrable f phaseMeasure) (hf : ∀ ω, 0 ≤ f ω) {K : ℝ}
    (hK : ∀ ω, f ω ≤ K) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (p : ℝ≥0∞) :
    MemLp (fun ω => (f ω)^q) p phaseMeasure := by
  apply MemLp.of_bound (nonnegative_fractional_integrable hi hf hq0 hq1).aestronglyMeasurable (K^q)
  apply ae_of_all
  intro ω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hf ω) q)]
  exact Real.rpow_le_rpow (hf ω) (hK ω) hq0

theorem restricted_fractional_holder {f : PhaseSpace → ℝ}
    (hi : Integrable f phaseMeasure) (hf : ∀ ω, 0 ≤ f ω) {K : ℝ}
    (hK : ∀ ω, f ω ≤ K) {A : Set PhaseSpace} (hA : MeasurableSet A)
    {q r : ℝ} (hq : 0 < q) (hqr : q < r) (hr : r ≤ 1) :
    (∫ ω in A, (f ω)^q ∂phaseMeasure) ≤
      (∫ ω, (f ω)^r ∂phaseMeasure)^(q/r)*(phaseMeasure.real A)^(1-q/r) := by
  have hr0 : 0 < r := hq.trans hqr
  have ht0 : 0 < q/r := div_pos hq hr0
  have ht1 : q/r < 1 := (div_lt_one hr0).mpr hqr
  have hp := Real.HolderConjugate.inv_one_sub_inv ht0 ht1
  have hmem := bounded_fractional_memLp hi hf hK hq.le (hqr.le.trans hr)
    (ENNReal.ofReal (q/r)⁻¹)
  have hmemA : MemLp (A.indicator (fun _ : PhaseSpace => (1 : ℝ)))
      (ENNReal.ofReal (1-q/r)⁻¹) phaseMeasure := (memLp_const (1 : ℝ)).indicator hA
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (ae_of_all _ (fun ω => Real.rpow_nonneg (hf ω) q))
    (ae_of_all _ (Set.indicator_nonneg (fun _ _ => by norm_num))) hmem hmemA
  have he : (fun ω => (f ω)^q*A.indicator (fun _ => (1 : ℝ)) ω) =
      A.indicator (fun ω => (f ω)^q) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have hepow (ω : PhaseSpace) : ((f ω)^q)^((q/r)⁻¹) = (f ω)^r := by
    rw [← Real.rpow_mul (hf ω)]
    congr 1
    field_simp
  have heA : (∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω)^((1-q/r)⁻¹) ∂phaseMeasure) =
      phaseMeasure.real A := by
    have hn : (1-q/r)⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr (by linarith))
    simp_rw [indicator_rpow _ _ hn,Real.one_rpow]
    rw [integral_indicator hA]
    simp
  rw [he,integral_indicator hA] at h
  simp_rw [hepow] at h
  rw [heA] at h
  simpa only [one_div,inv_inv] using h

theorem fractional_event_split {f : PhaseSpace → ℝ}
    (hi : Integrable f phaseMeasure) (hf : ∀ ω, 0 ≤ f ω) {K : ℝ}
    (hK : ∀ ω, f ω ≤ K) {A : Set PhaseSpace} (hA : MeasurableSet A)
    {q r : ℝ} (hq : 0 < q) (hqr : q < r) (hr : r ≤ 1) :
    (∫ ω, (f ω)^q ∂phaseMeasure) ≤
      (∫ ω, (A.indicator f ω)^q ∂phaseMeasure)+
      (∫ ω, (f ω)^r ∂phaseMeasure)^(q/r)*(phaseMeasure.real Aᶜ)^(1-q/r) := by
  have hpow := nonnegative_fractional_integrable hi hf hq.le (hqr.le.trans hr)
  rw [← integral_add_compl hA hpow]
  simp_rw [indicator_rpow A f hq.ne']
  rw [integral_indicator hA]
  exact add_le_add le_rfl (restricted_fractional_holder hi hf hK hA.compl hq hqr hr)

end NField.Alignment.HarperFractionalEventSplit
