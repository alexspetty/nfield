/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionUpperTails
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential moments from the actual tail probabilities

The layer-cake identity is applied before integrability is known. Its
finite upper bound then establishes integrability and the moment bound.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionExponentialMoments

open scoped Classical ENNReal
open MeasureTheory

theorem exponential_primitive (c z : ℝ) :
    (∫ t in (0 : ℝ)..z, c*Real.exp (c*t))=Real.exp (c*z)-1 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (c*t)) (c*Real.exp (c*x)) x := by
    simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id x).const_mul c).exp
  have hi : IntervalIntegrable (fun t : ℝ => c*Real.exp (c*t)) volume 0 z :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simpa only [mul_zero,Real.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi

theorem weighted_tail_integral {K c d : ℝ} (hcd : c < d) :
    (∫ t in Set.Ioi (0 : ℝ), K*c*Real.exp ((c-d)*t))=K*c/(d-c) := by
  rw [integral_const_mul,integral_exp_mul_Ioi (sub_neg.mpr hcd)]
  simp only [mul_zero,Real.exp_zero]
  rw [show c-d=-(d-c) by ring,div_neg]
  ring

theorem exponential_moment_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZ : AEMeasurable Z μ) (hZ0 : ∀ᵐ x ∂μ, 0 ≤ Z x)
    {K c d : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hcd : c < d)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {x | t < Z x} ≤ K*Real.exp (-d*t)) :
    Integrable (fun x => Real.exp (c*Z x)) μ ∧
      (∫ x, Real.exp (c*Z x) ∂μ) ≤ 1+K*c/(d-c) := by
  have hgInt (t : ℝ) (_ht : 0 < t) :
      IntervalIntegrable (fun s : ℝ => c*Real.exp (c*s)) volume 0 t :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul μ hZ0 hZ hgInt
    (Filter.Eventually.of_forall (fun t => mul_nonneg hc.le (Real.exp_pos (c*t)).le))
  simp only [exponential_primitive] at hcake
  have hmajor : (∫⁻ x, ENNReal.ofReal (Real.exp (c*Z x)-1) ∂μ) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (K*c*Real.exp ((c-d)*t)) := by
    rw [hcake]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    have hT : μ {x | t < Z x} ≤ ENNReal.ofReal (K*Real.exp (-d*t)) :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
        (mul_nonneg hK (Real.exp_pos _).le)).mpr (htail t ht.le)
    calc
      _ ≤ ENNReal.ofReal (K*Real.exp (-d*t))*ENNReal.ofReal (c*Real.exp (c*t)) :=
        mul_le_mul hT le_rfl bot_le bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
        congr 1
        calc
          _ = K*c*(Real.exp (-d*t)*Real.exp (c*t)) := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hmInt : IntegrableOn (fun t : ℝ => K*c*Real.exp ((c-d)*t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (sub_neg.mpr hcd) 0).const_mul (K*c)
  have hm0 : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ K*c*Real.exp ((c-d)*t) :=
    Filter.Eventually.of_forall (fun t => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hmInt hm0,weighted_tail_integral hcd] at hmajor
  have hGmeas : AEStronglyMeasurable (fun x => Real.exp (c*Z x)-1) μ :=
    (((hZ.const_mul c).exp).sub_const 1).aestronglyMeasurable
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ Real.exp (c*Z x)-1 := by
    filter_upwards [hZ0] with x hx
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hc.le hx))
  have hGint : Integrable (fun x => Real.exp (c*Z x)-1) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hGmeas hG0).mp
      ((lt_of_le_of_lt hmajor ENNReal.ofReal_lt_top).ne)
  have hExp : Integrable (fun x => Real.exp (c*Z x)) μ := by
    have hp : Integrable (fun x => (Real.exp (c*Z x)-1)+1) μ :=
      hGint.add (integrable_const (1 : ℝ))
    simpa only [sub_add_cancel] using hp
  refine ⟨hExp,?_⟩
  have hR : 0 ≤ K*c/(d-c) := by positivity
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmajor
  rw [ENNReal.toReal_ofReal hR,← integral_eq_lintegral_of_nonneg_ae hG0 hGmeas] at hreal
  rw [integral_sub hExp (integrable_const (1 : ℝ))] at hreal
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hreal
  linarith

theorem exponential_moment_nonpositive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZ : AEMeasurable Z μ) (hZ0 : ∀ᵐ x ∂μ, 0 ≤ Z x)
    {c : ℝ} (hc : c ≤ 0) : Integrable (fun x => Real.exp (c*Z x)) μ ∧
      (∫ x, Real.exp (c*Z x) ∂μ) ≤ 1 := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (c*Z x)) μ :=
    ((hZ.const_mul c).exp).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, Real.exp (c*Z x) ≤ 1 := by
    filter_upwards [hZ0] with x hx
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc hx)
  have hLp : MemLp (fun x => Real.exp (c*Z x)) 1 μ := MemLp.of_bound hm 1 (by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx)
  have hi := memLp_one_iff_integrable.mp hLp
  refine ⟨hi,?_⟩
  have h := integral_mono_ae hi (integrable_const (1 : ℝ)) hbound
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

end NField.Alignment.CollisionExponentialMoments
