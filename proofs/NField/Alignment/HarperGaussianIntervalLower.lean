/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianInterval
import NField.Alignment.HarperPrimeBlockVariance

/-!
# Lower mass of the source Gaussian intervals

The leading prime-sum mean is bounded by twice its variance. A literal
normal density with variance in [1/4,3/4] has a uniform lower bound on
the source's slowly growing center range. Integrating over a sufficiently
wide interval gives the mass needed to convert absolute to relative error.
The width condition is explicit here; source block growth discharges it later.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianIntervalLower
open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set HarperPrimeRangeCharacteristic

theorem rangeMean_abs_le (S : Finset ℕ) (t : ℕ → ℝ) :
    |rangeMean S t| ≤ 2*rangeVariance S := by
  unfold rangeMean rangeVariance
  calc
    _ ≤ ∑ q ∈ S, |Real.cos (t q*Real.log q)/(q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S, (q : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_div, show |(q : ℝ)| = (q : ℝ) from abs_of_nonneg (Nat.cast_nonneg q)]
      simpa only [one_div] using div_le_div_of_nonneg_right
        (Real.abs_cos_le_one _) (Nat.cast_nonneg q)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring

theorem gaussian_exponent_budget {X : ℝ} (hlog : 360000 ≤ Real.log X) :
    2+2*(Real.sqrt (Real.log X)/40+9/2)^2 ≤ Real.log X/300 := by
  have hlog0 : 0 ≤ Real.log X := by linarith
  have hs : 600 ≤ Real.sqrt (Real.log X) := by
    calc
      600 = Real.sqrt (360000 : ℝ) := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hlog
  have hr0 : 0 ≤ Real.sqrt (Real.log X)/40+9/2 := by positivity
  have hr : Real.sqrt (Real.log X)/40+9/2 ≤ Real.sqrt (Real.log X)/30 := by
    linarith
  have hsq := sq_le_sq₀ hr0 (by positivity) |>.mpr hr
  nlinarith [Real.sq_sqrt hlog0]

theorem gaussianPDF_source_lower {X m z : ℝ} {v : ℝ≥0}
    (hX : 0 < X) (hlog : 360000 ≤ Real.log X)
    (hvlo : (1/4 : ℝ) ≤ v) (hvhi : (v : ℝ) ≤ 3/4)
    (hz : |z-m| ≤ Real.sqrt (Real.log X)/40+9/2) :
    X^(-(1/300 : ℝ)) ≤ gaussianPDFReal m v z := by
  have hv0 : 0 < (v : ℝ) := by linarith
  have hd : 0 < Real.sqrt (2*Real.pi*v) := Real.sqrt_pos.mpr (by positivity)
  have hd3 : Real.sqrt (2*Real.pi*v) ≤ 3 := by
    have hb : 2*Real.pi*v ≤ 9 := by nlinarith [Real.pi_lt_four]
    calc
      _ ≤ Real.sqrt (9 : ℝ) := Real.sqrt_le_sqrt hb
      _ = 3 := by norm_num
  have hexp : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpre : Real.exp (-2) ≤ (Real.sqrt (2*Real.pi*v))⁻¹ := by
    simpa only [Real.exp_neg, one_div] using
      one_div_le_one_div_of_le hd (hd3.trans hexp)
  have hR : 0 ≤ Real.sqrt (Real.log X)/40+9/2 := by positivity
  have hs : (z-m)^2 ≤ (Real.sqrt (Real.log X)/40+9/2)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr hz
  have he : -(2*(Real.sqrt (Real.log X)/40+9/2)^2) ≤ -(z-m)^2/(2*v) := by
    rw [le_div_iff₀ (by positivity : 0 < 2*(v : ℝ))]
    nlinarith [sq_nonneg (Real.sqrt (Real.log X)/40+9/2)]
  rw [Real.rpow_def_of_pos hX]
  calc
    _ ≤ Real.exp (-2-2*(Real.sqrt (Real.log X)/40+9/2)^2) := by
      apply Real.exp_le_exp.mpr
      linarith [gaussian_exponent_budget hlog]
    _ = Real.exp (-2)*Real.exp (-(2*(Real.sqrt (Real.log X)/40+9/2)^2)) := by
      simp only [sub_eq_add_neg, Real.exp_add]
    _ ≤ (Real.sqrt (2*Real.pi*v))⁻¹*Real.exp (-(z-m)^2/(2*v)) :=
      mul_le_mul hpre (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity)
    _ = gaussianPDFReal m v z := rfl

theorem gaussian_interval_lower {X m a w : ℝ} {v : ℝ≥0}
    (hX : 0 < X) (hlog : 360000 ≤ Real.log X)
    (hvlo : (1/4 : ℝ) ≤ v) (hvhi : (v : ℝ) ≤ 3/4)
    (hm : |m| ≤ 3/2) (ha : |a| ≤ Real.sqrt (Real.log X)/40+2)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    w*X^(-(1/300 : ℝ)) ≤ (gaussianReal m v).real (Icc a (a+w)) := by
  have hvne : v ≠ 0 := by intro h; rw [h] at hvlo; norm_num at hvlo
  have hd (z : ℝ) (hz : z ∈ Icc a (a+w)) :
      X^(-(1/300 : ℝ)) ≤ gaussianPDFReal m v z := by
    apply gaussianPDF_source_lower hX hlog hvlo hvhi
    have hza : |z-a| ≤ w := by rw [abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2]
    have h := abs_sub_le z a m
    have h' := abs_sub a m
    linarith
  rw [measureReal_def, gaussianReal_apply_eq_integral m hvne,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg m v))]
  calc
    _ = ∫ _ in Icc a (a+w), X^(-(1/300 : ℝ)) := by
      rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]
      simp only [add_sub_cancel_left, max_eq_left hw0]
    _ ≤ _ := setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne)
      (integrable_gaussianPDFReal m v).integrableOn measurableSet_Icc hd

theorem gaussian_interval_mass_lower {X m a w : ℝ} {v : ℝ≥0}
    (hX : 0 < X) (hlog : 360000 ≤ Real.log X)
    (hvlo : (1/4 : ℝ) ≤ v) (hvhi : (v : ℝ) ≤ 3/4)
    (hm : |m| ≤ 3/2) (ha : |a| ≤ Real.sqrt (Real.log X)/40+2)
    (hw : X^(-(1/300 : ℝ)) ≤ w) (hw1 : w ≤ 1) :
    X^(-(1/150 : ℝ)) ≤ (gaussianReal m v).real (Icc a (a+w)) := by
  have hp : 0 ≤ X^(-(1/300 : ℝ)) := Real.rpow_nonneg hX.le _
  calc
    _ = X^(-(1/300 : ℝ))*X^(-(1/300 : ℝ)) := by
      rw [← Real.rpow_add hX]; norm_num
    _ ≤ w*X^(-(1/300 : ℝ)) := mul_le_mul_of_nonneg_right hw hp
    _ ≤ _ := gaussian_interval_lower hX hlog hvlo hvhi hm ha (hp.trans hw) hw1

end NField.Alignment.HarperGaussianIntervalLower
