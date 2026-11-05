/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSourceKilledPath

/-!
# A uniform Gaussian endpoint contraction

A centered Gaussian has half its mass on either side of zero. Its density
bounds the extra mass below a small positive endpoint. A variance lower
bound then gives the numerical contraction used in the survival argument.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianEndpoint
open MeasureTheory ProbabilityTheory Set HarperGaussianTail

theorem gaussian_mass_density (m : ℝ) {v : NNReal} (hv : 0 < v) (s : Set ℝ) :
    (gaussianReal m v).real s = ∫ z in s, gaussianPDFReal m v z := by
  rw [measureReal_def,gaussianReal_apply_eq_integral m (ne_of_gt hv),
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg m v))]

theorem gaussian_positive_half {v : NNReal} (hv : 0 < v) :
    (gaussianReal 0 v).real (Ioi (0 : ℝ)) = 1/2 := by
  rw [gaussian_mass_density 0 hv]
  simp only [gaussianPDFReal,sub_zero]
  rw [integral_const_mul,gaussian_tail_envelope_integral hv]
  have hs : Real.sqrt (2*Real.pi*(v : ℝ)) ≠ 0 := by positivity
  field_simp

theorem gaussian_nonpositive_half {v : NNReal} (hv : 0 < v) :
    (gaussianReal 0 v).real (Iic (0 : ℝ)) = 1/2 := by
  have h := measureReal_add_measureReal_compl (μ := gaussianReal 0 v)
    (s := Iic (0 : ℝ)) measurableSet_Iic
  rw [compl_Iic,probReal_univ,gaussian_positive_half hv] at h
  linarith

theorem gaussian_density_le_inv_sqrt {v : NNReal} (hv : 0 < v) (z : ℝ) :
    gaussianPDFReal 0 v z ≤ 1/Real.sqrt v := by
  have hv0 : (0 : ℝ) < v := hv
  have hp : (v : ℝ) ≤ 2*Real.pi*v := by nlinarith [Real.pi_gt_three]
  have hs := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hv0) (Real.sqrt_le_sqrt hp)
  unfold gaussianPDFReal
  simp only [sub_zero]
  calc
    _ ≤ (Real.sqrt (2*Real.pi*v))⁻¹*1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg z)) (by positivity))
    _ ≤ _ := by simpa only [mul_one,one_div] using hs

theorem gaussian_positive_interval_mass {v : NNReal} (hv : 0 < v)
    {R : ℝ} (hR : 0 ≤ R) :
    (gaussianReal 0 v).real (Ioc 0 R) ≤ R/Real.sqrt v := by
  rw [gaussian_mass_density 0 hv]
  calc
    _ ≤ ∫ _ in Ioc (0 : ℝ) R, (1/Real.sqrt (v : ℝ)) := by
      apply integral_mono (integrable_gaussianPDFReal 0 v).integrableOn
        (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) R)
          (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      exact gaussian_density_le_inv_sqrt hv
    _ = _ := by rw [setIntegral_const,Real.volume_real_Ioc_of_le hR]; simp [div_eq_mul_inv]

theorem gaussian_endpoint_mass {v : NNReal} (hv : 0 < v) {R : ℝ} (hR : 0 ≤ R) :
    (gaussianReal 0 v).real (Iic R) ≤ 1/2+R/Real.sqrt v := by
  have he : Iic R = Iic (0 : ℝ) ∪ Ioc 0 R := by
    ext z
    simp only [Set.mem_Iic,Set.mem_union,Set.mem_Ioc]
    constructor
    · intro hz
      by_cases hz0 : z ≤ 0
      · exact Or.inl hz0
      · exact Or.inr ⟨lt_of_not_ge hz0,hz⟩
    · rintro (hz | hz)
      · exact hz.trans hR
      · exact hz.2
  rw [he]
  have h := measureReal_union_le (μ := gaussianReal 0 v) (Iic (0 : ℝ)) (Ioc 0 R)
  rw [gaussian_nonpositive_half hv] at h
  linarith [gaussian_positive_interval_mass hv hR]

theorem gaussian_endpoint_contraction {q : ℝ} (hq : 0 < q) {v : NNReal}
    (hv : q/4 ≤ (v : ℝ)) :
    (gaussianReal 0 v).real (Iic (Real.sqrt q/20)) ≤ 3/5 := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hs : Real.sqrt q/2 ≤ Real.sqrt (v : ℝ) := by
    have hsq := Real.sq_sqrt (NNReal.coe_nonneg v)
    have hqq := Real.sq_sqrt hq.le
    nlinarith [Real.sqrt_nonneg q,Real.sqrt_nonneg (v : ℝ)]
  have he : (Real.sqrt q/20)/Real.sqrt (v : ℝ) ≤ 1/10 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hv0)).mpr
    linarith
  have h := gaussian_endpoint_mass (show 0 < v from hv0)
    (show 0 ≤ Real.sqrt q/20 by positivity)
  linarith

end NField.Alignment.HarperGaussianEndpoint
