/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel for the concrete Fourier integral

For an integrable square-integrable complex function whose integral Fourier
transform is also square-integrable, identify its concrete transform with
the L2 transform through tempered distributions. The L2 isometry then gives
equality of the integrals of the squared norms. These hypotheses are proved
for the actual logarithmic smooth sum in the Harper application.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.DirichletParseval

open MeasureTheory FourierTransform SchwartzMap ComplexInnerProductSpace
open scoped Topology

theorem fourier_integral_pairing {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ,ℂ)) :
    (∫ t, (𝓕 g) t * f t) = ∫ t, g t * (𝓕 f) t := by
  have h :=
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner hf (g.integrable (μ := volume))).symm
  simp only [ContinuousLinearMap.mul_apply', flip_innerₗ] at h
  change (∫ t, f t * (𝓕 g) t) = ∫ t, (𝓕 f) t * g t at h
  simpa only [mul_comm] using h

theorem fourier_toLp {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    (hF : MemLp (𝓕 f) 2) : 𝓕 (h2.toLp f) = hF.toLp (𝓕 f) := by
  have hi : Function.Injective (Lp.toTemperedDistributionCLM ℂ volume 2) :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (E := ℝ) (F := ℂ) (μ := volume) (p := 2))
  apply hi
  change (Lp.toTemperedDistribution (𝓕 (h2.toLp f))) = Lp.toTemperedDistribution (hF.toLp (𝓕 f))
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ t, (𝓕 g) t * f t := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with t ht
      simp only [ht, smul_eq_mul]
    _ = ∫ t, g t * (𝓕 f) t := fourier_integral_pairing h1 g
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with t ht
      simp only [ht, smul_eq_mul]

theorem integral_norm_sq_Lp (f : Lp (α := ℝ) ℂ 2) :
    (∫ t : ℝ, ‖f t‖^2) = ‖f‖^2 := by
  have h := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f)
  rw [L2.inner_def] at h
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) f f)
  change (∫ t : ℝ, (inner ℂ (f t) (f t)).re) = (∫ t : ℝ, inner ℂ (f t) (f t)).re at hr
  rw [← hr] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  change (∫ t : ℝ, ((‖f t‖ : ℂ)^2).re) = ((‖f‖ : ℂ)^2).re at h
  norm_cast at h

theorem integral_norm_sq_toLp {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫ t : ℝ, ‖f t‖^2) = ‖hf.toLp f‖^2 := by
  rw [← integral_norm_sq_Lp]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

theorem integral_norm_sq_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    (hF : MemLp (𝓕 f) 2) :
    (∫ t : ℝ, ‖(𝓕 f) t‖^2) = ∫ t : ℝ, ‖f t‖^2 := by
  rw [integral_norm_sq_toLp hF, ← fourier_toLp h1 h2 hF, Lp.norm_fourier_eq,
    integral_norm_sq_toLp h2]

end NField.Alignment.DirichletParseval
