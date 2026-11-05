/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDirichletBoundary
import NField.Alignment.CollisionHarmonicInterior

/-!
# The ordered harmonic-weight boundary series

Dirichlet convergence of the decreasing harmonic coefficients is followed
by Abel's radial limit theorem. The endpoint is the actual principal-log
square obtained from the interior Cauchy product.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicAbelBoundary

open scoped BigOperators Topology
open Filter Finset
open CollisionDirichletBoundary CollisionHarmonicCoefficients CollisionHarmonicInterior

theorem one_sub_unit_root_mem_slitPlane
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  change 0 < 1 - z.re
  have hrele : z.re ≤ 1 := by
    calc
      z.re ≤ ‖z‖ := Complex.re_le_norm z
      _ = 1 := hzNorm
  have hrene : z.re ≠ 1 := by
    intro hre
    have hsq := Complex.sq_norm z
    rw [hzNorm, Complex.normSq_apply, hre] at hsq
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    apply hz
    apply Complex.ext
    · simpa using hre
    · simpa using him
  have hrelt : z.re < 1 := lt_of_le_of_ne hrele hrene
  linarith


theorem harmonic_dirichlet_tendsto {z : ℂ} (hzNorm : ‖z‖=1) (hz : z≠1) :
    Tendsto (fun n => dirichletPartial shiftedHarmonicFirst n z) atTop
      (𝓝 (Complex.log (1-z)^2/(2*z))) := by
  have hz0 : z≠0 := by
    intro heq
    rw [heq,norm_zero] at hzNorm
    norm_num at hzNorm
  have hc := dirichletPartial_cauchy shiftedHarmonicFirst_antitone
    shiftedHarmonicFirst_tendsto_zero hzNorm hz
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hc
  have hAbel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL
  let F : ℂ → ℂ := fun w => ∑' n : ℕ,
    ((shiftedHarmonicFirst n : ℂ)*z^(n+1))*w^n
  let G : ℂ → ℂ := fun w => Complex.log (1-z*w)^2/(2*z*w^2)
  have hFG : F=ᶠ[((𝓝[<] (1 : ℝ)).map Complex.ofReal)] G := by
    change ∀ᶠ w in ((𝓝[<] (1 : ℝ)).map Complex.ofReal), F w=G w
    rw [Filter.eventually_map]
    have hlt : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r<1 := self_mem_nhdsWithin
    have hpos : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0<r :=
      (eventually_gt_nhds zero_lt_one).filter_mono inf_le_left
    filter_upwards [hlt,hpos] with r hrlt hrpos
    have hr0 : (r : ℂ)≠0 := by exact_mod_cast hrpos.ne'
    have hur : ‖z*(r : ℂ)‖<1 := by
      rw [norm_mul,hzNorm,one_mul,Complex.norm_real,Real.norm_of_nonneg hrpos.le]
      exact hrlt
    have hGseries : G (r : ℂ)=(∑' n, harmonicDerivativeTerm (z*(r : ℂ)) n)/(r : ℂ) := by
      rw [(harmonicDerivativeTerm_hasSum hur).tsum_eq]
      dsimp [G]
      field_simp
    rw [hGseries,← tsum_div_const]
    unfold F
    apply tsum_congr
    intro n
    unfold harmonicDerivativeTerm
    rw [mul_pow,pow_succ (r : ℂ)]
    field_simp
  have hG : Tendsto G (((𝓝[<] (1 : ℝ)).map Complex.ofReal))
      (𝓝 (Complex.log (1-z)^2/(2*z))) := by
    rw [Filter.tendsto_map'_iff]
    have hinner : ContinuousAt (fun w : ℂ => 1-z*w) 1 := by fun_prop
    have hmem : 1-z*(1 : ℂ)∈Complex.slitPlane := by
      simpa using one_sub_unit_root_mem_slitPlane hzNorm hz
    have hlog : ContinuousAt (fun w : ℂ => Complex.log (1-z*w)) 1 := hinner.clog hmem
    have hquot : ContinuousAt G 1 := by
      apply (hlog.pow 2).div (by fun_prop)
      simp [hz0]
    have hofReal : Tendsto Complex.ofReal (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left inf_le_left
    simpa [G] using hquot.tendsto.comp hofReal
  have hAbelF : Tendsto F (((𝓝[<] (1 : ℝ)).map Complex.ofReal)) (𝓝 L) := by
    simpa [F,dirichletPartial] using hAbel
  have hEq : L=Complex.log (1-z)^2/(2*z) :=
    tendsto_nhds_unique (hAbelF.congr' hFG) hG
  simpa [hEq] using hL

end NField.Alignment.CollisionHarmonicAbelBoundary
