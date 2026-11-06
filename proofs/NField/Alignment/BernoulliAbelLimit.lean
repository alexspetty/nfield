/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BernoulliAbelSeries

/-! # Symmetric Abel summation with the exact midpoint convention -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BernoulliAbelLimit
open scoped Topology
open Filter Complex BernoulliAbelPhase BernoulliAbelSeries CollisionDedekindPairing

theorem abel_noninteger_limit {y : ℝ} (hy : Int.fract y ≠ 0) :
    Tendsto (fun ρ : ℝ => ∑' j : ℤ, abelTerm ρ y j) (𝓝[<] 1)
      (𝓝 (periodicSawtooth y : ℂ)) := by
  have hu : 0 < Int.fract y := lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm hy)
  have hu1 := Int.fract_lt_one y
  have hs : 1-unitPhase y ∈ slitPlane := by
    rw [← unitPhase_fract y]
    exact phase_slitPlane hu hu1
  have hc : Continuous (fun ρ : ℝ => 1-(ρ : ℂ)*unitPhase y) := by fun_prop
  have ht : Tendsto (fun ρ : ℝ => 1-(ρ : ℂ)*unitPhase y) (𝓝[<] 1)
      (𝓝 (1-unitPhase y)) := by
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hl := (continuousAt_clog hs).tendsto.comp ht
  have hi := (Complex.continuous_im.tendsto (log (1-unitPhase y))).comp hl
  have hreal := hi.neg.div_const Real.pi
  have hcomplex := (Complex.continuous_ofReal.tendsto
    (-(log (1-unitPhase y)).im/Real.pi)).comp hreal
  have he : ((-(log (1-unitPhase y)).im/Real.pi : ℝ) : ℂ) = (periodicSawtooth y : ℂ) := by
    rw [← unitPhase_fract y,phase_log_im hu hu1]
    unfold periodicSawtooth
    rw [if_neg hy]
    congr 1
    field_simp [Real.pi_ne_zero]
    ring
  rw [he] at hcomplex
  apply hcomplex.congr'
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,self_mem_nhdsWithin] with ρ hρ0 hρ1
  exact (abel_tsum hρ0.le hρ1 y).symm

theorem abel_integer_value {y : ℝ} (hy : Int.fract y=0) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑' j : ℤ, abelTerm ρ y j)=0 := by
  have hp : unitPhase y=1 := by rw [← unitPhase_fract y,hy]; simp [unitPhase]
  rw [abel_tsum hρ0 hρ1 y,hp,mul_one]
  rw [show (1 : ℂ)-(ρ : ℂ)=((1-ρ : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (by linarith : 0 ≤ 1-ρ)]
  simp

/-- Title: `The first Bernoulli Fourier identity by symmetric Abel summation`. -/
theorem bernoulli_one_symmetric_abel (y : ℝ) :
    Tendsto (fun ρ : ℝ => ∑' j : ℤ,
      (ρ : ℂ)^j.natAbs * exp (-2*(Real.pi : ℂ)*I*j*y)/(2*(Real.pi : ℂ)*I*j))
      (𝓝[<] 1) (𝓝 (periodicSawtooth y : ℂ)) := by
  change Tendsto (fun ρ : ℝ => ∑' j : ℤ,abelTerm ρ y j) _ _
  by_cases hy : Int.fract y=0
  · have hz : periodicSawtooth y=0 := by simp [periodicSawtooth,hy]
    rw [hz,Complex.ofReal_zero]
    apply tendsto_const_nhds.congr'
    have hpos : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos,self_mem_nhdsWithin] with ρ hρ0 hρ1
    exact (abel_integer_value hy hρ0.le hρ1).symm
  · exact abel_noninteger_limit hy

end NField.Alignment.BernoulliAbelLimit
