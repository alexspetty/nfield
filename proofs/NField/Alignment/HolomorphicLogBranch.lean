/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Holomorphic logarithm branches from Mathlib's continuous lifting theorem -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HolomorphicLogBranch

open scoped Topology
open Complex Filter Set

theorem continuous_exp_lift_differentiableOn {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : ContinuousOn f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ z ∈ U, Complex.exp (f z) = g z) : DifferentiableOn ℂ f U := by
  intro z hz
  have hc : ContinuousAt f z := (hf z hz).continuousAt (hU.mem_nhds hz)
  have hd := (Complex.hasStrictDerivAt_exp (f z))
  let inv := hd.localInverse Complex.exp (Complex.exp (f z)) (f z) (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (g z) := by
    rw [← he z hz]
    exact (hd.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have hleft : ∀ᶠ w in 𝓝 (f z), inv (Complex.exp w) = w :=
    hd.eventually_left_inverse (Complex.exp_ne_zero _)
  have heq : f =ᶠ[𝓝 z] fun w => inv (g w) := by
    filter_upwards [hc hleft, hU.mem_nhds hz] with w hw hwU
    rw [← he w hwU]
    exact hw.symm
  exact ((hi.comp z ((hg z hz).differentiableAt (hU.mem_nhds hz))).congr_of_eventuallyEq
    heq).differentiableWithinAt

/-- Title: `A nonvanishing holomorphic function has a holomorphic logarithm on a simply connected domain`. -/
theorem exists_analytic_log_branch {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hzero : ∀ z ∈ U, g z ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ ∀ z ∈ U, Complex.exp (f z) = g z := by
  have hz : 0 ∉ g '' U := by
    rintro ⟨z, hz, heq⟩
    exact hzero z hz heq
  obtain ⟨f, hfc, hfe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hU hg.continuousOn hz
  have he : ∀ z ∈ U, Complex.exp (f z) = g z := fun z hz => hfe hz
  exact ⟨f, (continuous_exp_lift_differentiableOn hU hfc hg.differentiableOn he).analyticOnNhd hU, he⟩

theorem log_branch_derivative {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (he : ∀ z ∈ U, Complex.exp (f z) = g z) {z : ℂ} (hz : z ∈ U) :
    deriv f z = logDeriv g z := by
  have hd := ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt.cexp
  have heq : g =ᶠ[𝓝 z] fun w => Complex.exp (f w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he w hw).symm
  have hderiv := (hd.congr_of_eventuallyEq heq).deriv
  have hn : g z ≠ 0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
  rw [logDeriv_apply, eq_div_iff hn]
  rw [← he z hz]
  simpa only [mul_comm] using hderiv.symm

theorem log_branches_eqOn_of_agree {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f g L : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hef : ∀ z ∈ U, Complex.exp (f z) = L z)
    (heg : ∀ z ∈ U, Complex.exp (g z) = L z)
    {z : ℂ} (hz : z ∈ U) (heq : f z = g z) : EqOn f g U := by
  apply hU.eqOn_of_deriv_eq hUc hf.differentiableOn hg.differentiableOn ?_ hz heq
  intro w hw
  rw [log_branch_derivative hU hf.differentiableOn hef hw,
    log_branch_derivative hU hg.differentiableOn heg hw]

/-- Choose the logarithm branch that agrees with a given branch on a connected overlap. -/
theorem exists_analytic_log_branch_extending {U V : Set ℂ}
    (hUc : IsSimplyConnected U) (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    {L f : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U) (hzero : ∀ z ∈ U, L z ≠ 0)
    (hf : AnalyticOnNhd ℂ f V) (hef : ∀ z ∈ V, Complex.exp (f z) = L z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, Complex.exp (g z) = L z) ∧ EqOn g f V := by
  obtain ⟨g, hg, heg⟩ := exists_analytic_log_branch hUc hU hL hzero
  obtain ⟨z, hz⟩ := hVne
  let c := g z - f z
  have hc : Complex.exp c = 1 := by
    rw [Complex.exp_sub, heg z (hVU hz), hef z hz, div_self (hzero z (hVU hz))]
  let g' := fun w => g w - c
  have hg' : AnalyticOnNhd ℂ g' U := hg.sub analyticOnNhd_const
  have heg' : ∀ w ∈ U, Complex.exp (g' w) = L w := by
    intro w hw
    change Complex.exp (g w - c) = L w
    rw [Complex.exp_sub, heg w hw, hc, div_one]
  refine ⟨g', hg', heg', ?_⟩
  apply log_branches_eqOn_of_agree hV hVc (hg'.mono hVU) hf
    (fun w hw => heg' w (hVU hw)) hef hz
  dsimp [g', c]
  ring

end NField.Alignment.HolomorphicLogBranch
