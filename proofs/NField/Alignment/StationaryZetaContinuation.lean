/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryEulerZeta
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Continuation of the actual Euler formula to a neighborhood of zero -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryZetaContinuation
open Set Filter Complex StationaryEulerZeta

def upperRegion : Set ℂ := {s | -1 < s.re ∧ 0 < s.im}
def centralStrip : Set ℂ := {s | -1 < s.re ∧ s.re < 1}

theorem upperRegion_open : IsOpen upperRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem centralStrip_open : IsOpen centralStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem upperRegion_preconnected : IsPreconnected upperRegion :=
  ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_gt 0)).isPreconnected

theorem centralStrip_preconnected : IsPreconnected centralStrip :=
  ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt 1)).isPreconnected

theorem eulerZeta_eq_upper : EqOn eulerZeta riemannZeta upperRegion := by
  have hn {s : ℂ} (hs : s ∈ upperRegion) : s ≠ 1 := by
    intro h
    have hi := hs.2
    simp [h] at hi
  have hf : AnalyticOnNhd ℂ eulerZeta upperRegion :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (eulerZeta_differentiableAt hs.1 (hn hs)).differentiableWithinAt)
      upperRegion_open
  have hg : AnalyticOnNhd ℂ riemannZeta upperRegion :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hn hs)).differentiableWithinAt)
      upperRegion_open
  have hp : (2 + I : ℂ) ∈ upperRegion := by norm_num [upperRegion]
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg upperRegion_preconnected hp
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 < (2 + I : ℂ).re by norm_num)] with s hs
  exact eulerZeta_eq_riemannZeta hs

/-- Title: `The actual zeta function equals its Bernoulli Euler continuation near zero`. -/
theorem eulerZeta_eq_centralStrip : EqOn eulerZeta riemannZeta centralStrip := by
  have hn {s : ℂ} (hs : s ∈ centralStrip) : s ≠ 1 := by
    intro h
    have hr := hs.2
    simp [h] at hr
  have hf : AnalyticOnNhd ℂ eulerZeta centralStrip :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (eulerZeta_differentiableAt hs.1 (hn hs)).differentiableWithinAt)
      centralStrip_open
  have hg : AnalyticOnNhd ℂ riemannZeta centralStrip :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hn hs)).differentiableWithinAt)
      centralStrip_open
  have hp : I ∈ centralStrip := by norm_num [centralStrip]
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg centralStrip_preconnected hp
  filter_upwards [upperRegion_open.mem_nhds (show I ∈ upperRegion by norm_num [upperRegion])]
    with s hs
  exact eulerZeta_eq_upper hs

theorem eulerZeta_eventually_eq_riemannZeta : eulerZeta =ᶠ[nhds 0] riemannZeta := by
  filter_upwards [centralStrip_open.mem_nhds (show (0 : ℂ) ∈ centralStrip by norm_num [centralStrip])]
    with s hs
  exact eulerZeta_eq_centralStrip hs

end NField.Alignment.StationaryZetaContinuation
