/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OrdinaryCollisionPrimeSeries
import NField.Alignment.WeightedLogarithmicIdentity
import Mathlib.Analysis.Complex.Convex

/-! # The actual collision zero ledger forced by ordinary convergence -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionZeroObstruction
open scoped Topology BigOperators
open Filter Set
open CollisionCharacterStructure CollisionTransformStrip PrimeEulerLog
open ComplexPrimeCharacterExpansion CollisionHolomorphicContinuation HolomorphicLogBranch
open OrdinaryDirichletConvergence OrdinaryCollisionPrimeSeries
open WeightedLogarithmicIdentity AnalyticLogarithmicMultiplicity

theorem eulerLog_deriv {q : ℕ} [NeZero q] (χ : Character q) {s : ℂ} (hs : 1 < s.re) :
    deriv (eulerLog χ) s = logDeriv χ.LFunction s :=
  log_branch_derivative (isOpen_lt continuous_const Complex.continuous_re)
    (eulerLog_analyticOnNhd χ).differentiableOn
    (fun _ hz => exp_eulerLog_eq_LFunction χ hz) hs

def eulerSum {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) (s : ℂ) : ℂ :=
  ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * eulerLog χ s

def higherSum {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) (s : ℂ) : ℂ :=
  ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * higherPowerSum χ s

theorem eulerSum_deriv {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) {s : ℂ} (hs : 1 < s.re) :
    deriv (eulerSum F) s = weightedLog (activeCharacters F) (fun χ => χ.LFunction)
      (collisionCoefficient F) s := by
  classical
  have hd := HasDerivAt.fun_sum (u := activeCharacters F) (fun χ _ =>
    ((eulerLog_analyticOnNhd χ s hs).differentiableAt.hasDerivAt).const_mul (collisionCoefficient F χ))
  change deriv (fun z => ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * eulerLog χ z) s = _
  simpa only [eulerSum, weightedLog, eulerLog_deriv _ hs] using hd.deriv

/-- Title: `Ordinary collision convergence forces the actual weighted zero ledger to vanish`. -/
theorem ordinary_convergence_zero_ledger {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (c : ℕ) (hprincipal : collisionCoefficient F 1 = 0)
    {σ : ℝ} (hσ : (1/2 : ℝ) ≤ σ) {l : ℂ}
    (hconv : Tendsto (sums (coefficients F c) (σ : ℂ)) atTop (𝓝 l))
    {ρ : ℂ} (hρ : σ < ρ.re) :
    collisionZeroLedger F (fun χ => analyticOrderNatAt χ.LFunction ρ) = 0 := by
  classical
  obtain ⟨G, hG, _, hGseries⟩ := analytic_model_of_convergence F c hconv
  let U : Set ℂ := {s : ℂ | σ < s.re}
  let V : Set ℂ := {s : ℂ | max σ 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hhalf : U ⊆ {s : ℂ | (1/2 : ℝ) < s.re} := fun s hs => hσ.trans_lt hs
  have hH : AnalyticOnNhd ℂ (higherSum F) U :=
    (activeCharacters F).analyticOnNhd_fun_sum (fun χ _ =>
      analyticOnNhd_const.mul ((higherPower_analyticOnNhd χ).mono hhalf))
  have hE : AnalyticOnNhd ℂ (finiteCorrection F c) U :=
    ((finiteCorrection_differentiable F c).differentiableOn.analyticOnNhd isOpen_univ).mono
      (subset_univ U)
  let Q : ℂ → ℂ := fun s => G s + higherSum F s + finiteCorrection F c s
  have hQ : AnalyticOnNhd ℂ Q U := (hG.add hH).add hE
  have hQeuler : EqOn Q (eulerSum F) V := by
    intro s hs
    have hs1 : 1 < s.re := (le_max_right _ _).trans_lt hs
    have hgs := hGseries hs
    rw [periodicPrimeSeries_euler_expansion F c hs1] at hgs
    dsimp only [Q, eulerSum, higherSum]
    linear_combination hgs
  have hderiv : EqOn (weightedLog (activeCharacters F) (fun χ => χ.LFunction)
      (collisionCoefficient F)) (deriv Q) V := by
    intro s hs
    have he : Q =ᶠ[𝓝 s] eulerSum F := by
      filter_upwards [hV.mem_nhds hs] with z hz
      exact hQeuler hz
    rw [he.deriv.eq_of_nhds, eulerSum_deriv F ((le_max_right _ _).trans_lt hs)]
  let z₀ : ℂ := (max σ 1 + 1 : ℝ)
  have hzV : z₀ ∈ V := by
    change max σ 1 < ((max σ 1 + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  have hzU : z₀ ∈ U := by
    change σ < z₀.re
    exact (le_max_left σ 1).trans_lt hzV
  have hlocal : weightedLog (activeCharacters F) (fun χ => χ.LFunction) (collisionCoefficient F)
      =ᶠ[𝓝 z₀] deriv Q := by
    filter_upwards [hV.mem_nhds hzV] with z hz
    exact hderiv hz
  have hresult := weighted_order_zero (activeCharacters F) (collisionCoefficient F) hU
    (convex_halfSpace_re_gt σ).isPreconnected
    (fun χ hχ => LFunction_analyticOnNhd (active_ne_one hprincipal hχ) U)
    (fun z hz => (hQ z hz).deriv) hzU
    (fun χ _ => by
      rw [← exp_eulerLog_eq_LFunction χ ((le_max_right _ _).trans_lt hzV)]
      exact Complex.exp_ne_zero _) hlocal hρ
    (fun χ hχ => nonprincipal_LFunction_order_finite (active_ne_one hprincipal hχ) ρ)
  exact hresult

end NField.Alignment.CollisionZeroObstruction
