/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ComplexPrimeCharacterExpansion
import NField.Alignment.HolomorphicLogBranch

/-! # Continuation of the actual collision series on zero-free domains -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHolomorphicContinuation

open scoped BigOperators
open Set
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.PrimeEulerLog
open NField.Alignment.ComplexPrimeCharacterExpansion
open NField.Alignment.HolomorphicLogBranch

theorem active_ne_one {q : ℕ} [NeZero q] {F : UnitClass q → ℂ}
    (hprincipal : collisionCoefficient F 1 = 0) {χ : Character q}
    (hχ : χ ∈ activeCharacters F) : χ ≠ 1 := by
  classical
  intro heq
  subst χ
  exact (Finset.mem_filter.mp hχ).2 hprincipal

theorem LFunction_analyticOnNhd {q : ℕ} [NeZero q] {χ : Character q}
    (hχ : χ ≠ 1) (U : Set ℂ) : AnalyticOnNhd ℂ χ.LFunction U := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
    isOpen_univ).mono (subset_univ U)

/-- Title: `The collision prime series continues holomorphically on a simply connected active zero-free domain`. -/
theorem exists_collision_continuation {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (c : ℕ) (hprincipal : collisionCoefficient F 1 = 0)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hhalf : U ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re})
    (hconnected : IsPreconnected (U ∩ {s : ℂ | 1 < s.re}))
    (hmeets : (U ∩ {s : ℂ | 1 < s.re}).Nonempty)
    (hzero : ∀ χ ∈ activeCharacters F, ∀ s ∈ U, χ.LFunction s ≠ 0) :
    ∃ T : ℂ → ℂ, AnalyticOnNhd ℂ T U ∧
      EqOn T (periodicPrimeSeries F c) (U ∩ {s : ℂ | 1 < s.re}) := by
  classical
  let V : Set ℂ := U ∩ {s : ℂ | 1 < s.re}
  have hVo : IsOpen V := hU.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hVU : V ⊆ U := inter_subset_left
  have hbranches (χ : Character q) : ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g U ∧
      (χ ∈ activeCharacters F → EqOn g (eulerLog χ) V) := by
    by_cases hχ : χ ∈ activeCharacters F
    · obtain ⟨g, hg, _, heq⟩ := exists_analytic_log_branch_extending hUc hU hVo hVU
        hconnected hmeets (LFunction_analyticOnNhd (active_ne_one hprincipal hχ) U)
        (hzero χ hχ) ((eulerLog_analyticOnNhd χ).mono inter_subset_right)
        (fun s hs => exp_eulerLog_eq_LFunction χ hs.2)
      exact ⟨g, hg, fun _ => heq⟩
    · exact ⟨fun _ => 0, analyticOnNhd_const, fun h => (hχ h).elim⟩
  choose g hg heq using hbranches
  let T : ℂ → ℂ := fun s =>
    (∑ χ ∈ activeCharacters F, collisionCoefficient F χ * g χ s) -
    (∑ χ ∈ activeCharacters F, collisionCoefficient F χ * higherPowerSum χ s) -
    finiteCorrection F c s
  have hfirst : AnalyticOnNhd ℂ
      (fun s => ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * g χ s) U := by
    exact (activeCharacters F).analyticOnNhd_fun_sum
      (fun χ _ => analyticOnNhd_const.mul (hg χ))
  have hsecond : AnalyticOnNhd ℂ
      (fun s => ∑ χ ∈ activeCharacters F, collisionCoefficient F χ * higherPowerSum χ s) U := by
    exact (activeCharacters F).analyticOnNhd_fun_sum
      (fun χ _ => analyticOnNhd_const.mul ((higherPower_analyticOnNhd χ).mono hhalf))
  have hfinite : AnalyticOnNhd ℂ (finiteCorrection F c) U :=
    ((finiteCorrection_differentiable F c).differentiableOn.analyticOnNhd isOpen_univ).mono
      (subset_univ U)
  refine ⟨T, (hfirst.sub hsecond).sub hfinite, ?_⟩
  intro s hs
  change T s = periodicPrimeSeries F c s
  rw [periodicPrimeSeries_euler_expansion F c hs.2]
  dsimp [T]
  congr 2
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [heq χ hχ hs]

end NField.Alignment.CollisionHolomorphicContinuation
