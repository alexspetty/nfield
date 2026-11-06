/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OrdinaryDirichletConvergence
import NField.Alignment.ComplexPrimeCharacterExpansion

/-! # The actual prime collision series as an ordinary Dirichlet series -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.OrdinaryCollisionPrimeSeries
open scoped Topology BigOperators
open Filter Set OrdinaryDirichletKernel OrdinaryDirichletConvergence
open CollisionCharacterStructure PrimePeriodicLimits ComplexPrimeCharacterExpansion

def naturalTerm {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) (c : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if n.Prime ∧ c < n then unitExtension F n * (n : ℂ) ^ (-s) else 0

def coefficients {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) (c n : ℕ) : ℂ :=
  if (n+1).Prime ∧ c < n+1 then unitExtension F (n+1) else 0

theorem ordinary_term_eq {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) (c : ℕ) (s : ℂ) (n : ℕ) :
    term (coefficients F c) s n = naturalTerm F c s (n+1) := by
  simp only [term, coefficients, weight, naturalTerm]
  split_ifs <;> simp

theorem naturalTerm_hasSum {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (c : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (naturalTerm F c s) (periodicPrimeSeries F c s) := by
  have hp : HasSum (fun p : Nat.Primes => naturalTerm F c s p) (periodicPrimeSeries F c s) := by
    simpa only [naturalTerm, Subtype.property, true_and, periodicPrimeTerm, periodicPrimeSeries] using
      (periodicPrimeSeries_summable F c hs).hasSum
  apply (hasSum_subtype_iff_of_support_subset (f := naturalTerm F c s)
    (s := {n : ℕ | n.Prime}) ?_).mp hp
  intro n hn
  by_contra hprime
  change ¬n.Prime at hprime
  have hz : naturalTerm F c s n = 0 := by simp [naturalTerm, hprime]
  exact hn hz

/-- Title: `Ordered prime partial sums agree with the actual prime series above one`. -/
theorem ordinary_limit_above_one {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (c : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (sums (coefficients F c) s) atTop (𝓝 (periodicPrimeSeries F c s)) := by
  have hnat := naturalTerm_hasSum F c hs
  have hshift := (hasSum_nat_add_iff' (f := naturalTerm F c s) 1).mpr hnat
  have hz : (∑ i ∈ Finset.range 1, naturalTerm F c s i) = 0 := by simp [naturalTerm]
  rw [hz, sub_zero] at hshift
  change Tendsto (fun N => ∑ n ∈ Finset.range N, term (coefficients F c) s n) atTop _
  simpa only [ordinary_term_eq] using hshift.tendsto_sum_nat

/-- Title: `One ordinary prime convergence point supplies the analytic collision sum`. -/
theorem analytic_model_of_convergence {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (c : ℕ) {σ : ℝ} {l : ℂ}
    (h : Tendsto (sums (coefficients F c) (σ : ℂ)) atTop (𝓝 l)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | σ < s.re} ∧
      (∀ s : ℂ, σ < s.re → Tendsto (sums (coefficients F c) s) atTop (𝓝 (G s))) ∧
      EqOn G (periodicPrimeSeries F c) {s : ℂ | max σ 1 < s.re} := by
  obtain ⟨G, hG, hlim, _⟩ := holomorphic_of_ordinary_convergence h
  refine ⟨G, hG, hlim, ?_⟩
  intro s hs
  change max σ 1 < s.re at hs
  exact tendsto_nhds_unique (hlim s ((le_max_left _ _).trans_lt hs))
    (ordinary_limit_above_one F c ((le_max_right _ _).trans_lt hs))

end NField.Alignment.OrdinaryCollisionPrimeSeries
