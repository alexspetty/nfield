/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHolomorphicContinuation
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv

/-! # Actual zero multiplicities in logarithmic derivatives -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.AnalyticLogarithmicMultiplicity

open scoped Topology BigOperators
open Filter Set
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionHolomorphicContinuation
open NField.Alignment.PrimeEulerLog

/-- Title: `The logarithmic residue is the actual analytic zero multiplicity`. -/
theorem tendsto_mul_logDeriv_order {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hfinite : analyticOrderAt f ρ ≠ ⊤) :
    Tendsto (fun z => (z - ρ) * logDeriv f z) (𝓝[≠] ρ)
      (𝓝 (analyticOrderNatAt f ρ : ℂ)) := by
  obtain ⟨g, hg, hg0, heq⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  simp only [smul_eq_mul] at heq
  let n := analyticOrderNatAt f ρ
  have hne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hdiff : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono (fun _ h => h.differentiableAt)
  have hlocal : ∀ᶠ z in 𝓝[≠] ρ,
      (z - ρ) * logDeriv f z = (n : ℂ) + (z - ρ) * logDeriv g z := by
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
      heq.deriv.filter_mono nhdsWithin_le_nhds, hne.filter_mono nhdsWithin_le_nhds,
      hdiff.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hdz hgz hdg hzρ
    have hz0 : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    have hlin : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
    have hreplace : logDeriv f z = logDeriv (fun w => (w - ρ) ^ n * g w) z := by
      simp only [logDeriv_apply, hz, hdz, n]
    rw [hreplace, logDeriv_mul (f := fun w => (w - ρ) ^ n) (g := g)
      z (pow_ne_zero n hz0) hgz (hlin.differentiableAt.pow n) hdg,
      logDeriv_fun_pow hlin.differentiableAt n]
    have hbase : logDeriv (fun w : ℂ => w - ρ) z = 1 / (z - ρ) := by
      rw [logDeriv_apply, hlin.deriv]
    rw [hbase]
    field_simp [hz0]
    <;> ring
  have hcontinuous : ContinuousAt (logDeriv g) ρ :=
    hg.deriv.continuousAt.div hg.continuousAt hg0
  have hlimit : Tendsto (fun z : ℂ => (n : ℂ) + (z - ρ) * logDeriv g z)
      (𝓝 ρ) (𝓝 (n : ℂ)) := by
    have hzero : Tendsto (fun z : ℂ => z - ρ) (𝓝 ρ) (𝓝 0) := by
      simpa using (tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 ρ) (𝓝 ρ)).sub_const ρ
    simpa using (hzero.mul hcontinuous.tendsto).const_add (n : ℂ)
  exact (hlimit.mono_left nhdsWithin_le_nhds).congr' (hlocal.mono (fun _ h => h.symm))

theorem nonprincipal_LFunction_order_finite {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
  have htwo : χ.LFunction 2 ≠ 0 := by
    rw [← exp_eulerLog_eq_LFunction χ (by norm_num : 1 < (2 : ℂ).re)]
    exact Complex.exp_ne_zero _
  have horder : analyticOrderAt χ.LFunction (2 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr htwo)]
    exact ENat.zero_ne_top
  exact (LFunction_analyticOnNhd hχ univ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ 2) (mem_univ ρ) horder

/-- Title: `The logarithmic residue of a nonprincipal L-function equals its zero multiplicity`. -/
theorem LFunction_logarithmic_residue {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (ρ : ℂ) :
    Tendsto (fun z => (z - ρ) * logDeriv χ.LFunction z) (𝓝[≠] ρ)
      (𝓝 (analyticOrderNatAt χ.LFunction ρ : ℂ)) :=
  tendsto_mul_logDeriv_order (LFunction_analyticOnNhd hχ univ ρ (mem_univ ρ))
    (nonprincipal_LFunction_order_finite hχ ρ)

/-- Title: `The collision zero ledger is the actual weighted logarithmic residue`. -/
theorem collision_ledger_is_logarithmic_residue {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (hprincipal : collisionCoefficient F 1 = 0) (ρ : ℂ) :
    Tendsto (fun z => (z - ρ) * ∑ χ ∈ activeCharacters F,
      collisionCoefficient F χ * logDeriv χ.LFunction z) (𝓝[≠] ρ)
      (𝓝 (collisionZeroLedger F (fun χ => analyticOrderNatAt χ.LFunction ρ))) := by
  classical
  have h := tendsto_finsetSum (activeCharacters F) (fun χ hχ =>
    (LFunction_logarithmic_residue (active_ne_one hprincipal hχ) ρ).const_mul
      (collisionCoefficient F χ))
  change Tendsto _ _ (𝓝 (∑ χ ∈ activeCharacters F,
    collisionCoefficient F χ * (analyticOrderNatAt χ.LFunction ρ : ℂ)))
  convert h using 1
  funext z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

end NField.Alignment.AnalyticLogarithmicMultiplicity
