/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.AnalyticLogarithmicMultiplicity

/-! # Continuing a weighted logarithmic identity across its isolated zeros

Multiplying by the finite product clears the actual denominators. The
ordinary analytic identity theorem then transports the equality. Finite
analytic zero orders recover the weighted residue without an assumption
that the denominator is nonvanishing throughout the domain.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.WeightedLogarithmicIdentity
open scoped Topology BigOperators
open Filter Set AnalyticLogarithmicMultiplicity

variable {ι : Type*} [DecidableEq ι]

def product (S : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ) : ℂ := ∏ i ∈ S, f i z

def numerator (S : Finset ι) (f : ι → ℂ → ℂ) (c : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ S, c i * deriv (f i) z * ∏ j ∈ S.erase i, f j z

def weightedLog (S : Finset ι) (f : ι → ℂ → ℂ) (c : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ S, c i * logDeriv (f i) z

theorem clear_denominators (S : Finset ι) (f : ι → ℂ → ℂ) (c : ι → ℂ)
    (z : ℂ) (hn : ∀ i ∈ S, f i z ≠ 0) :
    product S f z * weightedLog S f c z = numerator S f c z := by
  unfold product weightedLog numerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase S (fun j => f j z) hi, logDeriv_apply]
  field_simp [hn i hi]

omit [DecidableEq ι] in
theorem product_analyticOnNhd (S : Finset ι) {f : ι → ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) U) : AnalyticOnNhd ℂ (product S f) U :=
  S.analyticOnNhd_fun_prod hf

theorem numerator_analyticOnNhd (S : Finset ι) {f : ι → ℂ → ℂ} (c : ι → ℂ) {U : Set ℂ}
    (hf : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) U) : AnalyticOnNhd ℂ (numerator S f c) U := by
  apply S.analyticOnNhd_fun_sum
  intro i hi z hz
  exact (analyticAt_const.mul (hf i hi z hz).deriv).mul
    ((S.erase i).analyticAt_fun_prod (fun j hj => hf j (Finset.mem_of_mem_erase hj) z hz))

/-- Title: `A cleared logarithmic identity continues throughout a connected analytic domain`. -/
theorem continue_cleared_identity (S : Finset ι) {f : ι → ℂ → ℂ} (c : ι → ℂ)
    {U : Set ℂ} (_hU : IsOpen U) (hconnected : IsPreconnected U)
    (hf : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) U) {D : ℂ → ℂ} (hD : AnalyticOnNhd ℂ D U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hn : ∀ i ∈ S, f i z₀ ≠ 0)
    (heq : weightedLog S f c =ᶠ[𝓝 z₀] D) :
    EqOn (numerator S f c) (fun z => product S f z * D z) U := by
  have hne : ∀ᶠ z in 𝓝 z₀, ∀ i ∈ S, f i z ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact (hf i hi z₀ hz₀).continuousAt.eventually_ne (hn i hi)
  apply (numerator_analyticOnNhd S c hf).eqOn_of_preconnected_of_eventuallyEq
    ((product_analyticOnNhd S hf).mul hD) hconnected hz₀
  filter_upwards [hne, heq] with z hz he
  rw [← clear_denominators S f c z hz, he]

theorem eventually_nonzero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (horder : analyticOrderAt f z ≠ ⊤) : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  exact hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun h => horder (analyticOrderAt_eq_top.mpr h))

/-- Title: `An analytic weighted logarithmic sum has zero total zero multiplicity`. -/
theorem weighted_order_zero (S : Finset ι) {f : ι → ℂ → ℂ} (c : ι → ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hconnected : IsPreconnected U)
    (hf : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) U) {D : ℂ → ℂ} (hD : AnalyticOnNhd ℂ D U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hn : ∀ i ∈ S, f i z₀ ≠ 0)
    (heq : weightedLog S f c =ᶠ[𝓝 z₀] D) {ρ : ℂ} (hρ : ρ ∈ U)
    (horder : ∀ i ∈ S, analyticOrderAt (f i) ρ ≠ ⊤) :
    (∑ i ∈ S, c i * (analyticOrderNatAt (f i) ρ : ℂ)) = 0 := by
  have hglobal := continue_cleared_identity S c hU hconnected hf hD hz₀ hn heq
  have hne : ∀ᶠ z in 𝓝[≠] ρ, ∀ i ∈ S, f i z ≠ 0 := by
    rw [eventually_all_finset]
    exact fun i hi => eventually_nonzero (hf i hi ρ hρ) (horder i hi)
  have hlocal : weightedLog S f c =ᶠ[𝓝[≠] ρ] D := by
    have hnear : ∀ᶠ z in 𝓝 ρ, z ∈ U := hU.mem_nhds hρ
    filter_upwards [hne, hnear.filter_mono nhdsWithin_le_nhds] with z hnz hz
    have hp : product S f z ≠ 0 := Finset.prod_ne_zero_iff.mpr hnz
    apply mul_left_cancel₀ hp
    rw [clear_denominators S f c z hnz]
    exact hglobal hz
  have hres := tendsto_finsetSum S (fun i hi =>
    (tendsto_mul_logDeriv_order (hf i hi ρ hρ) (horder i hi)).const_mul (c i))
  have hres' : Tendsto (fun z => (z-ρ) * weightedLog S f c z) (𝓝[≠] ρ)
      (𝓝 (∑ i ∈ S, c i * (analyticOrderNatAt (f i) ρ : ℂ))) := by
    convert hres using 1
    funext z
    simp only [weightedLog, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzero : Tendsto (fun z => (z-ρ) * D z) (𝓝[≠] ρ) (𝓝 0) := by
    have hz : Tendsto (fun z : ℂ => z-ρ) (𝓝 ρ) (𝓝 0) := by
      simpa using (continuousAt_id.tendsto : Tendsto (fun z : ℂ => z) (𝓝 ρ) (𝓝 ρ)).sub_const ρ
    simpa using (hz.mul (hD ρ hρ).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hres'
    (hzero.congr' (hlocal.mono (fun z hz => congrArg (fun x => (z-ρ)*x) hz.symm)))

end NField.Alignment.WeightedLogarithmicIdentity
