/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionActivationArithmetic

/-!
# Transfer of uniform concentration through an almost-everywhere limit

The target closed interval is enlarged strictly inside the available edge
increment before taking the limit. Continuity from below controls the sets
of points whose entire remaining sequence lies in that enlargement.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConcentrationLimit

open scoped ENNReal Classical
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionActivationArithmetic

theorem measure_eventually_membership_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (B : ℕ → Set Ω) {C : ℝ≥0∞}
    (hA : ∀ᵐ x ∂μ, x∈A → ∀ᶠ n in atTop, x∈B n)
    (hB : ∀ᶠ n in atTop, μ (B n)≤C) : μ A≤C := by
  let T : ℕ → Set Ω := fun N => {x | ∀ n, N≤n → x∈B n}
  have hT : Monotone T := by
    intro N M hNM x hx n hn
    exact hx n (hNM.trans hn)
  have hsub : A≤ᵐ[μ] ⋃ N, T N := by
    filter_upwards [hA] with x hx
    intro hxA
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hx hxA)
    exact Set.mem_iUnion.mpr ⟨N,hN⟩
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hB
  calc
    μ A ≤ μ (⋃ N, T N) := measure_mono_ae hsub
    _ = ⨆ N, μ (T N) := hT.measure_iUnion
    _ ≤ C := by
      apply iSup_le
      intro N
      exact (measure_mono (show T N⊆B (max N N0) from fun x hx =>
        hx _ (le_max_left N N0))).trans (hN0 _ (le_max_right N N0))

theorem closed_interval_limit_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    {u v δ C : ℝ} (hδ : 0<δ) (hC : 0≤C)
    (hb : ∀ᶠ n in atTop, μ.real {x | f n x∈Set.Icc (u-δ) (v+δ)}≤C) :
    μ.real {x | g x∈Set.Icc u v}≤C := by
  have he : ∀ᵐ x ∂μ, g x∈Set.Icc u v →
      ∀ᶠ n in atTop, f n x∈Set.Icc (u-δ) (v+δ) := by
    filter_upwards [hlim] with x hx
    intro hg
    have hlo : u-δ<g x := by linarith [hg.1]
    have hhi : g x<v+δ := by linarith [hg.2]
    filter_upwards [(tendsto_order.mp hx).1 _ hlo,(tendsto_order.mp hx).2 _ hhi] with n hn hn'
    exact ⟨hn.le,hn'.le⟩
  have hb' : ∀ᶠ n in atTop, μ {x | f n x∈Set.Icc (u-δ) (v+δ)}≤ENNReal.ofReal C := by
    filter_upwards [hb] with n hn
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC).mpr hn
  have ht := measure_eventually_membership_le μ {x | g x∈Set.Icc u v}
    (fun n => {x | f n x∈Set.Icc (u-δ) (v+δ)}) he hb'
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC).mp ht

theorem forcingBlock_limit_concentration (h : ℕ) {a C : ℝ} (hC : 0≤C)
    (hb : ∀ u v : ℝ, v-u<a → ∀ᶠ M : ℕ in atTop,
      phaseHaar.real {x | forcingCutoff h M x∈Set.Icc u v}≤C)
    {u v : ℝ} (huv : v-u<a) :
    phaseHaar.real {x | forcingBlock h x∈Set.Icc u v}≤C := by
  let δ : ℝ := (a-(v-u))/4
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hw : (v+δ)-(u-δ)<a := by dsimp [δ]; linarith
  apply closed_interval_limit_bound phaseHaar (forcingCutoff h) (forcingBlock h) _ hδ hC
    (hb (u-δ) (v+δ) hw)
  filter_upwards [blockResetSummable_ae h] with x hx
  exact forcingCutoff_tendsto h x hx

end NField.Alignment.CollisionConcentrationLimit
