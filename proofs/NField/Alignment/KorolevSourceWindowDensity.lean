/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSourceWindowCount
import NField.Alignment.KorolevQuadraticWindowDensity
import NField.Alignment.KorolevWindowParameters

/-! # Uniform actual prime populations through the full source-index envelope -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceWindowDensity
open Filter KorolevPrimeWindows KorolevWindowMass KorolevQuadraticWindowDensity
  KorolevSourceEnvelope KorolevSourceScales KorolevWindowParameters KorolevEndpointIndices
open scoped Topology

/-- Every index below the actual source envelope eventually satisfies the population criterion. -/
theorem eventual_envelope_population : ∀ᶠ v : ℝ in atTop,
    ∀ m : ℕ, 0 < m → Real.log m = Real.exp v → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ envelope v →
      lowerEndpoint (Real.exp v) k / (8*(k : ℝ)) ≤
        (((windowPrimes (Real.exp v) k).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [eventual_envelope_small (8*(Real.log 4+1)),
    eventual_envelope_small (16*lossConstant), eventual_envelope_small 36]
    with v hs hf hq m hm hcoord k hk hkenv
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hkenv 2
  have derive (K : ℝ) (hK : 0 ≤ K) (h : K*(envelope v)^2/Real.exp v ≤ 1) :
      K*(k : ℝ)^2 ≤ Real.exp v := by
    exact (mul_le_mul_of_nonneg_left hsq hK).trans
      (by simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos v)).mp h)
  rw [← hcoord]
  apply coprime_window_population_ge_quadratic hm hk
  · have h := derive (8*(Real.log 4+1)) (by positivity) hs
    rw [hcoord]
    nlinarith only [h]
  · rw [hcoord]
    exact derive (16*lossConstant) (mul_nonneg (by norm_num) lossConstant_pos.le) hf
  · rw [hcoord]
    exact derive 36 (by norm_num) hq

/-- The rounded upper source indices, including the endpoint convention, fit the envelope. -/
theorem eventual_index_envelope (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      (pLast v u c : ℝ)+1 ≤ envelope v ∧ (qLast v u c : ℝ)+1 ≤ envelope v := by
  filter_upwards [eventual_scale_bounds c hc] with v hv u hulo hule
  obtain ⟨_, _, hpA, hqA, hR, _, hpB, hqB⟩ := hv u hulo hule
  have hpord : 4*pStart v u c ≤ pStop v u c := by
    rw [pStop_ratio]
    nlinarith
  have hqord : 4*qStart v u c ≤ qStop v u c := by
    rw [qStop_ratio]
    nlinarith
  have hp := rounded_pair_bounds hpA hpord (by norm_num : (1 : ℕ) ≤ 1)
  have hq := rounded_pair_bounds hqA hqord (by norm_num : (0 : ℕ) ≤ 1)
  constructor
  · exact hp.2.2.2.2.trans (by unfold envelope; linarith)
  · exact hq.2.2.2.2.trans (by unfold envelope; linarith)

/-- Actual window populations, uniformly for both complete rounded source-index ranges. -/
theorem eventual_source_population (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      ∀ m : ℕ, 0 < m → Real.log m = Real.exp v → ∀ k : ℕ, 1 ≤ k →
        (k ≤ pLast v u c ∨ k ≤ qLast v u c) →
        lowerEndpoint (Real.exp v) k / (8*(k : ℝ)) ≤
          (((windowPrimes (Real.exp v) k).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [eventual_envelope_population, eventual_index_envelope c hc]
    with v hp hi u hulo hule m hm hcoord k hk hlast
  have hii := hi u hulo hule
  apply hp m hm hcoord k hk
  rcases hlast with h | h
  · have hh : (k : ℝ) ≤ pLast v u c := by exact_mod_cast h
    linarith [hii.1]
  · have hh : (k : ℝ) ≤ qLast v u c := by exact_mod_cast h
    linarith [hii.2]

/-- The separated window sits inside the corresponding full contiguous source interval. -/
theorem window_subset_step {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    windowPrimes L k ⊆ KorolevPrimeIntervals.intervalPrimes
      (upperEndpoint L (k+1)) (upperEndpoint L k) := by
  intro p hp
  obtain ⟨hpp, hlo, hhi⟩ := KorolevPrimeIntervals.intervalPrimes_mem.mp hp
  exact KorolevPrimeIntervals.intervalPrimes_mem.mpr
    ⟨hpp, (successor_separation hL hk).trans hlo, hhi⟩

/-- The full contiguous source step retains at least the separated window population. -/
theorem coprime_step_card_ge_window (m : ℕ) {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    (((windowPrimes L k).filter (fun p => p.Coprime m)).card : ℝ) ≤
      (((KorolevPrimeIntervals.intervalPrimes (upperEndpoint L (k+1))
        (upperEndpoint L k)).filter (fun p => p.Coprime m)).card : ℝ) := by
  exact_mod_cast Finset.card_le_card
    (Finset.filter_subset_filter (fun p => p.Coprime m) (window_subset_step hL hk))

/-- Actual populations in the full contiguous steps, uniformly through both source-index ranges. -/
theorem eventual_source_step_population (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      ∀ m : ℕ, 0 < m → Real.log m = Real.exp v → ∀ k : ℕ, 1 ≤ k →
        (k ≤ pLast v u c ∨ k ≤ qLast v u c) →
        lowerEndpoint (Real.exp v) k / (8*(k : ℝ)) ≤
          (((KorolevPrimeIntervals.intervalPrimes (upperEndpoint (Real.exp v) (k+1))
            (upperEndpoint (Real.exp v) k)).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [eventual_source_population c hc] with v hv u hulo hule m hm hcoord k hk hlast
  exact (hv u hulo hule m hm hcoord k hk hlast).trans
    (coprime_step_card_ge_window m (Real.exp_pos v).le hk)

/-- Actual integer-modulus populations throughout the paper's complete source range. -/
theorem eventual_source_population_nat (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in atTop,
    ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k : ℕ, 1 ≤ k →
        (k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ∨
          k ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)) →
        lowerEndpoint (Real.log m) k / (8*(k : ℝ)) ≤
          (((windowPrimes (Real.log m) k).filter (fun p => p.Coprime m)).card : ℝ) ∧
        lowerEndpoint (Real.log m) k / (8*(k : ℝ)) ≤
          (((KorolevPrimeIntervals.intervalPrimes (upperEndpoint (Real.log m) (k+1))
            (upperEndpoint (Real.log m) k)).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [ht.eventually (eventual_source_population (Real.log C) (Real.log_nonneg hC)),
    ht.eventually (eventual_source_step_population (Real.log C) (Real.log_nonneg hC)),
    hlog.eventually_gt_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with m hp hq hL hm x hlo hhi k hk hlast
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hcoord : Real.log (m : ℝ) = Real.exp (Real.log (Real.log m)) :=
    (Real.exp_log (by linarith : 0 < Real.log (m : ℝ))).symm
  have hp' := hp (Real.log (Real.log x)) hulo hule m hmpos hcoord k hk hlast
  have hq' := hq (Real.log (Real.log x)) hulo hule m hmpos hcoord k hk hlast
  simpa only [Function.comp_apply, ← hcoord] using And.intro hp' hq'

end NField.Alignment.KorolevSourceWindowDensity
