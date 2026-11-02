/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSourceWindowCount

/-!
# Selected primes are large and distinct

The q start scale is exactly eight times the square of the p stop scale.
This separates the actual rounded prime families. The common index
bound also puts the bottom q endpoint above log(m), hence above log(x).
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevPrimeSeparation
open Filter KorolevSourceScales KorolevSourceEnvelope KorolevEndpointIndices
  KorolevWindowParameters KorolevPrimeWindows KorolevParameterCount KorolevSourceWindowCount
open scoped Topology

theorem qStart_eq_eight_pStop_sq (v u c : ℝ) : qStart v u c = 8*(pStop v u c)^2 := by
  unfold qStart pStop
  have he : Real.exp (2*v-2*u+8*gain v u c) = (Real.exp (v-u+4*gain v u c))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he]
  ring

theorem index_separation {v u c : ℝ} (hB : 2 ≤ pStop v u c) :
    pLast v u c+1 ≤ qFirst v u c := by
  have hp := (upperIndex_bounds hB (by norm_num : (1 : ℕ) ≤ 1)).2
  have hq := (lowerIndex_bounds (by unfold qStart; positivity : 0 ≤ qStart v u c)).1
  norm_num only [Nat.cast_one] at hp
  have hh : (pLast v u c : ℝ)+1 ≤ qFirst v u c := by
    change (upperIndex (pStop v u c) 1 : ℝ)+1 ≤ lowerIndex (qStart v u c)
    have hs := qStart_eq_eight_pStop_sq v u c
    nlinarith [sq_nonneg (pStop v u c-1)]
  exact_mod_cast hh

theorem prime_order {v u c : ℝ} (ha : 1 ≤ pFirst v u c)
    (hi : pLast v u c+1 ≤ qFirst v u c) {p q : ℕ}
    (hp : p ∈ pPrimes v u c) (hq : q ∈ qPrimes v u c) : q < p := by
  obtain ⟨k, hak, hkb, _, hpV, _⟩ := (selectedPrimes_mem _ _ _ _).mp hp
  have hqU := (KorolevPrimeIntervals.intervalPrimes_mem.mp hq).2.2
  have hk : 1 ≤ k := ha.trans hak
  have hu := upper_antitone (Real.exp_pos v).le (by omega : 1 ≤ k+1)
    (by omega : k+1 ≤ qFirst v u c)
  have hs := successor_separation (Real.exp_pos v).le hk
  have hh : (q : ℝ) < p := lt_trans (lt_of_le_of_lt (hqU.trans hu) hs) hpV
  exact_mod_cast hh

theorem envelope_endpoint_ratio (v : ℝ) :
    Real.exp v/(2*envelope v) = Real.exp (7*v/12)/8 := by
  unfold envelope
  rw [show 2*(4*Real.exp (5*v/12)) = Real.exp (5*v/12)*8 by ring,
    div_mul_eq_div_div, ← Real.exp_sub]
  congr 2
  ring

theorem eventual_bottom_large : ∀ᶠ v : ℝ in atTop, ∀ b : ℕ,
    (b : ℝ)+1 ≤ envelope v → Real.exp v < upperEndpoint (Real.exp v) (b+1) := by
  have ht := tendsto_exp_mul_div_rpow_atTop 1 (7/12) (by norm_num)
  simp only [Real.rpow_one] at ht
  filter_upwards [ht.eventually_ge_atTop 16, eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop (Real.log 4)] with v hv hv0 hv4 b hb
  have hh := (le_div_iff₀ hv0).mp hv
  rw [show (7/12 : ℝ)*v = 7*v/12 by ring] at hh
  have hd : 0 < 2*((b+1 : ℕ) : ℝ)-1 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have hden : 2*((b+1 : ℕ) : ℝ)-1 ≤ 2*envelope v := by push_cast; linarith
  have hl := div_le_div_of_nonneg_left (Real.exp_pos v).le hd hden
  rw [envelope_endpoint_ratio] at hl
  have hlog : v < Real.log (upperEndpoint (Real.exp v) (b+1)) := by
    rw [log_upper]
    nlinarith
  have he := Real.exp_lt_exp.mpr hlog
  rwa [Real.exp_log (upperEndpoint_pos _ _)] at he

theorem eventual_prime_properties (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v → ∀ p ∈ pPrimes v u c,
      ∀ q ∈ qPrimes v u c, p.Prime ∧ q.Prime ∧ Real.exp u < (q : ℝ) ∧ q < p := by
  filter_upwards [eventual_scale_bounds c hc, eventual_window_conditions c hc,
    eventual_bottom_large] with v hs hw hb u hulo hule p hp q hq
  obtain ⟨_, _, hpA, hqA, hR, _, _, hqB⟩ := hs u hulo hule
  have hpB : 2 ≤ pStop v u c := by
    rw [pStop_ratio]
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ pStart v u c by linarith)]
  have hqratio : 4*qStart v u c ≤ qStop v u c := by
    rw [qStop_ratio]
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ qStart v u c by linarith)]
  have hqpair := rounded_pair_bounds hqA hqratio (by norm_num : (0 : ℕ) ≤ 1)
  have henv : (qLast v u c : ℝ)+1 ≤ envelope v :=
    hqpair.2.2.2.2.trans (by unfold envelope; linarith)
  have hbottom := hb (qLast v u c) henv
  obtain ⟨_, _, _, hprime, _, _⟩ := (selectedPrimes_mem _ _ _ _).mp hp
  obtain ⟨hqprime, hqlow, _⟩ := KorolevPrimeIntervals.intervalPrimes_mem.mp hq
  exact ⟨hprime, hqprime, lt_trans (lt_of_le_of_lt (Real.exp_le_exp.mpr hule) hbottom) hqlow,
    prime_order (hw u hulo hule).1.first_pos (index_separation hpB) hp hq⟩

theorem eventual_source_prime_properties (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℝ in atTop,
    ∀ x : ℝ, Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ p ∈ sourcePPrimes C m x, ∀ q ∈ sourceQPrimes C m x,
        p.Prime ∧ q.Prime ∧ Real.log x < (q : ℝ) ∧ q < p := by
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventual_prime_properties (Real.log C) (Real.log_nonneg hC)),
    eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with m hm hm0 hL x hlo hhi p hp q hq
  obtain ⟨_, hY, hulo, hule⟩ := source_log_range hm0 hL hlo hhi
  have hh := hm _ hulo hule p hp q hq
  rwa [Real.exp_log hY] at hh

end NField.Alignment.KorolevPrimeSeparation
