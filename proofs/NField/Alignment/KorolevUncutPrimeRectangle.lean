/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourceWindows

/-! # No modular aliasing on the complete source prime rectangle -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevUncutPrimeRectangle
open Filter KorolevPrimeWindows KorolevPrimeIntervals KorolevSourceScales
  KorolevWindowParameters KorolevEndpointIndices
open scoped Topology

/-- Both full upper endpoints have product below the exponential modulus. -/
theorem upper_rectangle_lt_exp {L : ℝ} (hL : 0 ≤ L) {k s : ℕ}
    (hk : 2 ≤ k) (hs : 2 ≤ s) : upperEndpoint L k * upperEndpoint L s < Real.exp L := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hp : L/(2*(k : ℝ)-1) ≤ L/2 :=
    div_le_div_of_nonneg_left hL (by norm_num) (by linarith)
  have hq : L/(2*(s : ℝ)-1) ≤ L/2 :=
    div_le_div_of_nonneg_left hL (by norm_num) (by linarith)
  calc
    _ = Real.exp (L/(2*(k : ℝ)-1)+L/(2*(s : ℝ)-1))/16 := by
      rw [Real.exp_add]
      unfold upperEndpoint
      ring
    _ ≤ Real.exp L/16 := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ < Real.exp L := by linarith [Real.exp_pos L]

/-- Every product in the uncut source rectangle is a literal integer below the modulus. -/
theorem product_lt_modulus {m k s p q : ℕ} (hm : 1 ≤ m) (hk : 2 ≤ k) (hs : 2 ≤ s)
    (hp : (p : ℝ) ≤ upperEndpoint (Real.log m) k)
    (hq : (q : ℝ) ≤ upperEndpoint (Real.log m) s) : p*q < m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbound := upper_rectangle_lt_exp (Real.log_nonneg hmR) hk hs
  rw [Real.exp_log (by linarith : (0 : ℝ) < m)] at hbound
  have hmul := mul_le_mul hp hq (Nat.cast_nonneg q) (upperEndpoint_pos _ _).le
  exact_mod_cast hmul.trans_lt hbound

/-- The actual rounded lower indices are uniformly at least two throughout the source range. -/
theorem eventual_first_indices_ge_two (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ t : ℝ in atTop,
    ∀ z : ℝ, (4/5)*t+5*Real.log t ≤ z → z ≤ t →
      2 ≤ pFirst t z c ∧ 2 ≤ qFirst t z c := by
  filter_upwards [eventual_scale_bounds c hc] with t ht z hz hzt
  obtain ⟨_, _, hp, hq, _⟩ := ht z hz hzt
  have hpi := (lowerIndex_bounds (by linarith : 0 ≤ pStart t z c)).1
  have hqi := (lowerIndex_bounds (by linarith : 0 ≤ qStart t z c)).1
  constructor
  · change 2 ≤ lowerIndex (pStart t z c)
    exact_mod_cast (show (2 : ℝ) ≤ lowerIndex (pStart t z c) by linarith)
  · change 2 ≤ lowerIndex (qStart t z c)
    exact_mod_cast (show (2 : ℝ) ≤ lowerIndex (qStart t z c) by linarith)

/-- No product aliases modulo m, even before the canonical product cutoff is applied. -/
theorem eventual_source_rectangle (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in atTop,
    ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      ∀ p ∈ windowPrimes (Real.log m) k,
      ∀ q ∈ intervalPrimes (upperEndpoint (Real.log m) (s+1)) (upperEndpoint (Real.log m) s),
        p*q < m := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [ht.eventually (eventual_first_indices_ge_two (Real.log C) (Real.log_nonneg hC)),
    hlog.eventually_gt_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with m hi hL hm x hlo hhi k s hk hs p hp q hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hii := hi (Real.log (Real.log x)) hulo hule
  exact product_lt_modulus hm (hii.1.trans hk) (hii.2.trans hs)
    (intervalPrimes_mem.mp hp).2.2 (intervalPrimes_mem.mp hq).2.2

end NField.Alignment.KorolevUncutPrimeRectangle
