/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.NearOneReciprocalDivisorBound
import NField.Alignment.KorolevWindowParameters
import NField.Alignment.KorolevSourceWindowCount

/-! # The actual source indices satisfy the near-one frequency conditions -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceFrequencyWeight
open Filter KorolevSourceScales KorolevWindowParameters KorolevEndpointIndices
open scoped Topology BigOperators

/-- The first source prime scale dominates the logarithm of the shorter-sum logarithm. -/
theorem pStart_ge_short_log {v u c : ℝ} (hule : u ≤ v)
    (hexp : 2*u ≤ Real.exp (2*gain v u c)) : u ≤ pStart v u c := by
  have he : 1 ≤ Real.exp (v-u) := Real.one_le_exp (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (2*gain v u c)).le
  unfold pStart
  rw [Real.exp_add]
  nlinarith

/-- Positive source indices make their even-moment root an admissible near-one exponent. -/
theorem admissible_of_indices {v : ℝ} {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hv : v ≤ 2*(k : ℝ)) :
    0 ≤ (((2*s*k : ℕ) : ℝ)⁻¹) ∧ (((2*s*k : ℕ) : ℝ)⁻¹) ≤ 1/2 ∧
      (((2*s*k : ℕ) : ℝ)⁻¹)*v ≤ 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn : (2 : ℝ) ≤ (2*s*k : ℕ) := by
    have hnat : 2 ≤ 2*s*k := by nlinarith
    exact_mod_cast hnat
  have hn0 : (0 : ℝ) < (2*s*k : ℕ) := by linarith
  have hV : v ≤ ((2*s*k : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (s : ℝ)-1 by linarith) (Nat.cast_nonneg k)]
  refine ⟨inv_nonneg.mpr hn0.le, ?_, ?_⟩
  · simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hn
  · calc
      _ = v/((2*s*k : ℕ) : ℝ) := by ring
      _ ≤ 1 := (div_le_one hn0).mpr hV

/-- Actual rounded source lower indices discharge every epsilon condition uniformly. -/
theorem eventual_source_admissible (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v → ∀ k s : ℕ,
      pFirst v u c ≤ k → qFirst v u c ≤ s →
      0 ≤ (((2*s*k : ℕ) : ℝ)⁻¹) ∧ (((2*s*k : ℕ) : ℝ)⁻¹) ≤ 1/2 ∧
        (((2*s*k : ℕ) : ℝ)⁻¹)*v ≤ 1 := by
  filter_upwards [eventual_scale_bounds c hc, eventually_ge_atTop (2 : ℝ)]
    with v hv hv2 u hulo hule k s hkfirst hsfirst
  obtain ⟨hu, hg, hp, hq, h4, h2u, _⟩ := hv u hulo hule
  have hpBounds := (lowerIndex_bounds (by linarith : 0 ≤ pStart v u c)).1
  have hqBounds := (lowerIndex_bounds (by linarith : 0 ≤ qStart v u c)).1
  have hkR : (pFirst v u c : ℝ) ≤ k := by exact_mod_cast hkfirst
  have hsR : (qFirst v u c : ℝ) ≤ s := by exact_mod_cast hsfirst
  change pStart v u c+1/2 ≤ (pFirst v u c : ℝ) at hpBounds
  change qStart v u c+1/2 ≤ (qFirst v u c : ℝ) at hqBounds
  have hk : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  have hs : 1 ≤ s := by exact_mod_cast (show (1 : ℝ) ≤ s by linarith)
  have hpu := pStart_ge_short_log hule h2u
  have hlogv : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  apply admissible_of_indices hk hs
  linarith

/-- The weighted sawtooth-frequency bound holds at every actual source-index root exponent. -/
theorem eventual_source_frequency_bound (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      (∑ j : ZMod m, ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) j‖ *
        (j.val.gcd m : ℝ)^(((2*s*k : ℕ) : ℝ)⁻¹))/(m : ℝ) ≤
          K*(harmonic m : ℝ)*(Real.log (Real.log m))^12 := by
  obtain ⟨K, hK, hbound⟩ := NearOneReciprocalDivisorBound.eventual_weighted_frequency_bound
  refine ⟨K, hK, ?_⟩
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hbound, ht.eventually (eventual_source_admissible (Real.log C) (Real.log_nonneg hC)),
    hlog.eventually_gt_atTop 1] with m hb he hL inst x hlo hhi k s hk hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have heps := he (Real.log (Real.log x)) hulo hule k s hk hs
  exact hb _ heps.1 heps.2.1 heps.2.2

end NField.Alignment.KorolevSourceFrequencyWeight
