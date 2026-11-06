/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowParameters

/-! # Squared separation of the actual rounded source indices -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevIndexSeparation
open Filter KorolevSourceScales KorolevWindowParameters KorolevEndpointIndices
open scoped Topology

/-- The second prime family's starting index is eight times the square of the first stopping scale. -/
theorem qStart_eq_eight_pStop_sq (v u c : ℝ) : qStart v u c = 8*(pStop v u c)^2 := by
  unfold qStart pStop
  rw [show 2*v-2*u+8*gain v u c = 2*(v-u+4*gain v u c) by ring]
  rw [show Real.exp (2*(v-u+4*gain v u c)) = Real.exp (v-u+4*gain v u c)^2 by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (v-u+4*gain v u c) 2]
  ring

/-- The actual rounding conventions retain the square separation. -/
theorem rounded_index_separation {v u c : ℝ} (hB : 2 ≤ pStop v u c) :
    8*(pLast v u c : ℝ)^2 ≤ qFirst v u c := by
  have hp := (upperIndex_bounds hB (by norm_num : (1 : ℕ) ≤ 1)).2
  have hq := (lowerIndex_bounds (show 0 ≤ qStart v u c by unfold qStart; positivity)).1
  change (pLast v u c : ℝ) ≤ pStop v u c - (1 : ℕ) + 1/2 at hp
  change qStart v u c+1/2 ≤ (qFirst v u c : ℝ) at hq
  norm_num only [Nat.cast_one] at hp
  have hle : (pLast v u c : ℝ) ≤ pStop v u c := by linarith
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (pLast v u c)) hle 2
  rw [qStart_eq_eight_pStop_sq] at hq
  nlinarith only [hs, hq]

/-- Every selected pair of indices has the separation needed by the bilinear parameters. -/
theorem selected_index_separation {v u c : ℝ} (hB : 2 ≤ pStop v u c) {k s : ℕ}
    (hk : k ≤ pLast v u c) (hs : qFirst v u c ≤ s) : 8*(k : ℝ)^2 ≤ s := by
  have hkR : (k : ℝ) ≤ pLast v u c := by exact_mod_cast hk
  have hsR : (qFirst v u c : ℝ) ≤ s := by exact_mod_cast hs
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hkR 2
  have hsep := rounded_index_separation hB
  nlinarith only [hsq, hsep, hsR]

/-- The full source range eventually provides square separation for every selected index pair. -/
theorem eventual_selected_index_separation (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v → ∀ k s : ℕ,
      k ≤ pLast v u c → qFirst v u c ≤ s → 8*(k : ℝ)^2 ≤ s := by
  filter_upwards [eventual_scale_bounds c hc] with v hv u hulo hule k s hk hs
  obtain ⟨_, _, hpA, _, hR, _, _, _⟩ := hv u hulo hule
  have hB : 2 ≤ pStop v u c := by
    rw [pStop_ratio]
    nlinarith
  exact selected_index_separation hB hk hs

end NField.Alignment.KorolevIndexSeparation
