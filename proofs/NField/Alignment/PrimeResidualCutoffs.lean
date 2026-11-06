/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeFiniteCutoffs

/-! # Finite initial prime segments in residual limits -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.PrimePeriodicLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.ProgressionMertens

theorem sum_Ioc_residual_cutoff_limit (F : ℕ → ℂ) (c : ℕ) (g : ℝ → ℂ) {L : ℂ}
    (hL : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n) - g x)
      atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc c ⌊x⌋₊, F n) - g x)
      atTop (𝓝 (L - ∑ n ∈ Finset.Ioc 0 c, F n)) := by
  apply (hL.sub_const _).congr'
  filter_upwards [sum_Ioc_cutoff_eventually F c] with x hx
  rw [hx]
  ring

theorem summable_Ioc_real_cutoff_limit (F : ℕ → ℂ) (hF : Summable F) (hzero : F 0 = 0)
    (c : ℕ) :
    ∃ L : ℂ, Tendsto (fun x : ℝ => ∑ n ∈ Finset.Ioc c ⌊x⌋₊, F n) atTop (𝓝 L) := by
  have hsum := hF.hasSum.tendsto_sum_nat.comp
    ((tendsto_add_atTop_nat 1).comp
      (tendsto_nat_floor_atTop : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop))
  have hfull : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n) atTop (𝓝 (∑' n, F n)) := by
    convert hsum using 1
    ext x
    exact sum_Ioc_eq_range_succ hzero ⌊x⌋₊
  exact ⟨_, sum_Ioc_cutoff_limit F c hfull⟩

end NField.Alignment.PrimePeriodicLimits
