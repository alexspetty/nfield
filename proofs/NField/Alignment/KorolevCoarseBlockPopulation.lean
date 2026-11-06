/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSourceLogarithmicPartition

/-! # Actual logarithmic-block populations with a uniform polynomial denominator -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCoarseBlockPopulation
open Filter KorolevPrimeWindows KorolevLogarithmicPartition
open scoped Topology

/-- A width at least one and an upper logarithm bounded by L give the coarser normalizer. -/
theorem coarse_lower {u v B L N : ℝ} (hu : 0 ≤ u) (hv : 0 < Real.log v)
    (hB : 1 ≤ B) (hlog : Real.log v ≤ L) (hpop : u*B/(4*Real.log v) ≤ N) :
    u/(4*L) ≤ N := by
  apply le_trans _ hpop
  apply div_le_div₀ (by positivity) (by nlinarith) (by positivity)
  linarith

/-- Every actual partition block stays between the original logarithmic endpoints. -/
theorem partition_log_bounds {l D A : ℝ} (hl : 1 ≤ l) (hA : 0 < A) (hD : A ≤ D)
    {i : ℕ} (hi : i < blockCount D A) :
    0 < Real.log (point l D A (i+1)) ∧
      Real.log (point l D A (i+1)) ≤ l+D ∧ Real.exp l ≤ point l D A i := by
  have hw : 0 < width D A := lt_of_lt_of_le hA (count_width hA hD).2.1
  have hm := (point_strictMono l hA hD).monotone
  refine ⟨?_, ?_, ?_⟩
  · rw [point, Real.log_exp]
    positivity
  · have hh := Real.log_le_log (Real.exp_pos _) (hm (show i+1 ≤ blockCount D A by omega))
    rw [point_last l hA hD] at hh
    simpa only [point, Real.log_exp] using hh
  · have hh := hm (Nat.zero_le i)
    rw [point_zero] at hh
    exact hh

/-- Actual coprime source blocks satisfy the population criterion used by the block moment estimate. -/
theorem eventual_coarse_population_nat (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k : ℕ, 1 ≤ k →
      (k ≤ KorolevWindowParameters.pLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C) ∨
       k ≤ KorolevWindowParameters.qLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C)) →
      ∀ l D : ℝ, 1 ≤ l → upperEndpoint (Real.log m) (k+1) ≤ Real.exp l →
      A ≤ D → l+D ≤ Real.log m → ∀ i : ℕ, i < blockCount D A →
      Real.exp l/(4*Real.log m) ≤
        (((block l D A i).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [KorolevSourceLogarithmicPartition.eventual_partition_population_nat C hC A hA herror]
    with m hp x hlo hhi k hk hlast l D hl hbase hD hlog i hi
  have hA0 : 0 < A := by linarith
  obtain ⟨hv, hupper, hlower⟩ := partition_log_bounds hl hA0 hD hi
  have hh := coarse_lower (Real.exp_pos _).le hv (hA.trans (count_width hA0 hD).2.1)
    (hupper.trans hlog) (hp x hlo hhi k hk hlast l D hbase hD i)
  have hL : 0 < Real.log (m : ℝ) := hv.trans_le (hupper.trans hlog)
  exact (div_le_div_of_nonneg_right hlower (by positivity : 0 ≤ 4*Real.log (m : ℝ))).trans hh

end NField.Alignment.KorolevCoarseBlockPopulation
