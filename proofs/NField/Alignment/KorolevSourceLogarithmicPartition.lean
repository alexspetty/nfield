/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevLogarithmicPartition
import NField.Alignment.KorolevMergedBlockPopulation

/-! # Actual source-range populations in the finite logarithmic partition -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceLogarithmicPartition
open Filter KorolevPrimeWindows KorolevLogarithmicPartition
open scoped Topology

/-- All blocks of the exact partition inherit the population bound in the full source range. -/
theorem eventual_partition_population_nat (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k : ℕ, 1 ≤ k →
      (k ≤ KorolevWindowParameters.pLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C) ∨
       k ≤ KorolevWindowParameters.qLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C)) →
      ∀ l D : ℝ, upperEndpoint (Real.log m) (k+1) ≤ Real.exp l → A ≤ D → ∀ i : ℕ,
      point l D A i * width D A / (4*Real.log (point l D A (i+1))) ≤
        (((block l D A i).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [KorolevMergedBlockPopulation.eventual_source_population_nat C hC A hA herror]
    with m hb x hlo hhi k hk hlast l D hl hD i
  have hA0 : 0 < A := by linarith
  have hw := count_width hA0 hD
  have hm := (point_strictMono l hA0 hD).monotone
  have hbase : upperEndpoint (Real.log m) (k+1) ≤ point l D A i := by
    have hh := hm (Nat.zero_le i)
    rw [point_zero] at hh
    exact hl.trans hh
  exact hb x hlo hhi k hk hlast (width D A) hw.2.1 hw.2.2.1.le
    (point l D A i) (point l D A (i+1)) hbase (hm (by omega)) (log_increment l D A i)

/-- A quadratic size condition ensures both actual source intervals can be partitioned. -/
theorem source_log_width {L A : ℝ} {k : ℕ} (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hsize : 4*(A+Real.log 4)*(k : ℝ)^2 ≤ L) :
    A ≤ Real.log (upperEndpoint L k) - Real.log (lowerEndpoint L k) ∧
    A ≤ Real.log (upperEndpoint L k) - Real.log (upperEndpoint L (k+1)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ L := (by positivity : 0 ≤ 4*(A+Real.log 4)*(k : ℝ)^2).trans hsize
  have hd : 0 < 4*(k : ℝ)^2-1 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hdiv : A+Real.log 4 ≤ L/(4*(k : ℝ)^2-1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hsize, hA, hlog4]
  have hw : A ≤ Real.log (upperEndpoint L k) - Real.log (lowerEndpoint L k) := by
    rw [log_gap L hk]
    linarith
  refine ⟨hw, ?_⟩
  have hsep := Real.log_le_log (upperEndpoint_pos L (k+1)) (successor_separation hL hk).le
  linarith

/-- The entire source envelope eventually has enough logarithmic width for the partition. -/
theorem eventual_envelope_width (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ KorolevSourceEnvelope.envelope t →
      A ≤ Real.log (upperEndpoint (Real.exp t) k) - Real.log (lowerEndpoint (Real.exp t) k) ∧
      A ≤ Real.log (upperEndpoint (Real.exp t) k) - Real.log (upperEndpoint (Real.exp t) (k+1)) := by
  filter_upwards [KorolevSourceEnvelope.eventual_envelope_small (4*(A+Real.log 4))]
    with t hs k hk hkenv
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hkenv 2
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsize : 4*(A+Real.log 4)*(k : ℝ)^2 ≤ Real.exp t := by
    have hh := (div_le_iff₀ (Real.exp_pos t)).mp hs
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*(A+Real.log 4) by positivity)]
  exact source_log_width hk hA hsize

end NField.Alignment.KorolevSourceLogarithmicPartition
