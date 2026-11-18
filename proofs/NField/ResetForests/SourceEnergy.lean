/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ActualPrefixCost
import NField.Alignment.MagnitudeCubicLimits
/-! # The actual sampled coherent energy and its unconditional cubic budget -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CostCriteria

open scoped BigOperators Topology Matrix
open Filter
open NField.Alignment CommonResetGram CommonResetSampling
open SourceMetrics GramDecomposition RecordGeometry

abbrev OddPrime := MagnitudeCubicLimits.OddPrimeBase
abbrev primeAtTop := MagnitudeCubicLimits.oddPrimeAtTop

def sourceEnergy (p : ℕ) : ℝ :=
  sourceWork (sampledGram (p - 1) (p ^ 2)) (fun _ => 1) (fun _ => 1)

theorem source_energy_grid_sum (p : ℕ) :
    sourceEnergy p = ∑ a ∈ Finset.range (p ^ 2),
      CollisionRampEnergy.boundaryResponse (p - 1) ((a : ℝ) / ((p ^ 2 : ℕ) : ℝ)) ^ 2 := by
  unfold sourceEnergy sourceWork
  rw [sampled_gram_mixed]
  simp_rw [cutoff_complete_profile, unit_weights, ← pow_two]
  simpa only using (Fin.sum_univ_eq_sum_range
    (fun a : ℕ => CollisionRampEnergy.boundaryResponse (p - 1)
      ((a : ℝ) / ((p ^ 2 : ℕ) : ℝ)) ^ 2) (p ^ 2))

theorem source_energy_sampled_energy (p : ℕ) :
    sourceEnergy p = (p : ℝ) ^ 2 * sampledEnergy (p - 1) (p ^ 2) := by
  rw [source_energy_grid_sum]
  unfold sampledEnergy
  by_cases hp : p = 0
  · subst p
    simp
  · have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
    simp only [Nat.cast_pow]
    field_simp

theorem source_energy_eq_prime_carry {p : ℕ} (hp : p.Prime) :
    sourceEnergy p = PrimeCarryEnergyBridge.primeCarryEnergy hp := by
  rw [source_energy_sampled_energy, sampledEnergy_prime hp,
    ExactSamplingReservoirBridge.collisionEnergy_eq_primeCarryEnergy hp]
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp

theorem source_energy_cubic_error {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    |sourceEnergy p - (p : ℝ) ^ 3| ≤ 96 * (p : ℝ) ^ 2 * (Real.log (p : ℝ)) ^ 2 := by
  rw [source_energy_eq_prime_carry hp]
  exact PrimeSquareCubicEnergy.primeCarryEnergy_cubic_pureLog_bound hp hodd

theorem source_energy_cubic_limit :
    Tendsto (fun p : OddPrime => sourceEnergy p.val / (p.val : ℝ) ^ 3) primeAtTop (𝓝 1) := by
  apply MagnitudeCubicLimits.normalized_cubic_limit.congr'
  exact Eventually.of_forall (fun p => by dsimp only; rw [source_energy_eq_prime_carry p.property.1])

theorem source_energy_eventual_budget :
    ∀ᶠ p : OddPrime in primeAtTop, sourceEnergy p.val ≤ 2 * (p.val : ℝ) ^ 3 := by
  have hq : ∀ᶠ p : OddPrime in primeAtTop,
      sourceEnergy p.val / (p.val : ℝ) ^ 3 < 2 :=
    (tendsto_order.mp source_energy_cubic_limit).2 2 (by norm_num)
  filter_upwards [hq] with p hp
  have hpR : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  exact ((div_lt_iff₀ (pow_pos hpR 3)).mp hp).le

theorem source_energy_nonnegative (p : OddPrime) : 0 ≤ sourceEnergy p.val :=
  source_work_nonnegative _ (both_prime_square_grams_posDef p.property.1 p.property.2).2 _

end NField.ResetForests.CostCriteria
