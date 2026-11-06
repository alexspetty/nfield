/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeIntervals

/-! # Prime interval populations from the checked reciprocal mass -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevPrimePopulation
open scoped BigOperators
open KorolevPrimeIntervals

/-- A lower endpoint converts reciprocal mass into a lower bound on population. -/
theorem endpoint_mass_le_card {S : Finset ℕ} {u : ℝ}
    (hpos : ∀ p ∈ S, 0 < p) (hlo : ∀ p ∈ S, u ≤ (p : ℝ)) :
    u * (∑ p ∈ S, (1 : ℝ)/p) ≤ S.card := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _p ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpr : (0 : ℝ) < p := by exact_mod_cast hpos p hp
      simpa only [mul_one_div] using (div_le_one hpr).mpr (hlo p hp)
    _ = _ := by simp

/-- An upper endpoint converts reciprocal mass into an upper bound on population. -/
theorem card_le_endpoint_mass {S : Finset ℕ} {v : ℝ}
    (hpos : ∀ p ∈ S, 0 < p) (hhi : ∀ p ∈ S, (p : ℝ) ≤ v) :
    (S.card : ℝ) ≤ v * (∑ p ∈ S, (1 : ℝ)/p) := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ _p ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpr : (0 : ℝ) < p := by exact_mod_cast hpos p hp
      simpa only [mul_one_div] using (one_le_div hpr).mpr (hhi p hp)

/-- The actual population of coprime interval primes has an explicit Mertens lower bound. -/
theorem coprime_population_lower {m : ℕ} (hm : 0 < m) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    u * (Real.log (Real.log v) - Real.log (Real.log u) -
      2 * errorConstant / Real.log u - Real.log m / (u * Real.log u)) ≤
      (((intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) := by
  apply (mul_le_mul_of_nonneg_left (coprime_interval_lower hm hu huv) (by linarith)).trans
  apply endpoint_mass_le_card
  · intro p hp
    exact (intervalPrimes_mem.mp (Finset.mem_filter.mp hp).1).1.pos
  · intro p hp
    exact (intervalPrimes_mem.mp (Finset.mem_filter.mp hp).1).2.1.le

/-- The same actual population has an explicit Mertens upper bound. -/
theorem coprime_population_upper (m : ℕ) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    (((intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) ≤
      v * (Real.log (Real.log v) - Real.log (Real.log u) +
        2 * errorConstant / Real.log u) := by
  have hc : (((intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) ≤
      v * (∑ p ∈ (intervalPrimes u v).filter (fun p => p.Coprime m), (1 : ℝ)/p) := by
    apply card_le_endpoint_mass
    · intro p hp
      exact (intervalPrimes_mem.mp (Finset.mem_filter.mp hp).1).1.pos
    · intro p hp
      exact (intervalPrimes_mem.mp (Finset.mem_filter.mp hp).1).2.2
  exact hc.trans (mul_le_mul_of_nonneg_left (coprime_interval_upper m hu huv) (by linarith))

end NField.Alignment.KorolevPrimePopulation
