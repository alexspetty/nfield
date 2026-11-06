/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimePopulation
import NField.Alignment.KorolevWindowMass

/-! # Actual coprime populations in the selected prime windows -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevWindowPopulation
open scoped BigOperators
open KorolevPrimeIntervals KorolevPrimeWindows KorolevWindowMass KorolevPrimePopulation

/-- Removing modulus divisors from a source window retains an explicit mass lower bound. -/
theorem coprime_window_mass_lower {m k : ℕ} (hm : 0 < m) {L : ℝ} (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ L) :
    (Real.log ((k : ℝ)+1)-Real.log k)/2 - lossConstant*(k : ℝ)/L -
      Real.log m / (lowerEndpoint L k * Real.log (lowerEndpoint L k)) ≤
      ∑ p ∈ (windowPrimes L k).filter (fun p => p.Coprime m), (1 : ℝ)/p := by
  obtain ⟨_, _, htwo, _⟩ := window_conditions hk hsize
  have hmass := window_mass_lower hk hsize
  have hremoved := removed_reciprocal_bound (v := upperEndpoint L k) hm
    (by linarith : 1 < lowerEndpoint L k)
  have he := Finset.sum_filter_add_sum_filter_not (windowPrimes L k)
    (fun p : ℕ => p.Coprime m) (fun p : ℕ => (1 : ℝ)/p)
  change (∑ p ∈ (windowPrimes L k).filter (fun p => ¬p.Coprime m), (1 : ℝ)/p) ≤ _ at hremoved
  linarith

/-- A lower bound for the actual number of coprime primes, with source endpoints and losses. -/
theorem coprime_window_population_lower {m k : ℕ} (hm : 0 < m) {L : ℝ} (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ L) :
    lowerEndpoint L k *
      ((Real.log ((k : ℝ)+1)-Real.log k)/2 - lossConstant*(k : ℝ)/L -
        Real.log m / (lowerEndpoint L k * Real.log (lowerEndpoint L k))) ≤
      (((windowPrimes L k).filter (fun p => p.Coprime m)).card : ℝ) := by
  apply (mul_le_mul_of_nonneg_left (coprime_window_mass_lower hm hk hsize)
    (lowerEndpoint_pos L k).le).trans
  apply endpoint_mass_le_card
  · intro p hp
    exact (intervalPrimes_mem.mp (Finset.mem_filter.mp hp).1).1.pos
  · intro p hp
    exact (intervalPrimes_mem.mp (Finset.mem_filter.mp hp).1).2.1.le

end NField.Alignment.KorolevWindowPopulation
