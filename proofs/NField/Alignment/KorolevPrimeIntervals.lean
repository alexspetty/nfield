/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMertensInput
import NField.Alignment.CollisionLargePrimeFactors

/-!
# Reciprocal prime mass in the intervals used by Korolev

Subtract the already proved Mertens prefix identities, retaining both
endpoint errors. Removing prime divisors of the modulus uses the existing
large-prime-divisor estimate. These are general real-interval estimates;
the source's selected endpoints and missing-factor counts remain separate.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevPrimeIntervals
open scoped BigOperators Classical
open CollisionMertensInput CollisionLargePrimeFactors

def intervalPrimes (u v : ℝ) : Finset ℕ := primesUpTo v \ primesUpTo u

theorem intervalPrimes_mem {u v : ℝ} {p : ℕ} :
    p ∈ intervalPrimes u v ↔ p.Prime ∧ u < (p : ℝ) ∧ (p : ℝ) ≤ v := by
  simp only [intervalPrimes, Finset.mem_sdiff, primesUpTo_mem]
  by_cases hp : p.Prime <;> simp [hp, not_le, and_comm]

theorem interval_reciprocal_identity {u v : ℝ} (huv : u ≤ v) :
    (∑ p ∈ intervalPrimes u v, (1 : ℝ) / p) =
      Real.log (Real.log v) - Real.log (Real.log u) + Mertens.E₂p v - Mertens.E₂p u := by
  have hs : primesUpTo u ⊆ primesUpTo v := by
    intro p hp
    obtain ⟨hp, hpu⟩ := primesUpTo_mem.mp hp
    exact primesUpTo_mem.mpr ⟨hp, hpu.trans huv⟩
  have he := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hs
  change (∑ p ∈ intervalPrimes u v, (1 : ℝ) / p) +
    (∑ p ∈ (Finset.Ioc 0 ⌊u⌋₊).filter Nat.Prime, (1 : ℝ) / p) =
    ∑ p ∈ (Finset.Ioc 0 ⌊v⌋₊).filter Nat.Prime, (1 : ℝ) / p at he
  rw [Mertens.sum_prime_div_eq, Mertens.sum_prime_div_eq] at he
  linarith

def errorConstant : ℝ := Real.log 4 + 6 + Mertens.E₁

theorem errorConstant_pos : 0 < errorConstant := by
  have h := Mertens.E₁.nonneg
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold errorConstant
  linarith

theorem interval_reciprocal_error {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    |(∑ p ∈ intervalPrimes u v, (1 : ℝ) / p) -
      (Real.log (Real.log v) - Real.log (Real.log u))| ≤
        2 * errorConstant / Real.log u := by
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlv : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv
  rw [interval_reciprocal_identity huv]
  calc
    _ = |Mertens.E₂p v - Mertens.E₂p u| := by congr 1; ring
    _ ≤ |Mertens.E₂p v| + |Mertens.E₂p u| := abs_sub _ _
    _ ≤ errorConstant / Real.log v + errorConstant / Real.log u :=
      add_le_add (Mertens.E₂p.abs_le (hu.trans huv)) (Mertens.E₂p.abs_le hu)
    _ ≤ errorConstant / Real.log u + errorConstant / Real.log u :=
      add_le_add (div_le_div_of_nonneg_left errorConstant_pos.le hlu hlv) le_rfl
    _ = _ := by ring

theorem coprime_interval_upper (m : ℕ) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ (intervalPrimes u v).filter (fun p => p.Coprime m), (1 : ℝ) / p) ≤
      Real.log (Real.log v) - Real.log (Real.log u) + 2 * errorConstant / Real.log u := by
  have hs : (∑ p ∈ (intervalPrimes u v).filter (fun p => p.Coprime m), (1 : ℝ) / p) ≤
      ∑ p ∈ intervalPrimes u v, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have he := (abs_le.mp (interval_reciprocal_error hu huv)).2
  linarith

theorem removed_reciprocal_bound {m : ℕ} (hm : 0 < m) {u v : ℝ} (hu : 1 < u) :
    (∑ p ∈ (intervalPrimes u v).filter (fun p => ¬p.Coprime m), (1 : ℝ) / p) ≤
      Real.log m / (u * Real.log u) := by
  have hs : (intervalPrimes u v).filter (fun p => ¬p.Coprime m) ⊆ largePrimeFactors m u := by
    intro p hp
    obtain ⟨hpi, hpc⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpp, hpu, _⟩ := intervalPrimes_mem.mp hpi
    have hpd : p ∣ m := by simpa [hpp.coprime_iff_not_dvd] using hpc
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd, hm.ne'⟩, hpu⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
    (large_prime_reciprocal_bound hm hu)

theorem coprime_interval_lower {m : ℕ} (hm : 0 < m) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    Real.log (Real.log v) - Real.log (Real.log u) - 2 * errorConstant / Real.log u -
      Real.log m / (u * Real.log u) ≤
        ∑ p ∈ (intervalPrimes u v).filter (fun p => p.Coprime m), (1 : ℝ) / p := by
  have he := Finset.sum_filter_add_sum_filter_not (intervalPrimes u v)
    (fun p : ℕ => p.Coprime m) (fun p : ℕ => (1 : ℝ) / p)
  have hlo := (abs_le.mp (interval_reciprocal_error hu huv)).1
  have hrem := removed_reciprocal_bound (v := v) hm (by linarith : 1 < u)
  linarith

end NField.Alignment.KorolevPrimeIntervals
