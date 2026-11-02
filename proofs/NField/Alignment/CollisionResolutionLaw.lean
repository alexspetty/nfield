/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMassReadout
import Mathlib.NumberTheory.Divisors

/-!
# Exact capacity reconstruction and divisor resets

All-resolution uniqueness is proved from the triangular finite capacity
readout. The infinite remainder sum has an independently justified reset.
-/

noncomputable section

namespace NField.Alignment.CollisionResolutionLaw

open scoped BigOperators
open CollisionRemainderDynamics CollisionMassReadout SecondaryCapacityLedger

def completedCapacity (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / 3 + (2 / 3 : ℝ) *
    ∑ k ∈ Finset.Icc 2 N, v k * (k : ℝ) * ((N / k : ℕ) : ℝ)

theorem completedCapacity_collision (N : ℕ) :
    completedCapacity collisionWeight N = continuousCapacity N := by
  unfold completedCapacity continuousCapacity
  have he : (∑ k ∈ Finset.Icc 2 N, collisionWeight k * (k : ℝ) * ((N / k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 2 N, (((N / k : ℕ) : ℝ) / (k : ℝ)) * reducedHarmonicStar k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1
      exact_mod_cast (show k ≠ 0 by omega)
    unfold collisionWeight
    field_simp
  rw [he]
  ring

theorem completedCapacity_injective (v : ℕ → ℝ) (hv1 : v 1 = 0)
    (hc : ∀ N, completedCapacity v N = continuousCapacity N) :
    ∀ k, 1 ≤ k → v k = collisionWeight k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases hk1 : k = 1
      · simpa [hk1] using hv1
      have hk2 : 2 ≤ k := by omega
      have hkm : k ∈ Finset.Icc 2 k := Finset.mem_Icc.mpr ⟨hk2, le_refl k⟩
      have hread := (hc k).trans (completedCapacity_collision k).symm
      unfold completedCapacity at hread
      have hvsum := Finset.sum_erase_add (Finset.Icc 2 k)
        (fun j => v j * (j : ℝ) * ((k / j : ℕ) : ℝ)) hkm
      have hwsum := Finset.sum_erase_add (Finset.Icc 2 k)
        (fun j => collisionWeight j * (j : ℝ) * ((k / j : ℕ) : ℝ)) hkm
      have he : (∑ j ∈ (Finset.Icc 2 k).erase k, v j * (j : ℝ) * ((k / j : ℕ) : ℝ)) =
          ∑ j ∈ (Finset.Icc 2 k).erase k, collisionWeight j * (j : ℝ) * ((k / j : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_erase.mp hj
        have hjI := Finset.mem_Icc.mp hj'.2
        rw [ih j (by omega) (by omega)]
      rw [he] at hvsum
      have hk0 : k ≠ 0 := by omega
      simp only [Nat.div_self (show 0 < k by omega), Nat.cast_one, mul_one] at hvsum hwsum
      have hprod : v k * (k : ℝ) = collisionWeight k * (k : ℝ) := by linarith
      exact mul_right_cancel₀ (by exact_mod_cast hk0) hprod

theorem completedCapacity_tsum (N : ℕ) :
    continuousCapacity N = (N : ℝ) / 3 + (2 / 3 : ℝ) *
      ∑' k, collisionWeight k * (k : ℝ) * ((N / k : ℕ) : ℝ) := by
  rw [← completedCapacity_collision]
  unfold completedCapacity
  congr 2
  symm
  apply tsum_eq_sum
  intro k hk
  by_cases hsmall : k < 2
  · interval_cases k <;> simp
  · have hNk : N < k := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hk
      omega
    rw [Nat.div_eq_of_lt hNk, Nat.cast_zero, mul_zero]

def resetTerm (n k : ℕ) : ℝ := if k ∣ n then (k : ℝ) * collisionWeight k else 0

theorem resetTerm_summable {n : ℕ} (hn : 0 < n) : Summable (resetTerm n) := by
  apply summable_of_ne_finset_zero (s := n.divisors)
  intro k hk
  unfold resetTerm
  rw [if_neg]
  intro hdiv
  exact hk (Nat.mem_divisors.mpr ⟨hdiv, hn.ne'⟩)

theorem resetTerm_tsum {n : ℕ} (hn : 0 < n) :
    (∑' k, resetTerm n k) = ∑ k ∈ n.divisors, (k : ℝ) * collisionWeight k := by
  calc
    _ = ∑ k ∈ n.divisors, resetTerm n k := by
      apply tsum_eq_sum
      intro k hk
      unfold resetTerm
      rw [if_neg]
      intro hdiv
      exact hk (Nat.mem_divisors.mpr ⟨hdiv, hn.ne'⟩)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact if_pos (Nat.dvd_of_mem_divisors hk)

theorem deficit_reset (N : ℕ) :
    deficit (N + 1) - deficit N =
      (2 / 3 : ℝ) * (1 - ∑ k ∈ (N + 1).divisors, (k : ℝ) * collisionWeight k) := by
  have hterm (k : ℕ) :
      collisionWeight k * (((N + 1) % k : ℕ) : ℝ) -
        collisionWeight k * ((N % k : ℕ) : ℝ) = collisionWeight k - resetTerm (N + 1) k := by
    by_cases hk : k = 0
    · simp [hk, resetTerm]
    rw [← mul_sub, remainder_step (Nat.pos_of_ne_zero hk) N]
    unfold resetTerm
    split_ifs <;> ring
  unfold deficit
  rw [← mul_sub, ← (remainder_age_summable (N + 1)).tsum_sub (remainder_age_summable N)]
  simp_rw [hterm]
  rw [collisionWeight_summable.tsum_sub (resetTerm_summable (Nat.succ_pos N)),
    collisionWeight_tsum, resetTerm_tsum (Nat.succ_pos N)]

end NField.Alignment.CollisionResolutionLaw
