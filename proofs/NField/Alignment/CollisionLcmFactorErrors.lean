/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmPrimeLosses
import NField.Alignment.CollisionSqrtPrimeSplit
import NField.Alignment.CollisionAbsentPrimeProducts

/-!
# Summed errors of the actual lcm local factors

The square-root split gives explicit constants for both observables.
The alignment estimates include the literal floor-exponent display.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmFactorErrors

open scoped Classical
open Filter CollisionLcmPrimeLosses CollisionLocalFactorLosses CollisionSqrtPrimeSplit
open CollisionOdometerRecurrence CollisionZetaMoments CollisionResetLocalFactors
open CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds

def lcmAlignmentFactorLoss (m : ℕ) : ℝ := ∑ p ∈ Nat.primesLE m,
  ((1+(p : ℝ)⁻¹)-alignmentPrimeFactor (p : ℝ) ((cutoffPeriod m).factorization p))/(1+(p : ℝ)⁻¹)

def lcmAlignmentAverageLoss (m : ℕ) : ℝ := ∑ p ∈ Nat.primesLE m,
  (1/((p : ℝ)-1)-alignmentPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p))*Real.log p

def lcmResetFactorLoss (m : ℕ) : ℝ := ∑ p ∈ Nat.primesLE m,
  ((1+(p : ℝ)⁻¹)-resetPrimeFactor (p : ℝ) ((cutoffPeriod m).factorization p))/(1+(p : ℝ)⁻¹)

def lcmResetAverageLoss (m : ℕ) : ℝ := ∑ p ∈ Nat.primesLE m,
  (1/((p : ℝ)-1)-resetPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p))*Real.log p

theorem lcmPrimePowerLoss_sum_bound {m : ℕ} (hm : 4 ≤ m) :
    (∑ p ∈ Nat.primesLE m, lcmPrimePowerLoss m p) ≤ 3/Real.sqrt m := by
  apply finite_inverse_square_split (Nat.primesLE m) (lcmPrimePowerLoss m)
    (by exact_mod_cast hm)
  · exact fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  · exact fun p hp => (lcmPrimePowerLoss_bound (Nat.prime_of_mem_primesLE hp)
      (Nat.le_of_mem_primesLE hp)).1
  · exact fun p hp => (lcmPrimePowerLoss_bound (Nat.prime_of_mem_primesLE hp)
      (Nat.le_of_mem_primesLE hp)).2

theorem lcmAlignmentFactorLoss_nonneg (m : ℕ) : 0 ≤ lcmAlignmentFactorLoss m := by
  apply Finset.sum_nonneg
  intro p hp
  exact (alignmentPrimeFactor_relative_loss_bound
    (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) _).1

theorem lcmAlignmentAverageLoss_nonneg (m : ℕ) : 0 ≤ lcmAlignmentAverageLoss m := by
  apply Finset.sum_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
  exact mul_nonneg (alignmentPrimeAverage_loss_bound hp2 _).1 (Real.log_nonneg (by linarith))

theorem lcmResetFactorLoss_nonneg (m : ℕ) : 0 ≤ lcmResetFactorLoss m := by
  apply Finset.sum_nonneg
  intro p hp
  exact (resetPrimeFactor_relative_loss_bound
    (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) _).1

theorem lcmResetAverageLoss_nonneg (m : ℕ) : 0 ≤ lcmResetAverageLoss m := by
  apply Finset.sum_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
  exact mul_nonneg (resetPrimeAverage_loss_bound hp2 _).1 (Real.log_nonneg (by linarith))

theorem lcmAlignmentFactorLoss_bound {m : ℕ} (hm : 4 ≤ m) :
    lcmAlignmentFactorLoss m ≤ 3/Real.sqrt m := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE m, lcmPrimePowerLoss m p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [cutoffPeriod_prime_exponent m (Nat.prime_of_mem_primesLE hp)]
      exact (alignmentPrimeFactor_relative_loss_bound
        (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) _).2
    _ ≤ _ := lcmPrimePowerLoss_sum_bound hm

theorem lcmResetFactorLoss_bound {m : ℕ} (hm : 4 ≤ m) :
    lcmResetFactorLoss m ≤ 3/Real.sqrt m := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE m, lcmPrimePowerLoss m p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [cutoffPeriod_prime_exponent m (Nat.prime_of_mem_primesLE hp)]
      exact (resetPrimeFactor_relative_loss_bound
        (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) _).2
    _ ≤ _ := lcmPrimePowerLoss_sum_bound hm

theorem lcmAlignmentAverageLoss_bound {m : ℕ} (hm : 4 ≤ m) :
    lcmAlignmentAverageLoss m ≤ 9*Real.log m/Real.sqrt m := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE m, 3*Real.log m*lcmPrimePowerLoss m p :=
      Finset.sum_le_sum (fun p hp => lcm_alignment_average_loss (Nat.prime_of_mem_primesLE hp)
        (Nat.le_of_mem_primesLE hp))
    _ = 3*Real.log m*(∑ p ∈ Nat.primesLE m, lcmPrimePowerLoss m p) := by rw [Finset.mul_sum]
    _ ≤ 3*Real.log m*(3/Real.sqrt m) := mul_le_mul_of_nonneg_left
      (lcmPrimePowerLoss_sum_bound hm) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg m))
    _ = _ := by ring

theorem lcmResetAverageLoss_bound {m : ℕ} (hm : 4 ≤ m) :
    lcmResetAverageLoss m ≤ 9*Real.log m/Real.sqrt m := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE m, 3*Real.log m*lcmPrimePowerLoss m p :=
      Finset.sum_le_sum (fun p hp => lcm_reset_average_loss (Nat.prime_of_mem_primesLE hp)
        (Nat.le_of_mem_primesLE hp))
    _ = 3*Real.log m*(∑ p ∈ Nat.primesLE m, lcmPrimePowerLoss m p) := by rw [Finset.mul_sum]
    _ ≤ 3*Real.log m*(3/Real.sqrt m) := mul_le_mul_of_nonneg_left
      (lcmPrimePowerLoss_sum_bound hm) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg m))
    _ = _ := by ring

theorem lcm_alignment_local_errors {m : ℕ} (hm : 4 ≤ m) :
    (∑ p ∈ Nat.primesLE m,
      ((1+(p : ℝ)⁻¹)-alignmentPrimeFactor (p : ℝ) ⌊Real.log m/Real.log p⌋₊)/(1+(p : ℝ)⁻¹)) ≤
      3/Real.sqrt m ∧
    (∑ p ∈ Nat.primesLE m,
      (1/((p : ℝ)-1)-alignmentPrimeAverage (p : ℝ) ⌊Real.log m/Real.log p⌋₊)*Real.log p) ≤
      9*Real.log m/Real.sqrt m := by
  have hK := lcmAlignmentFactorLoss_bound hm
  have hu := lcmAlignmentAverageLoss_bound hm
  have heK : lcmAlignmentFactorLoss m=∑ p ∈ Nat.primesLE m,
      ((1+(p : ℝ)⁻¹)-alignmentPrimeFactor (p : ℝ) ⌊Real.log m/Real.log p⌋₊)/(1+(p : ℝ)⁻¹) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [cutoffPeriod_prime_exponent_floor m (Nat.prime_of_mem_primesLE hp)]
  have heu : lcmAlignmentAverageLoss m=∑ p ∈ Nat.primesLE m,
      (1/((p : ℝ)-1)-alignmentPrimeAverage (p : ℝ) ⌊Real.log m/Real.log p⌋₊)*Real.log p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [cutoffPeriod_prime_exponent_floor m (Nat.prime_of_mem_primesLE hp)]
  exact ⟨heK ▸ hK,heu ▸ hu⟩

theorem lcm_factor_errors_isBigO :
    Asymptotics.IsBigO atTop lcmAlignmentFactorLoss (fun m : ℕ => 1/Real.sqrt m) ∧
      Asymptotics.IsBigO atTop lcmAlignmentAverageLoss (fun m : ℕ => Real.log m/Real.sqrt m) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨3,?_⟩
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
    rw [Real.norm_of_nonneg (lcmAlignmentFactorLoss_nonneg m),
      Real.norm_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))]
    convert! lcmAlignmentFactorLoss_bound hm using 1
    ring
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨9,?_⟩
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
    rw [Real.norm_of_nonneg (lcmAlignmentAverageLoss_nonneg m),
      Real.norm_of_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _))]
    convert! lcmAlignmentAverageLoss_bound hm using 1
    ring

end NField.Alignment.CollisionLcmFactorErrors
