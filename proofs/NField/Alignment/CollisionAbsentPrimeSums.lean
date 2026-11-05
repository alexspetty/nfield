/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerPrimeTailMajorants

/-!
# Uniform sums over absent large primes

The modulus only chooses a subset of the prime tail. Both positive sums
are bounded by actual convergent integer tails, uniformly in that subset.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAbsentPrimeSums

open scoped Classical
open CollisionIntegerPrimeTailMajorants CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds
open CollisionZetaMoments CollisionAmplitudeTail CollisionPositiveLogTail

def absentPrimeMassTerm (L : ℕ) (y : ℝ) (p : Nat.Primes) : ℝ :=
  if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then 1/((p.val : ℝ)*(p.val+1)) else 0

def absentPrimeLogTerm (L : ℕ) (y : ℝ) (p : Nat.Primes) : ℝ :=
  if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then
    alignmentPrimeAverage (p.val : ℝ) 0*Real.log p.val else 0

theorem absentPrimeMassTerm_nonneg (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    0 ≤ absentPrimeMassTerm L y p := by
  unfold absentPrimeMassTerm
  split_ifs <;> positivity

theorem absentPrimeMassTerm_bound (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    absentPrimeMassTerm L y p ≤ inverseSquareTailTerm y p.val := by
  unfold absentPrimeMassTerm inverseSquareTailTerm
  by_cases hp : y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors
  · simp only [if_pos hp,if_pos hp.1,powerKernel]
    have hp0 : 0 < (p.val : ℝ) := by exact_mod_cast p.property.pos
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  · simp only [if_neg hp]
    split_ifs
    · unfold powerKernel
      positivity
    · rfl

theorem absentPrimeMassTerm_summable (L : ℕ) (y : ℝ) :
    Summable (absentPrimeMassTerm L y) :=
  Summable.of_nonneg_of_le (absentPrimeMassTerm_nonneg L y) (absentPrimeMassTerm_bound L y)
    ((inverseSquareTailTerm_summable y).comp_injective (Subtype.val_injective (p := Nat.Prime)))

theorem absent_prime_mass_sum_bound (L : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    (∑' p : Nat.Primes, absentPrimeMassTerm L y p) ≤ 2/y := by
  have hs := inverseSquareTailTerm_summable y
  calc
    _ ≤ ∑' p : Nat.Primes, inverseSquareTailTerm y p.val :=
      (absentPrimeMassTerm_summable L y).tsum_le_tsum (absentPrimeMassTerm_bound L y)
        (hs.comp_injective (Subtype.val_injective (p := Nat.Prime)))
    _ ≤ ∑' n : ℕ, inverseSquareTailTerm y n :=
      tsum_comp_le_tsum_of_inj hs (inverseSquareTailTerm_nonneg y)
        (Subtype.val_injective (p := Nat.Prime))
    _ ≤ _ := integer_inverse_square_tail_bound hy

theorem absentPrimeLogTerm_nonneg (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    0 ≤ absentPrimeLogTerm L y p := by
  have hp1 : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  unfold absentPrimeLogTerm
  split_ifs
  · exact mul_nonneg (alignmentPrimeAverage_bounds hp1 0).1 (Real.log_nonneg hp1.le)
  · rfl

theorem absentPrimeLogTerm_bound (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    absentPrimeLogTerm L y p ≤
      2*(if y < (p.val : ℝ) then positiveLogTerm positiveUnit p.val else 0) := by
  have hp2 : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
  have hl : 0 ≤ Real.log (p.val : ℝ) := Real.log_nonneg (by linarith)
  unfold absentPrimeLogTerm
  by_cases hp : y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors
  · simp only [if_pos hp,if_pos hp.1]
    calc
      _ ≤ (2/(p.val : ℝ)^2)*Real.log p.val :=
        mul_le_mul_of_nonneg_right (alignmentPrimeAverage_zero_bound hp2) hl
      _ ≤ 2*positiveLogTerm positiveUnit p.val := by
        simp only [positiveLogTerm,positiveUnit,if_neg p.property.ne_zero,mul_one,
          positiveLogKernel]
        have h := div_le_div_of_nonneg_right
          (show Real.log (p.val : ℝ) ≤ 1+Real.log p.val by linarith) (sq_nonneg (p.val : ℝ))
        convert! mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1
        ring
  · simp only [if_neg hp]
    split_ifs
    · exact mul_nonneg (by norm_num) (mul_nonneg (positiveLogKernel_nat_nonneg _)
        (positiveUnit_nonneg _))
    · norm_num

theorem absentPrimeLogTerm_summable (L : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    Summable (absentPrimeLogTerm L y) :=
  Summable.of_nonneg_of_le (absentPrimeLogTerm_nonneg L y) (absentPrimeLogTerm_bound L y)
    (((positiveUnit_tail_summable hy).mul_left 2).comp_injective
      (Subtype.val_injective (p := Nat.Prime)))

theorem absent_prime_log_sum_bound (L : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (∑' p : Nat.Primes, absentPrimeLogTerm L y p) ≤ 2*(2*Real.log y+3)/y := by
  have hs := (positiveUnit_tail_summable hy).mul_left 2
  have hnn (n : ℕ) : 0 ≤ 2*(if y < (n : ℝ) then positiveLogTerm positiveUnit n else 0) := by
    split_ifs
    · exact mul_nonneg (by norm_num) (mul_nonneg (positiveLogKernel_nat_nonneg _)
        (positiveUnit_nonneg _))
    · norm_num
  calc
    _ ≤ ∑' p : Nat.Primes, 2*(if y < (p.val : ℝ) then positiveLogTerm positiveUnit p.val else 0) :=
      (absentPrimeLogTerm_summable L hy).tsum_le_tsum (absentPrimeLogTerm_bound L y)
        (hs.comp_injective (Subtype.val_injective (p := Nat.Prime)))
    _ ≤ ∑' n : ℕ, 2*(if y < (n : ℝ) then positiveLogTerm positiveUnit n else 0) :=
      tsum_comp_le_tsum_of_inj hs hnn (Subtype.val_injective (p := Nat.Prime))
    _ = 2*positiveLogTail positiveUnit y := by rw [tsum_mul_left]; rfl
    _ ≤ 2*((2*Real.log y+3)/y) := mul_le_mul_of_nonneg_left (positiveUnit_tail_bound hy) (by norm_num)
    _ = _ := by ring

end NField.Alignment.CollisionAbsentPrimeSums
