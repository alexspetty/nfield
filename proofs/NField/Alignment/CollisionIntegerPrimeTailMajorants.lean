/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLargePrimeFactors
import NField.Alignment.CollisionAmplitudeTail
import NField.Alignment.MobiusReciprocalSquare

/-!
# Integer majorants for the absent-prime tails

The bounds are uniform in every subset of primes. Their convergence and
rates come from actual nonnegative series over all positive integers.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIntegerPrimeTailMajorants

open scoped Classical
open Filter CollisionZetaMoments CollisionAmplitudeTail CollisionPositiveLogTail
open MobiusReciprocalSquare

def inverseSquareTailTerm (y : ℝ) (n : ℕ) : ℝ :=
  if y < (n : ℝ) then powerKernel 2 n else 0

theorem inverseSquareTailTerm_nonneg (y : ℝ) (n : ℕ) :
    0 ≤ inverseSquareTailTerm y n := by
  unfold inverseSquareTailTerm powerKernel
  split_ifs <;> positivity

theorem inverseSquareTailTerm_summable (y : ℝ) : Summable (inverseSquareTailTerm y) := by
  apply Summable.of_nonneg_of_le (inverseSquareTailTerm_nonneg y) _
    (powerKernel_summable (by norm_num : 1 < (2 : ℕ)))
  intro n
  unfold inverseSquareTailTerm
  split_ifs
  · rfl
  · unfold powerKernel
    positivity

theorem inverseSquareTailTerm_tsum {y : ℝ} (hy : 0 ≤ y) :
    (∑' n : ℕ, inverseSquareTailTerm y n)=
      ∑' n : ℕ, (((n+⌊y⌋₊+1 : ℕ) : ℝ)^(-2 : ℝ)) := by
  have hhead : (∑ n ∈ Finset.range (⌊y⌋₊+1), inverseSquareTailTerm y n)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n ≤ ⌊y⌋₊ := by simpa only [Finset.mem_range,Nat.lt_add_one_iff] using hn
    have hcast : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hn'
    have hnR : (n : ℝ) ≤ y := hcast.trans (Nat.floor_le hy)
    exact if_neg (not_lt.mpr hnR)
  have htail (n : ℕ) : inverseSquareTailTerm y (n+(⌊y⌋₊+1))=
      (((n+⌊y⌋₊+1 : ℕ) : ℝ)^(-2 : ℝ)) := by
    have hn : y < ((n+(⌊y⌋₊+1) : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.lt_floor_add_one y,Nat.cast_nonneg (α := ℝ) n]
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_two]
    simp only [inverseSquareTailTerm,if_pos hn,powerKernel,one_div,add_assoc]
  have h := (inverseSquareTailTerm_summable y).sum_add_tsum_nat_add (⌊y⌋₊+1)
  rw [hhead,zero_add] at h
  rw [← h]
  exact tsum_congr htail

theorem integer_inverse_square_tail_bound {y : ℝ} (hy : 2 ≤ y) :
    (∑' n : ℕ, inverseSquareTailTerm y n) ≤ 2/y := by
  have hy0 : 0 < y := by linarith
  have hfloor : 1 ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy0.le).mpr
    (by simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ y by linarith))
  have hfloor0 : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast (show 0 < ⌊y⌋₊ by omega)
  rw [inverseSquareTailTerm_tsum hy0.le]
  calc
    _ ≤ 1/(⌊y⌋₊ : ℝ) := shifted_reciprocal_square_tsum_le hfloor
    _ ≤ 2/y := by
      apply (div_le_div_iff₀ hfloor0 hy0).mpr
      have hf : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hfloor
      linarith [Nat.lt_floor_add_one y]

theorem logarithmic_integer_tail_bound {y : ℝ} (hy : 1 ≤ y) :
    (∑' n : ℕ, if y < (n : ℝ) then logSquareTerm n else 0) ≤ (2*Real.log y+3)/y := by
  have hbase := positiveUnit_tail_summable hy
  have hterm (n : ℕ) :
      (if y < (n : ℝ) then logSquareTerm n else 0) ≤
        (if y < (n : ℝ) then positiveLogTerm positiveUnit n else 0) := by
    by_cases hn : y < (n : ℝ)
    · have hn0 : n ≠ 0 := by intro h; simp [h] at hn; linarith
      simp only [if_pos hn,logSquareTerm,positiveLogTerm,positiveUnit,if_neg hn0,
        mul_one,positiveLogKernel]
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    · simp only [if_neg hn,le_refl]
  have hnonneg (n : ℕ) : 0 ≤ (if y < (n : ℝ) then logSquareTerm n else 0) := by
    unfold logSquareTerm
    split_ifs
    · exact div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)
    · rfl
  have hs := Summable.of_nonneg_of_le hnonneg hterm hbase
  exact (hs.tsum_le_tsum hterm hbase).trans (positiveUnit_tail_bound hy)

end NField.Alignment.CollisionIntegerPrimeTailMajorants
