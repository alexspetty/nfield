/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeEnergyBound
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Factorial gain in the complete Taylor-error sum

Global factorial bounds retain the exponential factor in both factorials.
They reduce the actual remainder products to a geometric bound, uniformly
over all nonempty subsets of the partition factors.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperFactorialDecay

open scoped BigOperators
open HarperRemainderProduct HarperProductApproximation

theorem factorial_lower {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (by positivity) hs).trans
    (Stirling.le_factorial_stirling n)

theorem factorial_upper {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℝ) ≤ 6 * (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hseq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hthree : Stirling.stirlingSeq n ≤ 3 := by
    refine hseq.trans ?_
    rw [Stirling.stirlingSeq_one, div_le_iff₀ (by positivity)]
    linarith [Real.exp_one_lt_three]
  have hb := (div_le_iff₀ (by positivity :
    0 < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n)).mp hthree
  have hs : Real.sqrt (2 * (n : ℝ)) ≤ 2 * n :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  calc
    _ ≤ 3 * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := hb
    _ ≤ 3 * (2 * (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) := by gcongr
    _ = _ := by ring

theorem remainderScale_le {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hS : 0 < S) (hpref : 3 * (J : ℝ) ≤ delta * S) :
    remainderScale delta J S ≤ (Real.pi * Real.exp 1 / (delta * S)) ^ (2 * S) := by
  have hsR : (0 : ℝ) < S := by exact_mod_cast hS
  have hf := factorial_lower (Nat.mul_pos (by norm_num : 0 < 2) hS)
  have hratio : (2 * Real.pi / delta) / ((2 * (S : ℝ)) / Real.exp 1) =
      Real.pi * Real.exp 1 / (delta * S) := by field_simp
  have he : remainderScale delta J S =
      (3 * (J : ℝ) / (delta * S)) *
        ((2 * Real.pi / delta) ^ (2 * S) / ((2 * S).factorial : ℝ)) := by
    unfold remainderScale
    ring
  rw [he]
  calc
    _ ≤ (3 * (J : ℝ) / (delta * S)) *
        ((2 * Real.pi / delta) ^ (2 * S) / (((2 * S : ℕ) : ℝ) / Real.exp 1) ^ (2 * S)) := by
      gcongr
    _ = (3 * (J : ℝ) / (delta * S)) *
        (Real.pi * Real.exp 1 / (delta * S)) ^ (2 * S) := by
      rw [← div_pow]
      push_cast
      rw [hratio]
    _ ≤ _ := mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).mpr hpref)

theorem productBound_le {delta B : ℝ} (hd : 0 < delta) (hB : 0 ≤ B)
    {J S j : ℕ} (hS : 0 < S) (hj : 0 < j) (hpref : 3 * (J : ℝ) ≤ delta * S) :
    productBound delta J S j B ≤ 6 * (S : ℝ) * j *
      (Real.exp 1 * Real.pi ^ 2 * j * B / (delta ^ 2 * S)) ^ (S * j) := by
  have hsR : (0 : ℝ) < S := by exact_mod_cast hS
  have hpow : ((Real.pi * Real.exp 1 / (delta * S)) ^ (2 * S)) ^ j =
      ((Real.pi * Real.exp 1 / (delta * S)) ^ 2) ^ (S * j) := by
    simp only [← pow_mul, Nat.mul_assoc]
  have he : (Real.pi * Real.exp 1 / (delta * S)) ^ 2 *
      ((S : ℝ) * j / Real.exp 1) * B =
      Real.exp 1 * Real.pi ^ 2 * j * B / (delta ^ 2 * S) := by
    field_simp
  unfold productBound
  calc
    _ ≤ ((Real.pi * Real.exp 1 / (delta * S)) ^ (2 * S)) ^ j *
        (6 * ((S * j : ℕ) : ℝ) * (((S * j : ℕ) : ℝ) / Real.exp 1) ^ (S * j)) * B ^ (S * j) := by
      gcongr
      · exact remainderScale_nonneg hd J S
      · exact remainderScale_le hd hS hpref
      · exact factorial_upper (Nat.mul_pos hS hj)
    _ = _ := by
      rw [hpow, Nat.cast_mul]
      calc
        _ = (6 * (S : ℝ) * j) *
            (((Real.pi * Real.exp 1 / (delta * S)) ^ 2) ^ (S * j) *
              ((S : ℝ) * j / Real.exp 1) ^ (S * j) * B ^ (S * j)) := by ring
        _ = _ := by rw [← mul_pow, ← mul_pow, he]

theorem errorSum_nonneg {delta B : ℝ} (hd : 0 < delta) (hB : 0 ≤ B) (J S A : ℕ) :
    0 ≤ errorSum delta J S A B := by
  unfold errorSum productBound
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (by positivity [remainderScale_nonneg hd J S])

theorem errorSum_mono {delta B C : ℝ} (hd : 0 < delta) (hB : 0 ≤ B) (hBC : B ≤ C)
    (J S A : ℕ) : errorSum delta J S A B ≤ errorSum delta J S A C := by
  unfold errorSum productBound
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · rfl
  · gcongr
    positivity [remainderScale_nonneg hd J S]

theorem errorSum_geometric {delta B r : ℝ} (hd : 0 < delta) (hB : 0 ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {J S A : ℕ} (hS : 0 < S)
    (hpref : 3 * (J : ℝ) ≤ delta * S)
    (hbase : Real.exp 1 * Real.pi ^ 2 * A * B / (delta ^ 2 * S) ≤ r) :
    errorSum delta J S A B ≤ 6 * (S : ℝ) * A * 2 ^ A * r ^ S := by
  calc
    _ ≤ ∑ j ∈ Finset.range (A + 1), (A.choose j : ℝ) *
        (6 * (S : ℝ) * A * r ^ S) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hz : j = 0
      · simp only [hz, ↓reduceIte]
        positivity
      · rw [if_neg hz]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hjA : j ≤ A := by simpa using Finset.mem_range.mp hj
        have hjpos : 0 < j := Nat.pos_of_ne_zero hz
        refine (productBound_le hd hB hS hjpos hpref).trans ?_
        have hb : Real.exp 1 * Real.pi ^ 2 * j * B / (delta ^ 2 * S) ≤ r := by
          refine le_trans ?_ hbase
          gcongr
        have hpow := (pow_le_pow_left₀ (by positivity) hb (S * j)).trans
          (pow_le_pow_of_le_one hr0 hr1 (Nat.le_mul_of_pos_right S hjpos))
        gcongr
    _ = _ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

end NField.Alignment.HarperFactorialDecay
