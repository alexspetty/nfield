/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothRemoval

/-!
# Exact removal of the smooth part of the short sum

The retained coefficient vanishes exactly on the positive smooth integers.
At x=p-1 the two finite interval conventions agree. The literal sum splits
into retained and smooth parts, and a fixed-factor three-halves triangle
bound transfers this equality to normalized character moments.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRetainedSum

open scoped BigOperators
open HarperSmoothDivisor HarperSmoothCount HarperSmoothRemoval
  SpectralRepulsion CollisionCharacterStructure FiniteMagnitudeDecorrelation

def retainedCoefficient (y : ℝ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ smoothIntegers y then 0 else w n

theorem retainedCoefficient_norm_le (y : ℝ) (w : ℕ → ℂ) (n : ℕ) :
    ‖retainedCoefficient y w n‖ ≤ ‖w n‖ := by
  unfold retainedCoefficient
  split_ifs <;> simp

theorem smoothSet_at_base {p : ℕ} (hp : 1 ≤ p) (y : ℝ) :
    smoothSet ((p : ℝ)-1) y = (Finset.Icc 1 (p-1)).filter (· ∈ smoothIntegers y) := by
  have he : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by
    simp only [Nat.cast_sub hp, Nat.cast_one]
  have hx : ⌊(p : ℝ)-1⌋₊ = p-1 := by rw [← he]; simp
  ext n
  simp [smoothSet, hx, Nat.succ_le_iff]

theorem short_sum_split {p : ℕ} (hp : 1 ≤ p) (y : ℝ) (w z : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 (p-1), w n * z n) =
      (∑ n ∈ Finset.Icc 1 (p-1), retainedCoefficient y w n * z n) +
        ∑ n ∈ smoothSet ((p : ℝ)-1) y, w n * z n := by
  rw [smoothSet_at_base hp, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n ∈ smoothIntegers y <;> simp [retainedCoefficient, hn]

theorem norm_add_three_halves (a b : ℂ) :
    ‖a+b‖^(3/2 : ℝ) ≤ 2*‖a‖^(3/2 : ℝ) + 2*‖b‖^(3/2 : ℝ) := by
  have h : (‖a‖+‖b‖)^(3/2 : ℝ) ≤
      (2 : ℝ)^((3/2 : ℝ)-1) * (‖a‖^(3/2 : ℝ)+‖b‖^(3/2 : ℝ)) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖a‖₊ ‖b‖₊
      (by norm_num : (1 : ℝ) ≤ 3/2)
  have ht : (2 : ℝ)^((3/2 : ℝ)-1) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  calc
    _ ≤ (‖a‖+‖b‖)^(3/2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by norm_num)
    _ ≤ _ := h
    _ ≤ 2 * (‖a‖^(3/2 : ℝ)+‖b‖^(3/2 : ℝ)) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := by ring

theorem short_moment_split {p : ℕ} [NeZero (p^2)] (hp : 1 ≤ p) (y : ℝ) (w : ℕ → ℂ) :
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2 * uniformAverage (fun χ : Character (p^2) =>
        ‖∑ n ∈ Finset.Icc 1 (p-1), retainedCoefficient y w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) +
      2 * uniformAverage (fun χ : Character (p^2) =>
        ‖∑ n ∈ smoothSet ((p : ℝ)-1) y, w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) := by
  have h := average_mono (fun χ : Character (p^2) =>
    norm_add_three_halves
      (∑ n ∈ Finset.Icc 1 (p-1), retainedCoefficient y w n * χ (n : ZMod (p^2)))
      (∑ n ∈ smoothSet ((p : ℝ)-1) y, w n * χ (n : ZMod (p^2))))
  simp_rw [← short_sum_split hp y w] at h
  simpa only [uniformAverage_add, uniformAverage_mul_left] using h

theorem short_moment_removal {p : ℕ} [NeZero (p^2)] (hp : p.Prime)
    (y : ℝ) (w : ℕ → ℂ) (hw : ∀ n ∈ Finset.Icc 1 (p-1), ‖w n‖ ≤ 1) :
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2 * uniformAverage (fun χ : Character (p^2) =>
        ‖∑ n ∈ Finset.Icc 1 (p-1), retainedCoefficient y w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) +
      2 * (smoothCount ((p : ℝ)-1) y)^(3/4 : ℝ) := by
  have hs : ∀ n ∈ smoothSet ((p : ℝ)-1) y, ‖w n‖ ≤ 1 := by
    intro n hn
    rw [smoothSet_at_base hp.one_lt.le] at hn
    exact hw n (Finset.mem_filter.mp hn).1
  have hremoved := smooth_character_moment_bound hp y w hs
  have hsplit := short_moment_split hp.one_lt.le y w
  linarith

end NField.Alignment.HarperRetainedSum
