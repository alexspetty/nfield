/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.WeightedFractionalPartTransfer

/-! # Exact finite reduction for the logarithmically weighted distribution

The centered fractional part here is fract(t)-1/2, including at integers.
It is not the Dedekind sawtooth with value zero at integers. Strict
thresholds and both alpha endpoints are retained throughout.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SaffariVaughanFiniteReduction
open ReducedHarmonicMobius WeightedFractionalPartTransfer
open scoped BigOperators Classical

def centeredFraction (t : ℝ) : ℝ := Int.fract t-1/2

def shiftedWeightedSum (N d Y : ℕ) (β : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y,
    (n : ℝ)⁻¹*centeredFraction ((N : ℝ)/((d*n : ℕ) : ℝ)-β)

/-- The rational remainder representation is exactly Mathlib's fractional part. -/
theorem quotient_eq_fract (N d n : ℕ) :
    quotientFractionalPart N d n = Int.fract ((N : ℝ)/((d*n : ℕ) : ℝ)) := by
  exact Int.fract_div_natCast_eq_div_natCast_mod.symm

/-- The strict threshold indicator is an exact difference of shifted centered fractions. -/
theorem threshold_identity (t α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (if Int.fract t < α then (1 : ℝ) else 0) =
      α+centeredFraction (t-α)-centeredFraction t := by
  have hf0 := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  by_cases h : Int.fract t < α
  · have he : Int.floor (t-α) = Int.floor t-1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      dsimp only [Int.fract] at hf0 hf1 h
      constructor <;> linarith
    rw [if_pos h]
    unfold centeredFraction Int.fract
    rw [he]
    push_cast
    ring
  · have he : Int.floor (t-α) = Int.floor t := by
      apply Int.floor_eq_iff.mpr
      dsimp only [Int.fract] at hf0 hf1 h
      constructor <;> linarith
    rw [if_neg h]
    unfold centeredFraction Int.fract
    rw [he]
    ring

/-- The actual distribution sum is a harmonic main term plus two exact shifted sums. -/
theorem distribution_identity (N d Y : ℕ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    weightedFractionalDistribution N d Y α =
      α*(harmonic Y : ℝ)+shiftedWeightedSum N d Y α-shiftedWeightedSum N d Y 0 := by
  have hH : (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold weightedFractionalDistribution shiftedWeightedSum
  simp_rw [quotient_eq_fract, threshold_identity _ α hα0 hα1]
  rw [hH]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [sub_zero]
  ring

/-- The elementary harmonic correction has absolute size at most one. -/
theorem harmonic_correction (Y : ℕ) (hY : 1 ≤ Y) :
    |(harmonic Y : ℝ)-Real.log Y| ≤ 1 := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlog := Real.log_le_log hY0 (show (Y : ℝ) ≤ (Y : ℝ)+1 by linarith)
  have hlo := log_add_one_le_harmonic Y
  push_cast at hlo
  have hhi := harmonic_le_one_add_log Y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The finite discrepancy reduces to uniform bounds for the two actual shifted prefixes. -/
theorem discrepancy_le_shifted (N d Y : ℕ) (hY : 1 ≤ Y)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |weightedFractionalDistribution N d Y α-α*Real.log Y| ≤
      1+|shiftedWeightedSum N d Y α|+|shiftedWeightedSum N d Y 0| := by
  rw [distribution_identity N d Y α hα0 hα1]
  have hh : |α*((harmonic Y : ℝ)-Real.log Y)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hα0]
    have ha := mul_le_mul hα1 (harmonic_correction Y hY) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using ha
  calc
    _ = |α*((harmonic Y : ℝ)-Real.log Y)+shiftedWeightedSum N d Y α-shiftedWeightedSum N d Y 0| := by congr 1; ring
    _ ≤ |α*((harmonic Y : ℝ)-Real.log Y)+shiftedWeightedSum N d Y α|+|shiftedWeightedSum N d Y 0| := by simpa using (abs_sub_le (α*((harmonic Y : ℝ)-Real.log Y)+shiftedWeightedSum N d Y α) 0 (shiftedWeightedSum N d Y 0))
    _ ≤ (|α*((harmonic Y : ℝ)-Real.log Y)|+|shiftedWeightedSum N d Y α|)+|shiftedWeightedSum N d Y 0| :=
      by have hh := abs_add_le (α*((harmonic Y : ℝ)-Real.log Y)) (shiftedWeightedSum N d Y α); linarith
    _ ≤ _ := by linarith

/-- Each distribution value lies between zero and the full harmonic population. -/
theorem distribution_bounds (N d Y : ℕ) (α : ℝ) :
    0 ≤ weightedFractionalDistribution N d Y α ∧
      weightedFractionalDistribution N d Y α ≤ (harmonic Y : ℝ) := by
  have hH : (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold weightedFractionalDistribution
  constructor
  · exact Finset.sum_nonneg (fun n hn => by positivity)
  · rw [hH]
    apply Finset.sum_le_sum
    intro n hn
    split_ifs <;> simp only [mul_one, mul_zero, le_refl, inv_nonneg, Nat.cast_nonneg]

/-- The distribution error scale is at least one throughout the source domain. -/
theorem scale_ge_one (N d : ℕ) (hd : 0 < d) (hN : 3*d ≤ N) :
    1 ≤ fractionalDistributionScale N d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNX : (3 : ℝ) ≤ (N : ℝ)/d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast hN
  have hx : 0 < (N : ℝ)/d := by linarith
  have hlog : 1 ≤ Real.log ((N : ℝ)/d) :=
    (Real.le_log_iff_exp_le hx).mpr ((Real.exp_one_lt_three.le).trans hNX)
  unfold fractionalDistributionScale
  simpa only [Real.rpow_eq_pow] using Real.one_le_rpow hlog (by norm_num : (0 : ℝ) ≤ 2/3)

/-- The short logarithmic range of the actual Saffari-Vaughan target is unconditional. -/
theorem small_logarithmic_range (N d Y : ℕ) (hd : 0 < d) (hN : 3*d ≤ N)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hshort : Real.log Y ≤ fractionalDistributionScale N d) :
    |weightedFractionalDistribution N d Y α-α*Real.log Y| ≤
      2*fractionalDistributionScale N d := by
  have hscale := scale_ge_one N d hd hN
  have hLY : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  have hdist := distribution_bounds N d Y α
  have hH := harmonic_le_one_add_log Y
  have halpha : 0 ≤ α*Real.log Y ∧ α*Real.log Y ≤ Real.log Y := by
    constructor
    · positivity
    · nlinarith
  have habs : |weightedFractionalDistribution N d Y α-α*Real.log Y| ≤ 1+Real.log Y :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- The zero threshold contributes nothing, including at integral reciprocal arguments. -/
theorem distribution_zero (N d Y : ℕ) : weightedFractionalDistribution N d Y 0 = 0 := by
  unfold weightedFractionalDistribution
  apply Finset.sum_eq_zero
  intro n hn
  have hh : ¬quotientFractionalPart N d n < 0 := by
    rw [quotient_eq_fract]
    exact not_lt_of_ge (Int.fract_nonneg _)
  rw [if_neg hh, mul_zero]

/-- The unit threshold includes every term, including at integral reciprocal arguments. -/
theorem distribution_one (N d Y : ℕ) : weightedFractionalDistribution N d Y 1 = (harmonic Y : ℝ) := by
  have hH : (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH]
  unfold weightedFractionalDistribution
  apply Finset.sum_congr rfl
  intro n hn
  have hh : quotientFractionalPart N d n < 1 := by
    rw [quotient_eq_fract]
    exact Int.fract_lt_one _
  rw [if_pos hh, mul_one]

/-- Only a difference of shifted prefixes is needed for the distribution theorem. -/
theorem discrepancy_le_difference (N d Y : ℕ) (hY : 1 ≤ Y)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |weightedFractionalDistribution N d Y α-α*Real.log Y| ≤
      1+|shiftedWeightedSum N d Y α-shiftedWeightedSum N d Y 0| := by
  rw [distribution_identity N d Y α hα0 hα1]
  have hh : |α*((harmonic Y : ℝ)-Real.log Y)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hα0]
    have ha := mul_le_mul hα1 (harmonic_correction Y hY) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using ha
  calc
    _ = |α*((harmonic Y : ℝ)-Real.log Y)+(shiftedWeightedSum N d Y α-shiftedWeightedSum N d Y 0)| := by congr 1; ring
    _ ≤ |α*((harmonic Y : ℝ)-Real.log Y)|+|shiftedWeightedSum N d Y α-shiftedWeightedSum N d Y 0| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- A proved uniform shifted-difference estimate would discharge this source input. -/
theorem discrepancy_of_difference_bound (N d Y : ℕ) (hd : 0 < d) (hN : 3*d ≤ N)
    (hY : 1 ≤ Y) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (K : ℝ)
    (hshift : |shiftedWeightedSum N d Y α-shiftedWeightedSum N d Y 0| ≤
      K*fractionalDistributionScale N d) :
    |weightedFractionalDistribution N d Y α-α*Real.log Y| ≤
      (1+K)*fractionalDistributionScale N d := by
  have hh := discrepancy_le_difference N d Y hY α hα0 hα1
  have hs := scale_ge_one N d hd hN
  nlinarith

end NField.Alignment.SaffariVaughanFiniteReduction
