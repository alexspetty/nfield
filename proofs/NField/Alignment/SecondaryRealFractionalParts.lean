/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryTermUnconditional

/-! # The weighted fractional-part sum at arbitrary real arguments -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryRealFractionalParts
open scoped BigOperators Topology
open Filter ReducedHarmonicMobius SecondaryCapacityLedger

def weightedFractionalParts (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (harmonic (n-1) : ℝ)/(n : ℝ)*Int.fract (x/n)

theorem weightedFractionalParts_quotient (N d : ℕ) :
    weightedFractionalParts ((N : ℝ)/d) = weightedFractionalPartsAtQuotient N d := by
  unfold weightedFractionalParts weightedFractionalPartsAtQuotient
  rw [Nat.floor_div_natCast, Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro n hn
  rw [SaffariVaughanFiniteReduction.quotient_eq_fract, div_div, Nat.cast_mul]

/-- Title: `Möbius reduction at the exact rational argument`. -/
theorem mobius_reduction (N : ℕ) :
    fractionalFloorTerm N = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2*weightedFractionalParts ((N : ℝ)/d) := by
  rw [ReducedHarmonicMobius.mobius_reduction]
  simp only [exactMobiusFractionalTransform, weightedFractionalParts_quotient]

theorem fract_div_floor {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Int.fract (x/n) = Int.fract ((⌊x⌋₊ : ℝ)/n)+(x-⌊x⌋₊)/n := by
  have hf : Int.floor (x/n) = Int.floor ((⌊x⌋₊ : ℝ)/n) := by
    rw [Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_natCast,
      Int.natCast_floor_eq_floor hx]
  unfold Int.fract
  rw [hf]
  ring

theorem weightedFractionalParts_floor (x : ℝ) (hx : 0 ≤ x) :
    weightedFractionalParts x = weightedFractionalPartsAtQuotient ⌊x⌋₊ 1 +
      (x-⌊x⌋₊)*∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (harmonic (n-1) : ℝ)/(n : ℝ)^2 := by
  simp only [weightedFractionalParts, weightedFractionalPartsAtQuotient, Nat.div_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fract_div_floor hx, SaffariVaughanFiniteReduction.quotient_eq_fract]
  simp only [one_mul]
  ring

theorem harmonic_real_le_index (n : ℕ) : (harmonic n : ℝ) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : ((n+1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_pos n
    simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    push_cast at hi ⊢
    linarith

theorem weightedFractionalParts_floor_error {x : ℝ} (hx : 1 ≤ x) :
    |weightedFractionalParts x-weightedFractionalPartsAtQuotient ⌊x⌋₊ 1| ≤
      1+Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hδ0 : 0 ≤ x-(⌊x⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hx0)
  have hδ1 : x-(⌊x⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one x]
  have hw0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (harmonic (n-1) : ℝ)/(n : ℝ)^2 := by
    apply Finset.sum_nonneg
    intro n hn
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hw : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (harmonic (n-1) : ℝ)/(n : ℝ)^2) ≤ (harmonic ⌊x⌋₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hh : (harmonic (n-1) : ℝ) ≤ n :=
      (harmonic_real_le_index _).trans (by exact_mod_cast Nat.sub_le n 1)
    calc
      _ ≤ (n : ℝ)/(n : ℝ)^2 := by gcongr
      _ = (n : ℝ)⁻¹ := by field_simp
  rw [weightedFractionalParts_floor x hx0, add_sub_cancel_left, abs_of_nonneg (mul_nonneg hδ0 hw0)]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (harmonic (n-1) : ℝ)/(n : ℝ)^2 :=
      mul_le_of_le_one_left hw0 hδ1
    _ ≤ (harmonic ⌊x⌋₊ : ℝ) := hw
    _ ≤ 1+Real.log x := harmonic_floor_le_one_add_log x hx

theorem floor_log_square_error {x : ℝ} (hx : 3 ≤ x) :
    |Real.log (⌊x⌋₊ : ℝ)^2-Real.log x^2| ≤ 2*Real.log x := by
  have hx0 : 0 < x := by linarith
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hnR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hlow : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg hnR
  have hmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log hn0 (Nat.floor_le hx0.le)
  have htwice : x ≤ 2*(⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have hupp := Real.log_le_log hx0 htwice
  rw [Real.log_mul (by norm_num) hn0.ne'] at hupp
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  rw [abs_of_nonpos (by nlinarith : Real.log (⌊x⌋₊ : ℝ)^2-Real.log x^2 ≤ 0)]
  nlinarith [mul_nonneg (show 0 ≤ 1-(Real.log x-Real.log (⌊x⌋₊ : ℝ)) by linarith)
    (show 0 ≤ Real.log x+Real.log (⌊x⌋₊ : ℝ) by linarith)]

/-- Title: `Weighted fractional parts at real cutoffs`. -/
theorem weighted_fractional_parts :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |weightedFractionalParts x-(1/4 : ℝ)*Real.log x^2| ≤
        C*Real.rpow (Real.log x) (5/3 : ℝ) := by
  rcases SecondaryTermUnconditional.weighted_fractional_parts with ⟨C,hC,N₀,hbound⟩
  refine ⟨C+3, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (3 : ℝ) N₀)] with x hx
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hxN : (N₀ : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hnN : N₀ ≤ ⌊x⌋₊ := Nat.le_floor hxN
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hnR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg hnR
  have hlogx : 1 ≤ Real.log x :=
    (by linarith [Real.log_three_gt_d9] : (1 : ℝ) ≤ Real.log 3).trans
      (Real.log_le_log (by norm_num) hx3)
  have hmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by linarith) (Nat.floor_le hx0.le)
  have hpmono := Real.rpow_le_rpow hlogn hmono (by norm_num : (0 : ℝ) ≤ 5/3)
  have hpower := Real.self_le_rpow_of_one_le hlogx (by norm_num : (1 : ℝ) ≤ 5/3)
  change Real.rpow (Real.log (⌊x⌋₊ : ℝ)) (5/3 : ℝ) ≤
    Real.rpow (Real.log x) (5/3 : ℝ) at hpmono
  change Real.log x ≤ Real.rpow (Real.log x) (5/3 : ℝ) at hpower
  have hnBound := hbound ⌊x⌋₊ hnN
  change |weightedFractionalPartsAtQuotient ⌊x⌋₊ 1-
      (1/4 : ℝ)*Real.log (⌊x⌋₊ : ℝ)^2| ≤
      C*Real.rpow (Real.log (⌊x⌋₊ : ℝ)) (5/3 : ℝ) at hnBound
  have hmain : |(1/4 : ℝ)*Real.log (⌊x⌋₊ : ℝ)^2-
      (1/4 : ℝ)*Real.log x^2| ≤ (1/2 : ℝ)*Real.log x := by
    rw [← mul_sub, abs_mul]
    norm_num
    linarith [floor_log_square_error hx3]
  calc
    _ ≤ |weightedFractionalParts x-weightedFractionalPartsAtQuotient ⌊x⌋₊ 1| +
        |weightedFractionalPartsAtQuotient ⌊x⌋₊ 1-(1/4 : ℝ)*Real.log (⌊x⌋₊ : ℝ)^2| +
        |(1/4 : ℝ)*Real.log (⌊x⌋₊ : ℝ)^2-(1/4 : ℝ)*Real.log x^2| := by
      linarith [abs_sub_le (weightedFractionalParts x)
        (weightedFractionalPartsAtQuotient ⌊x⌋₊ 1) ((1/4 : ℝ)*Real.log x^2),
        abs_sub_le (weightedFractionalPartsAtQuotient ⌊x⌋₊ 1)
        ((1/4 : ℝ)*Real.log (⌊x⌋₊ : ℝ)^2) ((1/4 : ℝ)*Real.log x^2)]
    _ ≤ (1+Real.log x)+C*Real.rpow (Real.log (⌊x⌋₊ : ℝ)) (5/3 : ℝ)+
        (1/2 : ℝ)*Real.log x :=
      add_le_add (add_le_add (weightedFractionalParts_floor_error (by linarith)) hnBound) hmain
    _ ≤ (C+3)*Real.rpow (Real.log x) (5/3 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hpmono hC]

end NField.Alignment.SecondaryRealFractionalParts
