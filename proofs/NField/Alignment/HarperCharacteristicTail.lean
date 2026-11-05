/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeRangeCharacteristic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform prime-range characteristic error from the lower cutoff

The elementary integral test bounds the finite q^(-3/2) error sum by
4/sqrt(Y) whenever every prime in the range exceeds Y>=2. Combining this
with the actual characteristic-function product comparison gives a
uniform cutoff estimate, with no prime-density estimate assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperCharacteristicTail
open scoped BigOperators Topology
open MeasureTheory Set HarperPrimeRangeCharacteristic HarperWeightedCharacteristic CollisionMertensInput

theorem shifted_three_halves_tail {N : ℕ} (hN : 0 < N) :
    (∑' k : ℕ, ((k+N+1 : ℕ) : ℝ)^(-(3/2 : ℝ))) ≤ 2*(N : ℝ)^(-(1/2 : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AntitoneOn (fun x : ℝ => x^(-(3/2 : ℝ))) (Ici (N : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le ha) hab (by norm_num)
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ)< -1) hNR
  have h := ha.tsum_comp_add_le_integral N hi
    (fun x hx => Real.rpow_nonneg (hNR.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ)< -1) hNR] at h
  norm_num at h
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

theorem finite_three_halves_tail {N : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (hS : ∀ q ∈ S, N < q) :
    (∑ q ∈ S, (q : ℝ)^(-(3/2 : ℝ))) ≤ 2*(N : ℝ)^(-(1/2 : ℝ)) := by
  have hi : Summable (fun k : ℕ => ((k+N+1 : ℕ) : ℝ)^(-(3/2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ)< -1)).comp_injective
      (fun a b h => by omega)
  calc
    _ = ∑ k ∈ S.image (fun q => q-(N+1)), ((k+N+1 : ℕ) : ℝ)^(-(3/2 : ℝ)) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro q hq
        have hn : q-(N+1)+N+1 = q := by have h := hS q hq; omega
        rw [hn]
      · intro a ha b hb he
        have h1 := hS a ha
        have h2 := hS b hb
        change a-(N+1) = b-(N+1) at he
        omega
    _ ≤ ∑' k : ℕ, ((k+N+1 : ℕ) : ℝ)^(-(3/2 : ℝ)) :=
      hi.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := shifted_three_halves_tail hN

theorem real_cutoff_three_halves_tail {Y : ℝ} (hY : 2 ≤ Y) (S : Finset ℕ)
    (hS : ∀ q ∈ S, Y < q) :
    (∑ q ∈ S, (q : ℝ)^(-(3/2 : ℝ))) ≤ 4*Y^(-(1/2 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hfloor : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hnext : Y < (⌊Y⌋₊ : ℝ)+1 := Nat.lt_floor_add_one Y
  have hN0 : (0 : ℝ) < ⌊Y⌋₊ := by linarith
  have hN : 0 < ⌊Y⌋₊ := by exact_mod_cast hN0
  have hS' : ∀ q ∈ S, ⌊Y⌋₊ < q := by
    intro q hq
    exact_mod_cast hfloor.trans_lt (hS q hq)
  apply (finite_three_halves_tail hN S hS').trans
  have hs : Real.sqrt Y ≤ 2*Real.sqrt (⌊Y⌋₊ : ℝ) := by
    nlinarith [Real.sq_sqrt hY0.le, Real.sq_sqrt hN0.le,
      Real.sqrt_nonneg Y, Real.sqrt_nonneg (⌊Y⌋₊ : ℝ)]
  rw [Real.rpow_neg hN0.le, Real.rpow_neg hY0.le, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]
  change 2/Real.sqrt (⌊Y⌋₊ : ℝ) ≤ 4/Real.sqrt Y
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hN0) (Real.sqrt_pos.mpr hY0)).mpr
  linarith

theorem rangeCharacteristic_cutoff_error (P : ℝ) {Y : ℝ} (hY : 2 ≤ Y)
    (S : Finset ℕ) (hS : S ⊆ primesUpTo P) (hSY : ∀ q ∈ S, Y < q)
    (t : ℕ → ℝ) {u : ℝ} (hu : |u| ≤ Real.sqrt Y) :
    ‖rangeCharacteristic P S t u-rangeGaussian S t u‖ ≤
      4*comparisonConstant*(|u|+|u|^3)*Y^(-(1/2 : ℝ)) := by
  have hq : ∀ q ∈ S, |u| ≤ Real.sqrt q :=
    fun q h => hu.trans (Real.sqrt_le_sqrt (hSY q h).le)
  calc
    _ ≤ comparisonConstant*(|u|+|u|^3)*(∑ q ∈ S, (q : ℝ)^(-(3/2 : ℝ))) :=
      rangeCharacteristic_gaussian_error P S hS t hq
    _ ≤ comparisonConstant*(|u|+|u|^3)*(4*Y^(-(1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (real_cutoff_three_halves_tail hY S hSY)
        (mul_nonneg comparisonConstant_pos.le (by positivity))
    _ = _ := by ring

end NField.Alignment.HarperCharacteristicTail
