/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.GrowingSigned
/-! # The complete complementary clock reading

Both remainders retain the actual source and the full nonunit clock grid.
The half-power equivalence does not supply the remaining complementary bound.
-/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open scoped BigOperators
open NField.Alignment AbsoluteForestWork SignedForestWork ClockRows

theorem normalized_first_power_bound {p : ℕ} (hp : 0 < p) (x C ε : ℝ)
    (h : |x| ≤ C*(p : ℝ)^(1+ε)) :
    |4*x/(p : ℝ)^2| ≤ 4*C*(p : ℝ)^(-1+ε) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ = 4*|x|/(p : ℝ)^2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
      norm_num
    _ ≤ 4*(C*(p : ℝ)^(1+ε))/(p : ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) (sq_nonneg _)
    _ = _ := by
      rw [show 4*(C*(p : ℝ)^(1+ε))/(p : ℝ)^2=(4*C)*((p : ℝ)^(1+ε)/(p : ℝ)^2) by ring,
        ← Real.rpow_two, ← Real.rpow_sub hpR, show (1+ε : ℝ)-2=-1+ε by ring]

theorem remainder_bound_from_signed {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (D : ℕ) (C ε : ℝ) (hε : 0 < ε)
    (hA : |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)| ≤ C*(p : ℝ)^(1+ε)) :
    |forestRemainder p D| ≤ (4*C+4)*(p : ℝ)^(-1+ε) := by
  have hinv : 1/(p : ℝ) ≤ (p : ℝ)^(-1+ε) := by
    calc
      _ = (p : ℝ)^(-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith)
  rw [forest_remainder_identity hp hodd]
  calc
    _ ≤ |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)/(p : ℝ)^2|+
        |-2/(p : ℝ)+1/(p : ℝ)^2-
          ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)| := abs_add_le _ _
    _ ≤ 4*C*(p : ℝ)^(-1+ε)+4/(p : ℝ) :=
      add_le_add (normalized_first_power_bound hp.pos _ _ _ hA) (PhasePopulations.smooth_correction_bound hp.one_le)
    _ ≤ 4*C*(p : ℝ)^(-1+ε)+4*(p : ℝ)^(-1+ε) := by
      apply add_le_add (le_refl _)
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 4 by norm_num)
    _ = _ := by ring

theorem growing_window_remainder {L : ℕ → ℕ} (hL : GrowingReturnWindow L) :
    PrimePowerRate (fun p => forestRemainder p (returnDivisor p (L p))) (-1) := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := growing_signed_and_restoration hL ε hε
  refine ⟨4*C+4, by positivity, ?_⟩
  intro p hp hodd
  exact remainder_bound_from_signed hp hodd _ C ε hε (hc p hp hodd).1

theorem growing_window_half_rate_iff {L : ℕ → ℕ} (hL : GrowingReturnWindow L) :
    PrimePowerRate centeredSamplingDefect (-1/2) ↔
      PrimePowerRate (fun p => otherForestReading p (returnDivisor p (L p))) (3/2) :=
  scaled_half_rate_iff _ _ (growing_window_remainder hL)

theorem growing_window_half_remainder {L : ℕ → ℕ} (hL : GrowingReturnWindow L) :
    PrimePowerRate (fun p => forestRemainder p (returnDivisor p (L p))) (-1/2) := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := growing_window_remainder hL ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp hodd
  exact (hc p hp hodd).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith)) hC.le)

def otherUnitClockReading (p D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 (p-1), if Core.forestMask (p-1) D d then 0 else PhasePopulations.fullClock (p-1) (p^2) d

def otherBinaryReading (p D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 (p-1), if Core.forestMask (p-1) D d then 0 else
    ∑ a ∈ Finset.Icc 1 ((d-1)/2),
      clockGamma p (a : ZMod d)*Core.completeCorrelation p a d

theorem other_unit_clock_binary {p : ℕ} (hp : p.Prime) (D : ℕ) :
    otherUnitClockReading p D=otherBinaryReading p D := by
  unfold otherUnitClockReading otherBinaryReading
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs
  · rfl
  · have hdI := Finset.mem_Icc.mp hd
    letI : NeZero d := ⟨by omega⟩
    apply complete_clock_binary_source hp.one_le
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0 < d)
      (by have := hp.two_le; omega))

theorem binary_remainder_identity {p : ℕ} (hp : p.Prime) (D : ℕ) :
    centeredSamplingDefect p-8*otherBinaryReading p D/(p : ℝ)^2 =
      forestRemainder p D+4*restorationWork (p-1) (p^2) D/(p : ℝ)^2 := by
  rw [← other_unit_clock_binary hp]
  have hN : 0 < p-1 := by have := hp.two_le; omega
  have ho := other_forest_restoration_identity hN (p^2) D
  change otherForestReading p D=2*otherUnitClockReading p D+restorationWork (p-1) (p^2) D at ho
  unfold forestRemainder
  rw [ho]
  ring

theorem binary_remainder_bound {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (D : ℕ)
    (C ε : ℝ) (hε : 0 < ε)
    (hA : |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)| ≤ C*(p : ℝ)^(1+ε))
    (hR : |restorationWork (p-1) (p^2) D| ≤ C*(p : ℝ)^(1+ε)) :
    |centeredSamplingDefect p-8*otherBinaryReading p D/(p : ℝ)^2| ≤
      (8*C+4)*(p : ℝ)^(-1+ε) := by
  rw [binary_remainder_identity hp]
  calc
    _ ≤ |forestRemainder p D|+|4*restorationWork (p-1) (p^2) D/(p : ℝ)^2| := abs_add_le _ _
    _ ≤ (4*C+4)*(p : ℝ)^(-1+ε)+(4*C)*(p : ℝ)^(-1+ε) :=
      add_le_add (remainder_bound_from_signed hp hodd D C ε hε hA)
        (normalized_first_power_bound hp.pos _ C ε hR)
    _ = _ := by ring

theorem growing_binary_remainder {L : ℕ → ℕ} (hL : GrowingReturnWindow L) :
    PrimePowerRate (fun p => centeredSamplingDefect p-
      8*otherBinaryReading p (returnDivisor p (L p))/(p : ℝ)^2) (-1) := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := growing_signed_and_restoration hL ε hε
  refine ⟨8*C+4, by positivity, ?_⟩
  intro p hp hodd
  exact binary_remainder_bound hp hodd _ C ε hε (hc p hp hodd).1 (hc p hp hodd).2

theorem polynomial_binary_remainder (K C₀ : ℝ) (hC₀ : 0 < C₀)
    (D : ℕ → ℕ)
    (hD : ∀ p : ℕ, p.Prime → p ≠ 2 → 1 ≤ D p ∧ (D p : ℝ) ≤ C₀*(p : ℝ)^K) :
    PrimePowerRate (fun p => centeredSamplingDefect p-8*otherBinaryReading p (D p)/(p : ℝ)^2) (-1) := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := polynomial_signed_and_restoration_any_exponent K C₀ ε hC₀ hε
  refine ⟨8*C+4, by positivity, ?_⟩
  intro p hp hodd
  have hb := hc p (D p) hp (hD p hp hodd).1 (hD p hp hodd).2
  exact binary_remainder_bound hp hodd _ C ε hε hb.1 hb.2

end NField.ResetForests.ReturnWindows
