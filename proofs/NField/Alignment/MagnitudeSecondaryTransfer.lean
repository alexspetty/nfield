/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeMomentArithmetic

/-! # Exact rational normalization of the secondary energy expansion

These estimates retain the energy error as an explicit input. They do not
assert the Saffari--Vaughan estimate. The rational denominators
are the exact denominators of the manuscript's two magnitude observables.
-/

noncomputable section
namespace NField.Alignment.MagnitudeSecondaryTransfer

theorem mixed_secondary_transfer {b A E L S C : ℝ}
    (hb : 2 ≤ b) (hA : 0 < A) (hS : 1 ≤ S) (hL0 : 0 ≤ L)
    (hL : L ≤ b*S) (hC : 0 ≤ C)
    (hE : |E-(b^3-A⁻¹*b^2*L)| ≤ C*b^2*S) :
    |A*E/(2*b^2*(b-1))-(A/2-L/(2*b))| ≤ (A*C+A+1)*S/b := by
  have hb0 : 0 < b := by linarith
  have hbm : 0 < b-1 := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hid : A*E/(2*b^2*(b-1))-(A/2-L/(2*b)) =
      A*(E-(b^3-A⁻¹*b^2*L))/(2*b^2*(b-1)) +
        (A*b-L)/(2*b*(b-1)) := by
    field_simp [hb0.ne',hbm.ne',hA.ne']
    ring
  have hfirst : |A*(E-(b^3-A⁻¹*b^2*L))/(2*b^2*(b-1))| ≤ A*C*S/b := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos (by positivity : 0 < 2*b^2*(b-1))]
    calc
      _ ≤ A*(C*b^2*S)/(2*b^2*(b-1)) := by gcongr
      _ = A*C*S/(2*(b-1)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hb0 (by linarith)
  have hsecond : |(A*b-L)/(2*b*(b-1))| ≤ (A+1)*S/b := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2*b*(b-1))]
    have hnum : |A*b-L| ≤ A*b+L := by
      simpa only [sub_zero,zero_sub,abs_neg,
        abs_of_nonneg (mul_nonneg hA.le hb0.le),abs_of_nonneg hL0] using
        abs_sub_le (A*b) 0 L
    calc
      _ ≤ (A*b+L)/(2*b*(b-1)) := by gcongr
      _ ≤ (A*b+b*S)/(2*b*(b-1)) := by gcongr
      _ ≤ (A*b+b*S)/b^2 := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (by nlinarith)
      _ = (A+S)/b := by field_simp
      _ ≤ (A+1)*S/b := by
        apply div_le_div_of_nonneg_right _ hb0.le
        nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hS)]
  rw [hid]
  calc
    _ ≤ |A*(E-(b^3-A⁻¹*b^2*L))/(2*b^2*(b-1))|+
        |(A*b-L)/(2*b*(b-1))| := abs_add_le _ _
    _ ≤ A*C*S/b+(A+1)*S/b := add_le_add hfirst hsecond
    _ = _ := by ring

theorem ratio_secondary_transfer {b A E L S C : ℝ}
    (hb : 2 ≤ b) (hA : 0 < A) (hS : 1 ≤ S) (hL0 : 0 ≤ L)
    (hL : L ≤ b*S) (hC : 0 ≤ C)
    (hE : |E-(b^3-A⁻¹*b^2*L)| ≤ C*b^2*S) :
    |3*E/((b-1)*(b^2-1))-(3-3/A*L/b)| ≤
      (12*C+24+24/A)*S/b := by
  have hb0 : 0 < b := by linarith
  have hbm : 0 < b-1 := by linarith
  have hb2 : 0 < b^2-1 := by nlinarith
  have hS0 : 0 ≤ S := by linarith
  let D := (b-1)*(b^2-1)
  have hD : 0 < D := mul_pos hbm hb2
  have hDlo : b^3/4 ≤ D := by
    have h1 : b/2 ≤ b-1 := by linarith
    have h2 : b^2/2 ≤ b^2-1 := by nlinarith
    have hmul := mul_le_mul h1 h2 (by positivity : 0 ≤ b^2/2) hbm.le
    dsimp [D]
    nlinarith
  have hdelta : 0 ≤ b^3-D ∧ b^3-D ≤ 2*b^2 := by
    dsimp [D]
    constructor <;> nlinarith
  have hid : 3*E/D-(3-3/A*L/b) =
      3*(E-(b^3-A⁻¹*b^2*L))/D +
        (3-3/A*L/b)*(b^3-D)/D := by
    field_simp [hb0.ne',hD.ne',hA.ne']
    ring
  have hfirst : |3*(E-(b^3-A⁻¹*b^2*L))/D| ≤ 12*C*S/b := by
    rw [abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc
      _ ≤ 3*(C*b^2*S)/D := by gcongr
      _ ≤ 3*(C*b^2*S)/(b^3/4) := div_le_div_of_nonneg_left
        (by positivity) (by positivity) hDlo
      _ = _ := by field_simp; ring
  have hbase : |3-3/A*L/b| ≤ (3+3/A)*S := by
    have hfrac : 3/A*L/b ≤ 3/A*S := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hb0).mpr (by nlinarith [hL])
    calc
      _ ≤ 3+3/A*L/b := by
        simpa only [sub_zero,zero_sub,abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 3),
          abs_of_nonneg (by positivity : 0 ≤ 3/A*L/b)] using abs_sub_le (3 : ℝ) 0 (3/A*L/b)
      _ ≤ 3+3/A*S := by linarith
      _ ≤ _ := by nlinarith
  have hsecond : |(3-3/A*L/b)*(b^3-D)/D| ≤ (24+24/A)*S/b := by
    rw [abs_div,abs_mul,abs_of_pos hD,abs_of_nonneg hdelta.1]
    calc
      _ ≤ ((3+3/A)*S)*(2*b^2)/D := by
        apply div_le_div_of_nonneg_right _ hD.le
        exact mul_le_mul hbase hdelta.2 hdelta.1 (by positivity)
      _ ≤ ((3+3/A)*S)*(2*b^2)/(b^3/4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hDlo
      _ = _ := by field_simp; ring
  change |3*E/D-(3-3/A*L/b)| ≤ _
  rw [hid]
  calc
    _ ≤ |3*(E-(b^3-A⁻¹*b^2*L))/D|+|(3-3/A*L/b)*(b^3-D)/D| := abs_add_le _ _
    _ ≤ 12*C*S/b+(24+24/A)*S/b := add_le_add hfirst hsecond
    _ = _ := by ring

end NField.Alignment.MagnitudeSecondaryTransfer
