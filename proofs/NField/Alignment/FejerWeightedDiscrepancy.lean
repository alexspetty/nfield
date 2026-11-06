/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerWeightedWindow

/-! # Weighted strict-threshold discrepancy from positive Fourier smoothing -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FejerWeightedDiscrepancy
open FejerKernel FejerIntervalSmoothing FejerWindowFourier FejerWeightedWindow
open scoped BigOperators Classical

def spectralError {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) : ℝ :=
  ∑ k ∈ (frequencies H).erase 0, (1 / (Real.pi * |(k : ℝ)|)) *
    ‖∑ i ∈ s, (w i : ℂ) * fourier k (x i)‖

def thresholdSum {ι : Type*} (s : Finset ι) (w t : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (if Int.fract (t i) < α then 1 else 0)

theorem real_window_error {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) (hH : 0 < H) (a b : ℝ) :
    |(∑ i ∈ s, w i * window H a b (x i)) - (b-a)*(∑ i ∈ s, w i)| ≤
      spectralError s w x H := by
  have he := weighted_window_error_bound s w x H hH a b
  have hc : (((∑ i ∈ s, w i * window H a b (x i)) - (b-a)*(∑ i ∈ s, w i) : ℝ) : ℂ) =
      (∑ i ∈ s, (w i : ℂ)*(window H a b (x i) : ℂ)) -
        ((b-a : ℝ) : ℂ)*∑ i ∈ s, (w i : ℂ) := by push_cast; rfl
  rw [← hc, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

/-- A finite weighted discrepancy estimate with explicit smoothing radius
and retained-mass normalization. Strict threshold atoms are included. -/
theorem discrepancy_radius {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (H : ℕ) (hH : 0 < H) (δ α : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/2) (hscale : 1 < 2*(H : ℝ)*δ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |thresholdSum s w t α - α*(∑ i ∈ s, w i)| ≤
      ((2*δ + 1/(2*(H : ℝ)*δ))*(∑ i ∈ s, w i) +
        spectralError s w (fun i => (t i : AddCircle (1 : ℝ))) H) /
      (1 - 1/(2*(H : ℝ)*δ)) := by
  let d : ℝ := 1 - 1/(2*(H : ℝ)*δ)
  have hd : 0 < d := normalization_pos H δ hscale
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hu : thresholdSum s w t α * d ≤
      ∑ i ∈ s, w i * window H (-δ) (α+δ) (t i : AddCircle (1 : ℝ)) := by
    rw [thresholdSum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hh := threshold_upper H hH δ α (t i) hδ hδ' hscale hα0
    change _ ≤ window H (0-δ) (α+δ) _ / d at hh
    have hh' := (le_div_iff₀ hd).mp hh
    simpa only [zero_sub, mul_assoc] using mul_le_mul_of_nonneg_left hh' (hw i hi)
  have hl : ((∑ i ∈ s, w i) - thresholdSum s w t α) * d ≤
      ∑ i ∈ s, w i * window H (α-δ) (1+δ) (t i : AddCircle (1 : ℝ)) := by
    have hh : ∀ i ∈ s, w i * (1 - (if Int.fract (t i) < α then 1 else 0)) * d ≤
        w i * window H (α-δ) (1+δ) (t i : AddCircle (1 : ℝ)) := by
      intro i hi
      have hb := threshold_lower H hH δ α (t i) hδ hδ' hscale hα1
      have hb' : (1 - (if Int.fract (t i) < α then (1 : ℝ) else 0)) ≤
          window H (α-δ) (1+δ) (t i : AddCircle (1 : ℝ)) / d := by
        change 1 - window H (α-δ) (1+δ) _ / d ≤ _ at hb
        linarith
      have hc := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mp hb') (hw i hi)
      simpa only [mul_assoc] using hc
    have hs := Finset.sum_le_sum hh
    rw [← Finset.sum_mul] at hs
    simpa only [mul_sub, mul_one, Finset.sum_sub_distrib, thresholdSum] using hs
  have eu := (abs_le.mp (real_window_error s w (fun i => (t i : AddCircle (1 : ℝ))) H hH (-δ) (α+δ))).2
  have el := (abs_le.mp (real_window_error s w (fun i => (t i : AddCircle (1 : ℝ))) H hH (α-δ) (1+δ))).2
  have ht : 0 ≤ 1/(2*(H : ℝ)*δ) := by positivity
  have ha := mul_le_mul_of_nonneg_right hα1 ht
  have haW := mul_le_mul_of_nonneg_right ha hW
  have ha0 : 0 ≤ α*(1/(2*(H : ℝ)*δ))*(∑ i ∈ s, w i) := by positivity
  apply (abs_le).mpr
  constructor
  · apply neg_le.mpr
    apply (le_div_iff₀ hd).mpr
    dsimp only [d] at hu hl
    nlinarith
  · apply (le_div_iff₀ hd).mpr
    dsimp only [d] at hu hl
    nlinarith

/-- A uniform discrepancy bound at radius `1/sqrt(H)`, retaining both signs
of the nonzero frequencies in the explicit spectral error. -/
theorem discrepancy_sqrt {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (H : ℕ) (hH : 16 ≤ H) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |thresholdSum s w t α - α*(∑ i ∈ s, w i)| ≤
      4*(Real.sqrt (H : ℝ))⁻¹*(∑ i ∈ s, w i) +
        2*spectralError s w (fun i => (t i : AddCircle (1 : ℝ))) H := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hs0 := Real.sqrt_pos.mpr hH0
  have hs4 : 4 ≤ Real.sqrt (H : ℝ) := by
    apply (Real.le_sqrt (by norm_num) hH0.le).mpr
    exact_mod_cast hH
  let δ := (Real.sqrt (H : ℝ))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ4 : δ ≤ 1/4 := by
    dsimp [δ]
    rw [← one_div, div_le_iff₀ hs0]
    nlinarith
  have he : (H : ℝ)*δ = Real.sqrt (H : ℝ) := by
    dsimp [δ]
    rw [← div_eq_mul_inv]
    exact (div_eq_iff hs0.ne').mpr (by nlinarith [Real.sq_sqrt hH0.le])
  have hscale : 1 < 2*(H : ℝ)*δ := by nlinarith
  have ht : 1/(2*(H : ℝ)*δ) = δ/2 := by
    rw [mul_assoc, he]
    dsimp [δ]
    ring
  have hd : 0 < 1-δ/2 := by linarith
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hE : 0 ≤ spectralError s w (fun i => (t i : AddCircle (1 : ℝ))) H := by
    apply Finset.sum_nonneg
    intro k hk
    positivity
  have hb := discrepancy_radius s w t hw H (by omega) δ α hδ (by linarith) hscale hα0 hα1
  rw [ht] at hb
  apply hb.trans
  apply (div_le_iff₀ hd).mpr
  have hwδ := mul_le_mul_of_nonneg_right hδ4 hW
  have hwδδ := mul_le_mul_of_nonneg_left hwδ hδ.le
  have heδ := mul_le_mul_of_nonneg_right hδ4 hE
  nlinarith

end NField.Alignment.FejerWeightedDiscrepancy
