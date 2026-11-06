/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerWindowFourier

/-! # Finite spectral errors for weighted interval windows -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FejerWeightedWindow
open MeasureTheory FejerKernel FejerIntervalSmoothing FejerWindowFourier
open scoped BigOperators Classical

def frequencies (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) H

theorem window_finite_series (H : ℕ) (a b : ℝ) (x : AddCircle (1 : ℝ)) :
    (window H a b x : ℂ) = ∑ k ∈ frequencies H,
      fourierCoeff (fun y => (window H a b y : ℂ)) k * fourier k x := by
  let f : C(AddCircle (1 : ℝ), ℂ) := ⟨_, continuous_window_complex H a b⟩
  have hz (k : ℤ) (hk : k ∉ frequencies H) : fourierCoeff f k = 0 := by
    apply window_coefficient_zero
    have hh : ¬ (-(H : ℤ) ≤ k ∧ k ≤ H) := by simpa [frequencies] using hk
    have hb : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
    have hc : -(k.natAbs : ℤ) ≤ k := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le k
    omega
  have hs : Summable (fourierCoeff f) := summable_of_ne_finset_zero hz
  have hp := has_pointwise_sum_fourier_series_of_summable hs x
  have hf : HasSum (fun k => fourierCoeff f k • fourier k x)
      (∑ k ∈ frequencies H, fourierCoeff f k • fourier k x) :=
    hasSum_sum_of_ne_finset_zero (s := frequencies H)
    (f := fun k => fourierCoeff f k • fourier k x) (fun k hk => by rw [hz k hk, zero_smul])
  simpa [f, smul_eq_mul] using hp.unique hf

/-- An exact identity for arbitrary real weights; positivity is only needed
when the interval majorants are applied later. -/
theorem weighted_window_identity {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) (a b : ℝ) :
    (∑ i ∈ s, (w i : ℂ) * (window H a b (x i) : ℂ)) =
      ∑ k ∈ frequencies H, fourierCoeff (fun y => (window H a b y : ℂ)) k *
        ∑ i ∈ s, (w i : ℂ) * fourier k (x i) := by
  have he : (∑ i ∈ s, (w i : ℂ) * (window H a b (x i) : ℂ)) =
      ∑ i ∈ s, (w i : ℂ) * (∑ k ∈ frequencies H,
        fourierCoeff (fun y => (window H a b y : ℂ)) k * fourier k (x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact window_finite_series H a b (x i)
  rw [he]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Remove the zero frequency to leave exactly the weighted error. -/
theorem weighted_window_error_identity {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) (hH : 0 < H) (a b : ℝ) :
    (∑ i ∈ s, (w i : ℂ) * (window H a b (x i) : ℂ)) -
        ((b-a : ℝ) : ℂ) * ∑ i ∈ s, (w i : ℂ) =
      ∑ k ∈ (frequencies H).erase 0,
        fourierCoeff (fun y => (window H a b y : ℂ)) k *
          ∑ i ∈ s, (w i : ℂ) * fourier k (x i) := by
  have h0 : (0 : ℤ) ∈ frequencies H := by simp [frequencies]
  have he := Finset.sum_erase_add (frequencies H)
    (fun k => fourierCoeff (fun y => (window H a b y : ℂ)) k *
      ∑ i ∈ s, (w i : ℂ) * fourier k (x i)) h0
  have hc : fourierCoeff (fun y => (window H a b y : ℂ)) 0 = ((b-a : ℝ) : ℂ) := by
    simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]
    rw [integral_complex_ofReal, window_mean H hH]
  rw [hc] at he
  simp only [fourier_zero, mul_one] at he
  rw [weighted_window_identity]
  exact eq_sub_iff_add_eq.mpr he |>.symm

/-- Uniform spectral error for arbitrary real sample weights. -/
theorem weighted_window_error_bound {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) (hH : 0 < H) (a b : ℝ) :
    ‖(∑ i ∈ s, (w i : ℂ) * (window H a b (x i) : ℂ)) -
        ((b-a : ℝ) : ℂ) * ∑ i ∈ s, (w i : ℂ)‖ ≤
      ∑ k ∈ (frequencies H).erase 0,
        (1 / (Real.pi * |(k : ℝ)|)) * ‖∑ i ∈ s, (w i : ℂ) * fourier k (x i)‖ := by
  rw [weighted_window_error_identity s w x H hH]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (window_coefficient_norm H a b k (Finset.mem_erase.mp hk).1) (norm_nonneg _)

end NField.Alignment.FejerWeightedWindow
