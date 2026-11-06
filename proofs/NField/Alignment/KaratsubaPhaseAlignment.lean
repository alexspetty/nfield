/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaHolder

/-! # Explicit phase coefficients for the finite Holder argument -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaPhaseAlignment
open scoped BigOperators

def phaseAlign (z : ℂ) : ℂ := if z = 0 then 0 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

theorem norm_phaseAlign_le (z : ℂ) : ‖phaseAlign z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · simp [phaseAlign, hz, norm_ne_zero_iff.mpr hz]

theorem phaseAlign_mul (z : ℂ) : phaseAlign z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [phaseAlign, if_neg hz, div_mul_eq_mul_div,
      mul_comm ((starRingEnd ℂ) z) z, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    field_simp [hn]

theorem phaseAlign_power_mul (z : ℂ) (s : ℕ) :
    phaseAlign z ^ s * z ^ s = ((‖z‖ : ℂ) ^ s) := by
  rw [← mul_pow, phaseAlign_mul]

theorem norm_phaseAlign_power_le (z : ℂ) (s : ℕ) : ‖phaseAlign z ^ s‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_phaseAlign_le z) s

/-- All row norms are linearized by explicit coefficients, including zero rows. -/
theorem aligned_power_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) (s : ℕ) :
    (∑ i ∈ S, phaseAlign (f i) ^ s * f i ^ s) = ∑ i ∈ S, ((‖f i‖ : ℂ) ^ s) := by
  simp_rw [phaseAlign_power_mul]

theorem norm_aligned_power_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) (s : ℕ) :
    ‖∑ i ∈ S, phaseAlign (f i) ^ s * f i ^ s‖ = ∑ i ∈ S, ‖f i‖ ^ s := by
  rw [aligned_power_sum]
  have he : (∑ i ∈ S, ((‖f i‖ : ℂ) ^ s)) = ((∑ i ∈ S, ‖f i‖ ^ s : ℝ) : ℂ) := by simp
  rw [he]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg (norm_nonneg (f i)) s)]

/-- Holder's first row step with explicit bounded complex coefficients. -/
theorem linearized_holder {ι : Type*} (S : Finset ι) (f : ι → ℂ) {s : ℕ} (hs : 1 ≤ s) :
    ‖∑ i ∈ S, f i‖ ^ s ≤ (S.card : ℝ) ^ (s-1) *
      ‖∑ i ∈ S, phaseAlign (f i) ^ s * f i ^ s‖ := by
  rw [norm_aligned_power_sum]
  exact KaratsubaHolder.norm_sum_pow_le S f hs

end NField.Alignment.KaratsubaPhaseAlignment
