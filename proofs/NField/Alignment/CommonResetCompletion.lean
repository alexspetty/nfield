/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanGlobalBound

/-! # Completion of the actual reciprocal phase with every linear twist -/

noncomputable section

namespace NField.Alignment.CommonResetCompletion

open scoped BigOperators
open InverseAdditiveCompletion KloostermanGlobalBound

theorem weighted_fourier_completion {q : ℕ} [NeZero q] {α : Type*}
    (S : Finset α) (address : α → ZMod q) (w : α → ℂ) (f : ZMod q → ℂ) :
    (∑ a ∈ S, f (address a)*w a) =
      (q : ℂ)⁻¹*∑ h : ZMod q, ZMod.dft f h*
        ∑ a ∈ S, ZMod.stdAddChar (h*address a)*w a := by
  have hinv (x : ZMod q) : f x = (q : ℂ)⁻¹*∑ h : ZMod q,
      ZMod.stdAddChar (h*x)*ZMod.dft f h := by
    have hi := congrFun (ZMod.dft.symm_apply_apply f) x
    rw [ZMod.invDFT_apply] at hi
    simpa only [smul_eq_mul] using hi.symm
  simp_rw [hinv]
  simp only [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Title: `The actual normalized reciprocal Fourier coefficients obey the uniform Kloosterman bound`. -/
theorem reciprocal_coefficient_bound {q : ℕ} [NeZero q] (n h : ZMod q) :
    ‖(q : ℂ)⁻¹*ZMod.dft (inversePhase 1 n) h‖ ≤
      (4*Real.sqrt (q : ℝ)*q.divisors.card*Real.sqrt (Nat.gcd n.val q : ℝ))/(q : ℝ) := by
  rw [norm_mul, norm_inv, Complex.norm_natCast, inverse_phase_dft]
  have hb := complete_inverse_sum_bound q 1 n h (by simp)
  calc
    _ ≤ (q : ℝ)⁻¹*(4*Real.sqrt (q : ℝ)*q.divisors.card*
        Real.sqrt (Nat.gcd n.val q : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Title: `Exact completion retains every linear twist over the whole interval`. -/
theorem reciprocal_weighted_completion {q : ℕ} [NeZero q] {α : Type*}
    (S : Finset α) (address : α → ZMod q) (w : α → ℂ) (n : ZMod q) :
    (∑ a ∈ S, inversePhase 1 n (address a)*w a) =
      ∑ h : ZMod q, ((q : ℂ)⁻¹*completeInverseSum 1 n h)*
        ∑ a ∈ S, ZMod.stdAddChar (h*address a)*w a := by
  rw [weighted_fourier_completion]
  simp only [inverse_phase_dft, Finset.mul_sum, mul_assoc]

/-- Title: `The completed reciprocal sum is bounded by the actual sum of linear twists`. -/
theorem reciprocal_twist_mass_bound {q : ℕ} [NeZero q] {α : Type*}
    (S : Finset α) (address : α → ZMod q) (w : α → ℂ) (n : ZMod q) :
    ‖∑ a ∈ S, inversePhase 1 n (address a)*w a‖ ≤
      (4*Real.sqrt (q : ℝ)*q.divisors.card*Real.sqrt (Nat.gcd n.val q : ℝ))/(q : ℝ)*
        ∑ h : ZMod q, ‖∑ a ∈ S, ZMod.stdAddChar (h*address a)*w a‖ := by
  rw [reciprocal_weighted_completion]
  calc
    _ ≤ ∑ h : ZMod q, ‖((q : ℂ)⁻¹*completeInverseSum 1 n h)*
        ∑ a ∈ S, ZMod.stdAddChar (h*address a)*w a‖ := norm_sum_le _ _
    _ ≤ ∑ h : ZMod q,
        ((4*Real.sqrt (q : ℝ)*q.divisors.card*Real.sqrt (Nat.gcd n.val q : ℝ))/(q : ℝ))*
          ‖∑ a ∈ S, ZMod.stdAddChar (h*address a)*w a‖ := by
      apply Finset.sum_le_sum
      intro h _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [inverse_phase_dft] using reciprocal_coefficient_bound n h
    _ = _ := by rw [← Finset.mul_sum]

end NField.Alignment.CommonResetCompletion
