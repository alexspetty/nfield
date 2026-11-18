/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib
/-! # Complete finite Fourier work under arbitrary multiplication

Mathlib's discrete Fourier equivalence supplies inversion. Multiplication
need not be a unit: its Fourier transform is the full pushforward over
all frequency fibres. No nonunit address or frequency is deleted.
-/

noncomputable section

namespace NField.ResetForests.ResetGrid

open scoped BigOperators

variable {k : ℕ} [NeZero k]

theorem standard_character_star (z : ZMod k) :
    (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  have hp : 0 < ringChar (ZMod k) := by
    rw [ZMod.ringChar_zmod_n]
    exact NeZero.pos k
  simpa only [AddChar.inv_apply] using
    (AddChar.starComp_apply hp (φ := ZMod.stdAddChar) z)

theorem dft_bilinear (f g : ZMod k → ℂ) :
    (∑ x : ZMod k, ZMod.dft f x*g x) =
      ∑ y : ZMod k, f y*ZMod.dft g y := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm y x]
  ring

theorem dft_star (f : ZMod k → ℂ) (x : ZMod k) :
    ZMod.dft (fun y => (starRingEnd ℂ) (f y)) x =
      (starRingEnd ℂ) (ZMod.dft f (-x)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul,
    standard_character_star, mul_neg, neg_neg]

theorem dft_twice_star (f : ZMod k → ℂ) (x : ZMod k) :
    ZMod.dft (fun y => (starRingEnd ℂ) (ZMod.dft f y)) x =
      (k : ℂ)*(starRingEnd ℂ) (f x) := by
  rw [dft_star, ZMod.dft_dft]
  simp only [neg_neg, smul_eq_mul, map_mul, map_natCast]

theorem complex_square_work (z : ℂ) :
    z*(starRingEnd ℂ) z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Parseval on the complete counting grid, with Mathlib's unnormalised DFT. -/
theorem dft_parseval (f : ZMod k → ℂ) :
    (∑ x : ZMod k, ‖ZMod.dft f x‖^2) =
      (k : ℝ)*(∑ x : ZMod k, ‖f x‖^2) := by
  have hp := dft_bilinear f (fun y => (starRingEnd ℂ) (ZMod.dft f y))
  simp_rw [dft_twice_star] at hp
  have hleft : (∑ x : ZMod k, ZMod.dft f x*(starRingEnd ℂ) (ZMod.dft f x)) =
      ((∑ x : ZMod k, ‖ZMod.dft f x‖^2 : ℝ) : ℂ) := by
    simp only [complex_square_work]
    push_cast
    rfl
  have hright : (∑ y : ZMod k, f y*((k : ℂ)*(starRingEnd ℂ) (f y))) =
      (((k : ℝ)*(∑ y : ZMod k, ‖f y‖^2)) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [show f y*((k : ℂ)*(starRingEnd ℂ) (f y)) =
      (k : ℂ)*(f y*(starRingEnd ℂ) (f y)) by ring,
      complex_square_work]
    push_cast
    rfl
  rw [hleft, hright] at hp
  exact_mod_cast hp

def multiplicationPushforward (h : ZMod k) (F : ZMod k → ℂ) (j : ZMod k) : ℂ :=
  ∑ u : ZMod k, if h*u = j then F u else 0

/-- Fourier multiplication law with every frequency fibre retained. -/
theorem dft_comp_mul (f : ZMod k → ℂ) (h : ZMod k) :
    ZMod.dft (fun x => f (h*x)) = multiplicationPushforward h (ZMod.dft f) := by
  classical
  apply ZMod.dft.injective
  ext x
  rw [ZMod.dft_dft]
  have hpush : ZMod.dft (multiplicationPushforward h (ZMod.dft f)) x =
      ZMod.dft (ZMod.dft f) (h*x) := by
    change (∑ j : ZMod k, ZMod.stdAddChar (-(j*x))*
        multiplicationPushforward h (ZMod.dft f) j) =
      ∑ u : ZMod k, ZMod.stdAddChar (-(u*(h*x)))*ZMod.dft f u
    simp only [multiplicationPushforward, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    congr 1
    congr 1
    ring
  rw [hpush, ZMod.dft_dft]
  simp only [mul_neg]

/-- Pushing frequencies forward cannot increase their complete absolute mass. -/
theorem pushforward_mass_le (h : ZMod k) (F : ZMod k → ℂ) :
    (∑ j : ZMod k, ‖multiplicationPushforward h F j‖) ≤
      ∑ u : ZMod k, ‖F u‖ := by
  classical
  calc
    _ ≤ ∑ j : ZMod k, ∑ u : ZMod k, if h*u = j then ‖F u‖ else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact (norm_sum_le _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro u _
        split_ifs <;> simp)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      simp

end NField.ResetForests.ResetGrid
