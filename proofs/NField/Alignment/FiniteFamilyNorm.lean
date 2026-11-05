/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteFamilyEnergy

/-! # Real normalized norms corresponding to the complex energy identities -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteFamilyNorm
open scoped BigOperators ComplexConjugate
open DoubleTransversality FiniteFamilyEnergy

def finiteNorm {α : Type*} [Fintype α] (f : α → ℂ) : ℝ :=
  Real.sqrt (finiteEnergy f).re

theorem finiteEnergy_eq_real {α : Type*} [Fintype α] (f : α → ℂ) :
    finiteEnergy f = (((Fintype.card α : ℝ)⁻¹ * ∑ a, ‖f a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [finiteEnergy, finiteInner, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_pow]

theorem finiteEnergy_re_nonneg {α : Type*} [Fintype α] (f : α → ℂ) :
    0 ≤ (finiteEnergy f).re := by
  rw [finiteEnergy_eq_real, Complex.ofReal_re]
  positivity

theorem finiteNorm_sq {α : Type*} [Fintype α] (f : α → ℂ) :
    finiteNorm f ^ 2 = (finiteEnergy f).re :=
  Real.sq_sqrt (finiteEnergy_re_nonneg f)

theorem finiteNorm_of_energy_eq {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (h : finiteEnergy f = finiteEnergy g) :
    finiteNorm f = finiteNorm g := congrArg (fun z : ℂ => Real.sqrt z.re) h

theorem weighted_norm_square {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℂ) (w : ι → ℂ)
    (hf : ∀ i j, i ≠ j → finiteInner (f i) (f j) = 0) :
    finiteNorm (fun x => ∑ i, w i * f i x) ^ 2 = ∑ i, ‖w i‖ ^ 2 * finiteNorm (f i) ^ 2 := by
  have h := congrArg Complex.re (weighted_energy_of_orthogonal f w hf)
  simp only [Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq] at h
  simpa only [finiteNorm_sq] using h

end NField.Alignment.FiniteFamilyNorm
