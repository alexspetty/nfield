/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
# Fourier decay with a possible derivative jump at the endpoints

The angular inverse has matching function values at zero and one, but the
first derivative need not match. Mathlib's interval integration by parts
retains that jump explicitly through two differentiations.
-/

noncomputable section

namespace NField.Alignment.IntervalFourierDecay

open scoped Real Interval
open Set MeasureTheory Complex

def coefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n

theorem coefficient_norm_le (f : ℝ → ℂ) {B : ℝ}
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ B) (n : ℤ) :
    ‖coefficient f n‖ ≤ B := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  unfold coefficient
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun x => fourier (-n) (x : AddCircle (1 : ℝ)) • f x) (by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        have hx'' : x ∈ Ioc (0 : ℝ) 1 := by
          simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        exact ⟨le_of_lt hx''.1, hx''.2⟩
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      exact hbound x hx')
  simpa using h

/-- Title: `Two integrations by parts retain the derivative endpoint jump`.

 The derivative jump is retained; no periodic derivative is assumed. -/
theorem twice_differentiated_coefficient (f g h : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hgh : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (h x) x)
    (hh : IntervalIntegrable h volume 0 1) (hend : f 1 = f 0)
    {n : ℤ} (hn : n ≠ 0) :
    coefficient f n = (1 / (-2 * Real.pi * Complex.I * (n : ℂ))) ^ 2 *
      (coefficient h n - (g 1 - g 0)) := by
  have hu : [[(0 : ℝ), 1]] = Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hf' := fourierCoeffOn_of_hasDerivAt_Ioo
    (by norm_num : (0 : ℝ) < 1) hn (by simpa only [hu] using hf)
    (by simpa using hfg) (hg.intervalIntegrable_of_Icc (by norm_num))
  have hg' := fourierCoeffOn_of_hasDerivAt_Ioo
    (by norm_num : (0 : ℝ) < 1) hn (by simpa only [hu] using hg) (by simpa using hgh) hh
  change coefficient f n = _ at hf'
  change coefficient g n = _ at hg'
  simp only [hend, sub_self, mul_zero, Complex.ofReal_zero, sub_zero, Complex.ofReal_one,
    one_mul, zero_sub] at hf'
  simp only [Complex.ofReal_zero, sub_zero, Complex.ofReal_one, one_mul,
    AddCircle.coe_zero, fourier_eval_zero] at hg'
  change coefficient f n = (1 / (-2 * Real.pi * Complex.I * (n : ℂ))) *
    -(coefficient g n) at hf'
  change coefficient g n = (1 / (-2 * Real.pi * Complex.I * (n : ℂ))) *
    (g 1 - g 0 - coefficient h n) at hg'
  rw [hf', hg']
  ring

theorem reciprocal_fourier_factor_norm (n : ℕ) :
    ‖(1 / (-2 * Real.pi * Complex.I * (n : ℂ)) : ℂ)‖ =
      1 / (2 * Real.pi * (n : ℝ)) := by
  norm_num [norm_div, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem coefficient_quadratic_decay (f g h : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hgh : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (h x) x)
    (hh : IntervalIntegrable h volume 0 1) (hend : f 1 = f 0)
    {B : ℝ} (hbound : ∀ x ∈ Icc (0 : ℝ) 1, ‖h x‖ ≤ B)
    {n : ℕ} (hn : 0 < n) :
    ‖coefficient f (n : ℤ)‖ ≤
      ((B + ‖g 1 - g 0‖) / (2 * Real.pi) ^ 2) / (n : ℝ) ^ 2 := by
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [twice_differentiated_coefficient f g h hf hg hfg hgh hh hend hnZ,
    norm_mul, norm_pow]
  simp only [Int.cast_natCast]
  rw [reciprocal_fourier_factor_norm]
  have hb : ‖coefficient h (n : ℤ) - (g 1 - g 0)‖ ≤ B + ‖g 1 - g 0‖ :=
    (norm_sub_le _ _).trans (add_le_add (coefficient_norm_le h hbound _) le_rfl)
  calc
    (1 / (2 * Real.pi * (n : ℝ))) ^ 2 *
        ‖coefficient h (n : ℤ) - (g 1 - g 0)‖ ≤
        (1 / (2 * Real.pi * (n : ℝ))) ^ 2 * (B + ‖g 1 - g 0‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

/-- Title: `Two interval derivatives give quadratic Fourier coefficient decay`.

 Two derivatives on the closed interval suffice, even when the first derivatives differ
at the endpoints. This is the regularity used after removing the angular singularity. -/
theorem cont_diff_two_coefficient_decay (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hend : f 1 = f 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ‖coefficient f (n : ℤ)‖ ≤ C / (n : ℝ) ^ 2 := by
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  let g := derivWithin f (Icc (0 : ℝ) 1)
  let h := derivWithin g (Icc (0 : ℝ) 1)
  have hg : ContDiffOn ℝ 1 g (Icc 0 1) := hf.derivWithin hu (by norm_num)
  have hh : ContinuousOn h (Icc 0 1) := hg.continuousOn_derivWithin hu (by norm_num)
  have hfg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g x) x := by
    intro x hx
    exact ((hf.differentiableOn (by norm_num)) x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
  have hgh : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (h x) x := by
    intro x hx
    exact ((hg.differentiableOn (by norm_num)) x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hh.norm
  refine ⟨(‖h x‖ + ‖g 1 - g 0‖) / (2 * Real.pi) ^ 2, by positivity, ?_⟩
  intro n hn
  exact coefficient_quadratic_decay f g h hf.continuousOn hg.continuousOn hfg hgh
    (hh.intervalIntegrable_of_Icc (by norm_num)) hend (fun y hy => hmax hy) hn

end NField.Alignment.IntervalFourierDecay
