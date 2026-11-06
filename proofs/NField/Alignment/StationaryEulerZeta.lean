/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationarySawtoothMellin
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # The Euler summation representation of the actual Riemann zeta function -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryEulerZeta
open scoped BigOperators
open Filter MeasureTheory Set StationaryDiagonalDefinitions StationarySawtoothMellin
  StationaryMellinKernel

def eulerZeta (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2 - s * continuedSawtoothMellin s

theorem zeta_floor_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ x in Ioi (1 : ℝ), (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℂ)‖) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    simpa using (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  have hh := LSeries_eq_mul_integral' (1 : ℕ → ℂ) (by norm_num : (0 : ℝ) ≤ 1) hs hO
  rw [LSeries_one_eq_riemannZeta hs] at hh
  simpa only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_one] using hh

theorem shifted_cpow_identity (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  calc
    _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
    _ = (x : ℂ) ^ ((1 : ℂ) + -(s + 1)) := (Complex.cpow_add _ _ hxC).symm
    _ = _ := by congr 1; ring

theorem floor_kernel_split (s : ℂ) {x : ℝ} (hx : 1 < x) :
    (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      (x : ℂ) ^ (-s) - (1 / 2 : ℂ) * (x : ℂ) ^ (-(s + 1)) - sawtoothKernel s x := by
  have hx0 : 0 < x := by linarith
  have hf : (⌊x⌋₊ : ℝ) = x - 1 / 2 - psi x := by
    rw [natCast_floor_eq_intCast_floor hx0.le]
    unfold psi Int.fract
    ring
  have hfC := congrArg (fun y : ℝ => (y : ℂ)) hf
  push_cast at hfC
  rw [hfC, ← shifted_cpow_identity s hx0]
  unfold sawtoothKernel
  ring

theorem floor_integral_split {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      1 / (s - 1) - (1 / 2 : ℂ) * (1 / s) - sawtoothMellin s := by
  have h1 : (-s).re < -1 := by simp; linarith
  have h2 : (-(s + 1)).re < -1 := by simp; linarith
  have hi1 := integrableOn_Ioi_cpow_of_lt h1 (by norm_num : (0 : ℝ) < 1)
  have hi2 := integrableOn_Ioi_cpow_of_lt h2 (by norm_num : (0 : ℝ) < 1)
  have hi3 := sawtoothKernel_integrable (s := s) (by linarith)
  have hi12 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s) -
      (1 / 2 : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := hi1.sub (hi2.const_mul _)
  have he : (∫ x in Ioi (1 : ℝ), (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      ∫ x in Ioi (1 : ℝ), ((x : ℂ) ^ (-s) - (1 / 2 : ℂ) * (x : ℂ) ^ (-(s + 1)) - sawtoothKernel s x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact floor_kernel_split s hx
  rw [he, integral_sub hi12 hi3,
    integral_sub hi1 (hi2.const_mul (1 / 2 : ℂ)), integral_const_mul,
    integral_Ioi_cpow_of_lt h1 (by norm_num), integral_Ioi_cpow_of_lt h2 (by norm_num)]
  simp only [Complex.ofReal_one, Complex.one_cpow, sawtoothMellin]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := by intro h; have h' := congrArg Complex.re h; simp at h'; linarith
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hs1))
  have hs1'' : -1 + s ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hs1
  ring_nf
  field_simp [hs0, hs1, hs1', hs1'']
  ring

/-- Title: `The Bernoulli Euler formula agrees with the actual zeta function on its convergence half-plane`. -/
theorem eulerZeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : eulerZeta s = riemannZeta s := by
  rw [zeta_floor_integral hs, floor_integral_split hs,
    sawtoothMellin_eq_continued (by linarith : 0 < s.re)]
  unfold eulerZeta
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := by intro h; have h' := congrArg Complex.re h; simp at h'; linarith
  field_simp
  ring

theorem continuedSawtoothMellin_differentiableAt {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ continuedSawtoothMellin s := by
  exact (differentiableAt_const (-1 / 12 : ℂ)).add ((differentiableAt_id.add_const 1).mul
    (bernoulliMellin_hasDerivAt hs).differentiableAt)

theorem eulerZeta_differentiableAt {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ eulerZeta s := by
  apply (((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)).add_const (1 / 2)).sub
    (differentiableAt_id.mul (continuedSawtoothMellin_differentiableAt hs))

end NField.Alignment.StationaryEulerZeta
