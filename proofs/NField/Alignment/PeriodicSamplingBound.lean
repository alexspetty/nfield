/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Sampling a periodic differentiable function at an arithmetic grid -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.PeriodicSamplingBound
open scoped BigOperators Topology
open Set MeasureTheory intervalIntegral

theorem single_cell_bound (g B : ℝ → ℝ) (hg : Continuous g)
    (hd : Differentiable ℝ g) (hB : Continuous B) (hB0 : ∀ t, 0 ≤ B t)
    (hderiv : ∀ t, ‖deriv g t‖ ≤ B t) (a δ : ℝ) (hδ : 0 < δ) :
    δ*g a ≤ (∫ t in a..a+δ, g t)+δ*(∫ t in a..a+δ, B t) := by
  have hp (t : ℝ) (ht : t ∈ Icc a (a+δ)) :
      g a ≤ g t+∫ u in a..a+δ, B u := by
    have hn := norm_sub_le_integral_of_norm_deriv_le_of_le ht.1
      hg.continuousOn hd.differentiableOn
      (Filter.Eventually.of_forall (fun u _ => hderiv u)) (hB.intervalIntegrable a t)
    have hi := integral_mono_interval (μ := volume) (a := a) (b := t) (c := a) (d := a+δ)
      le_rfl ht.1 ht.2 (Filter.Eventually.of_forall hB0) (hB.intervalIntegrable a (a+δ))
    have ha : g a-g t ≤ ‖g t-g a‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_abs_self _
    linarith
  have hi := integral_mono_on (show a ≤ a+δ by linarith)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => g a) volume a (a+δ))
    ((hg.add continuous_const).intervalIntegrable a (a+δ)) hp
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hg.intervalIntegrable a (a+δ))
      (intervalIntegrable_const (c := ∫ u in a..a+δ, B u)),
    intervalIntegral.integral_const] at hi
  simpa only [add_sub_cancel_left, smul_eq_mul] using hi

theorem grid_sampling_bound (g B : ℝ → ℝ) (hg : Continuous g)
    (hd : Differentiable ℝ g) (hB : Continuous B) (hB0 : ∀ t, 0 ≤ B t)
    (hderiv : ∀ t, ‖deriv g t‖ ≤ B t) (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    δ*(∑ j ∈ Finset.range N, g (a+(j:ℝ)*δ)) ≤
      (∫ t in a..a+(N:ℝ)*δ, g t)+δ*(∫ t in a..a+(N:ℝ)*δ, B t) := by
  have hi := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) =>
    single_cell_bound g B hg hd hB hB0 hderiv (a+(j:ℝ)*δ) δ hδ)
  have he (j : ℕ) : a+(j:ℝ)*δ+δ = a+((j+1:ℕ):ℝ)*δ := by push_cast; ring
  simp_rw [he] at hi
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_integral_adjacent_intervals (fun j _ => hg.intervalIntegrable _ _),
    sum_integral_adjacent_intervals (fun j _ => hB.intervalIntegrable _ _)] at hi
  simpa only [Nat.cast_zero, zero_mul, add_zero] using hi

theorem periodic_integral_le (g : ℝ → ℝ) (hg : Continuous g)
    (hgp : Function.Periodic g 1) (hg0 : ∀ t, 0 ≤ g t) (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, g t) ≤ (b-a+1)*(∫ t in 0..1, g t) := by
  let m : ℤ := ⌈b-a⌉
  have hm : b ≤ a+(m:ℝ) := by
    have h := Int.le_ceil (b-a)
    dsimp [m]
    linarith
  have hmhi : (m:ℝ) ≤ b-a+1 := by
    have h := Int.ceil_lt_add_one (b-a)
    dsimp [m]
    linarith
  have hi := integral_mono_interval (μ := volume) (a := a) (b := b) (c := a) (d := a+(m:ℝ))
    le_rfl hab hm (Filter.Eventually.of_forall hg0) (hg.intervalIntegrable _ _)
  have he := hgp.intervalIntegral_add_zsmul_eq m a (fun x y => hg.intervalIntegrable x y)
  simp only [zsmul_eq_mul, mul_one] at he
  have hp := hgp.intervalIntegral_add_eq a 0
  simp only [zero_add] at hp
  rw [he,hp] at hi
  exact hi.trans (mul_le_mul_of_nonneg_right hmhi
    (integral_nonneg (by norm_num) (fun t _ => hg0 t)))

end NField.Alignment.PeriodicSamplingBound
