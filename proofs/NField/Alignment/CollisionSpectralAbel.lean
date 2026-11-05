/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLogTailKernel

/-!
# Abel summation for the actual spectral arithmetic weight

The partial sum is the literal floor-indexed sum of h. The differentiated
kernel times this step function has an explicit integrable majorant.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralAbel

open scoped BigOperators Classical
open Filter MeasureTheory
open CollisionJordanVariance CollisionSpectralArithmetic CollisionSpectralEuler CollisionSpectralMean
open CollisionLogTailKernel

def partialWeight (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, spectralWeight n
def kernelDerivative (x : ℝ) : ℝ := 2*Real.log x*(1-Real.log x)/x^3
def weightedTerm (n : ℕ) : ℝ := logPowerKernel 2 n*spectralWeight n
def weightedTail (Q : ℝ) : ℝ := ∑' n : ℕ, if Q<(n : ℝ) then weightedTerm n else 0

theorem spectralWeight_zero : spectralWeight 0=0 := by simp [spectralWeight]

theorem spectralWeight_nonneg (n : ℕ) : 0 ≤ spectralWeight n := by
  by_cases hn : n=0
  · simp [hn,spectralWeight_zero]
  · exact (spectralWeight_pos (Nat.pos_of_ne_zero hn)).le

theorem spectralWeight_bound (n : ℕ) : spectralWeight n ≤ 1 := by
  by_cases hn : n=0
  · simp [hn,spectralWeight_zero]
  · exact spectralWeight_le_one (Nat.pos_of_ne_zero hn)

theorem partialWeight_nonneg (x : ℝ) : 0 ≤ partialWeight x :=
  Finset.sum_nonneg (fun n _ => spectralWeight_nonneg n)

theorem partialWeight_monotone : Monotone partialWeight := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · exact fun n _ _ => spectralWeight_nonneg n

theorem partialWeight_le {x : ℝ} (hx : 0 ≤ x) : partialWeight x ≤ x := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => spectralWeight_bound n)
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

theorem partialWeight_Icc (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, spectralWeight n)=partialWeight x := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _),Finset.sum_cons,spectralWeight_zero,zero_add]
  rfl

theorem weightedTerm_nonneg (n : ℕ) : 0 ≤ weightedTerm n :=
  mul_nonneg (squareLogKernel_nonneg _) (spectralWeight_nonneg n)

theorem weightedTerm_summable : Summable weightedTerm := by
  apply Summable.of_nonneg_of_le weightedTerm_nonneg _ (logPowerKernel_nat_summable 2)
  intro n
  exact mul_le_of_le_one_right (squareLogKernel_nonneg _) (spectralWeight_bound n)

theorem kernelDerivative_nonpos {x : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x) :
    kernelDerivative x ≤ 0 := by
  unfold kernelDerivative
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  · exact (pow_pos hx 3).le

theorem kernelDerivative_abs_bound {x : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x) :
    |kernelDerivative x| *x ≤ 2*logPowerKernel 2 x := by
  have hx0 : x≠0 := hx.ne'
  have he : |kernelDerivative x| *x=2*Real.log x*(Real.log x-1)/x^2 := by
    rw [abs_of_nonpos (kernelDerivative_nonpos hx hl)]
    unfold kernelDerivative
    field_simp
    ring
  rw [he]
  have h := div_le_div_of_nonneg_right
    (show 2*Real.log x*(Real.log x-1) ≤ 2*(Real.log x)^2 by nlinarith)
    (sq_nonneg x)
  simpa only [logPowerKernel,mul_div_assoc] using h

theorem derivative_partial_norm_bound {x : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x) :
    ‖kernelDerivative x*partialWeight x‖ ≤ 2*logPowerKernel 2 x := by
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (partialWeight_nonneg x)]
  exact (mul_le_mul_of_nonneg_left (partialWeight_le hx.le) (abs_nonneg _)).trans
    (kernelDerivative_abs_bound hx hl)

theorem derivative_partial_integrableOn {Q : ℝ} (hQ : 0 < Q) (hlog : 1 ≤ Real.log Q) :
    IntegrableOn (fun x => kernelDerivative x*partialWeight x) (Set.Ioi Q) := by
  have hD : Measurable kernelDerivative := by unfold kernelDerivative; fun_prop
  have hA : Measurable partialWeight := partialWeight_monotone.measurable
  apply ((squareLogKernel_integrableOn hQ).const_mul 2).mono'
    (hD.mul hA).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact derivative_partial_norm_bound (hQ.trans hx)
    (hlog.trans (Real.log_le_log hQ hx.le))

theorem kernelDerivative_continuousOn {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    ContinuousOn kernelDerivative (Set.Icc Q R) := by
  intro x hx
  have hx0 : x≠0 := ne_of_gt (hQ.trans_le hx.1)
  have hl := Real.continuousAt_log hx0
  exact (((hl.const_mul 2).mul (continuousAt_const.sub hl)).div
    (continuousAt_id.pow 3) (pow_ne_zero 3 hx0)).continuousWithinAt

theorem squareLogKernel_derivative_integrable {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    IntegrableOn (deriv (logPowerKernel 2)) (Set.Icc Q R) := by
  have h : ContinuousOn (deriv (logPowerKernel 2)) (Set.Icc Q R) :=
    (kernelDerivative_continuousOn hQ R).congr (fun x hx =>
      (squareLogKernel_hasDerivAt (ne_of_gt (hQ.trans_le hx.1))).deriv)
  exact h.integrableOn_Icc

theorem finite_spectral_abel {Q R : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) :
    (∑ n ∈ Finset.Ioc ⌊Q⌋₊ ⌊R⌋₊, logPowerKernel 2 n*spectralWeight n)=
      logPowerKernel 2 R*partialWeight R-logPowerKernel 2 Q*partialWeight Q-
        ∫ x in Set.Ioc Q R, kernelDerivative x*partialWeight x := by
  have h := sum_mul_eq_sub_sub_integral_mul spectralWeight hQ.le hQR
    (fun x hx => (squareLogKernel_hasDerivAt (ne_of_gt (hQ.trans_le hx.1))).differentiableAt)
    (squareLogKernel_derivative_integrable hQ R)
  simp only [partialWeight_Icc] at h
  have he : (∫ x in Set.Ioc Q R, kernelDerivative x*partialWeight x)=
      ∫ x in Set.Ioc Q R, deriv (logPowerKernel 2) x*partialWeight x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(squareLogKernel_hasDerivAt (ne_of_gt (hQ.trans hx.1))).deriv]
    rfl
  rw [he]
  exact h

end NField.Alignment.CollisionSpectralAbel
