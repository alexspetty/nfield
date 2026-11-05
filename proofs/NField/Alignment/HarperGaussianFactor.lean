/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperCharacteristicTaylor

/-!
# A quantitative comparison for the leading Gaussian factor

At |u|<=sqrt(q), q>=1 and |c|<=1, the Gaussian characteristic factor
exp(i*u*c/q-u^2/(4q)) differs from its linear exponential polynomial by
O((|u|+|u|^3)q^(-3/2)). Its norm is at most one. These deterministic
estimates do not assert a distributional Gaussian approximation.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianFactor
open scoped BigOperators Topology
open HarperCharacteristicTaylor

def gaussianExponent (q c u : ℝ) : ℂ := (u*c/q : ℝ)*Complex.I-(u^2/(4*q) : ℝ)
def gaussianFactor (q c u : ℝ) : ℂ := Complex.exp (gaussianExponent q c u)

theorem sqrt_mul_neg_half {q : ℝ} (hq : 0 < q) : Real.sqrt q*q^(-(1/2 : ℝ)) = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq]
  norm_num

theorem sqrt_div_sq {q : ℝ} (hq : 0 < q) : Real.sqrt q/q^2 = q^(-(3/2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast q 2, ← Real.rpow_sub hq]
  norm_num

theorem square_le_abs_add_cube (u : ℝ) : u^2 ≤ |u|+|u|^3 := by
  have h := mul_nonneg (abs_nonneg u) (sq_nonneg (|u|-1/2))
  nlinarith [sq_abs u, abs_nonneg u]

theorem parameter_square_bound {q u : ℝ} (hq : 0 ≤ q) (hu : |u| ≤ Real.sqrt q) :
    u^2 ≤ q := by
  have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
  simpa only [sq_abs, Real.sq_sqrt hq] using h

theorem parameter_fourth_remainder {q u : ℝ} (hq : 0 < q) (hu : |u| ≤ Real.sqrt q) :
    (u^2+u^4)/q^2 ≤ (|u|+|u|^3)*q^(-(3/2 : ℝ)) := by
  have h : |u|/q^2 ≤ q^(-(3/2 : ℝ)) := by
    rw [← sqrt_div_sq hq]
    exact div_le_div_of_nonneg_right hu (sq_nonneg q)
  have h2 : u^2/q^2 ≤ |u| *q^(-(3/2 : ℝ)) := by
    calc
      _ = |u| *(|u|/q^2) := by rw [← sq_abs u]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg u)
  have h4 : u^4/q^2 ≤ |u|^3*q^(-(3/2 : ℝ)) := by
    have he : |u|^4 = u^4 := by
      calc
        _ = (|u|^2)^2 := by ring
        _ = (u^2)^2 := by rw [sq_abs]
        _ = _ := by ring
    calc
      _ = |u|^3*(|u|/q^2) := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  rw [add_div, add_mul]
  exact add_le_add h2 h4

theorem gaussianExponent_re (q c u : ℝ) : (gaussianExponent q c u).re = -u^2/(4*q) := by
  simp only [gaussianExponent, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem gaussianExponent_norm_bound {q c u : ℝ} (hq : 1 ≤ q) (hc : |c| ≤ 1)
    (hu : |u| ≤ Real.sqrt q) : ‖gaussianExponent q c u‖ ≤ 2 := by
  have hq0 : 0 < q := by linarith
  have hs : Real.sqrt q ≤ q := by nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg q]
  have h1 : |u*c/q| ≤ 1 := by
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0, abs_mul]
    have h := mul_le_mul_of_nonneg_left hc (abs_nonneg u)
    nlinarith
  have h2 : |u^2/(4*q)| ≤ 1/4 := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg u) (by positivity)), div_le_iff₀ (by positivity : 0 < 4*q)]
    nlinarith [parameter_square_bound hq0.le hu]
  have h := norm_sub_le (((u*c/q : ℝ) : ℂ)*Complex.I) (((u^2/(4*q) : ℝ) : ℂ))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at h
  change ‖((u*c/q : ℝ) : ℂ)*Complex.I-((u^2/(4*q) : ℝ) : ℂ)‖ ≤ 2
  linarith

theorem gaussianExponent_square_bound {q c u : ℝ} (hc : |c| ≤ 1) :
    ‖gaussianExponent q c u‖^2 ≤ (u^2+u^4)/q^2 := by
  have hc2 : c^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg c) hc 2
  have he : ‖gaussianExponent q c u‖^2 = (u^2*c^2+u^4/16)/q^2 := by
    simp only [gaussianExponent, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (sq_nonneg q)
  have hm := mul_le_mul_of_nonneg_left hc2 (sq_nonneg u)
  nlinarith [pow_nonneg (sq_nonneg u) 2]

theorem gaussianFactor_norm_le_one {q : ℝ} (hq : 0 ≤ q) (c u : ℝ) :
    ‖gaussianFactor q c u‖ ≤ 1 := by
  rw [gaussianFactor, Complex.norm_exp, gaussianExponent_re]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) (by positivity)

theorem gaussianFactor_zero (q c : ℝ) : gaussianFactor q c 0 = 1 := by
  simp [gaussianFactor, gaussianExponent]

theorem gaussianFactor_linear_identity (q c u : ℝ) :
    1+gaussianExponent q c u = meanPhase u (c/q) (q⁻¹/2) := by
  unfold gaussianExponent meanPhase
  push_cast
  ring

theorem gaussianFactor_error {q c u : ℝ} (hq : 1 ≤ q) (hc : |c| ≤ 1)
    (hu : |u| ≤ Real.sqrt q) :
    ‖gaussianFactor q c u-meanPhase u (c/q) (q⁻¹/2)‖ ≤
      Real.exp 2*(|u|+|u|^3)*q^(-(3/2 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (gaussianExponent q c u) 2
  have he : (∑ m ∈ Finset.range 2, (gaussianExponent q c u)^m/(m.factorial : ℂ)) =
      meanPhase u (c/q) (q⁻¹/2) := by
    simpa [Finset.sum_range_succ] using gaussianFactor_linear_identity q c u
  rw [he] at h
  calc
    _ ≤ ‖gaussianExponent q c u‖^2*Real.exp ‖gaussianExponent q c u‖ := h
    _ ≤ ((u^2+u^4)/q^2)*Real.exp 2 := mul_le_mul
      (gaussianExponent_square_bound hc)
      (Real.exp_le_exp.mpr (gaussianExponent_norm_bound hq hc hu))
      (Real.exp_pos _).le (by positivity)
    _ ≤ ((|u|+|u|^3)*q^(-(3/2 : ℝ)))*Real.exp 2 :=
      mul_le_mul_of_nonneg_right (parameter_fourth_remainder hq0 hu) (Real.exp_pos _).le
    _ = _ := by ring

end NField.Alignment.HarperGaussianFactor
