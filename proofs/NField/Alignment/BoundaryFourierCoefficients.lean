/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BoundaryDistributionalDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.AddCircle

/-! # Actual continuous Fourier coefficients from the complete boundary jump ledger -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BoundaryFourierCoefficients
open scoped BigOperators Topology
open MeasureTheory Complex RealBernoulliBoundaryLimits RealBernoulliJumpData RealBoundaryUniformCells
  BoundaryJumpFlux BoundaryDistributionalDerivative

def frequency (n : ℤ) : ℂ := 2*(Real.pi : ℂ)*I*(n : ℂ)
def negativePhase (n : ℤ) (x : ℝ) : ℂ := exp (-frequency n*(x : ℂ))
def boundaryFourierCoefficient (N : ℕ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1,(realBoundary N x : ℂ)^2*negativePhase n x

theorem frequency_ne_zero {n : ℤ} (hn : n≠0) : frequency n≠0 := by
  unfold frequency
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
    (by exact_mod_cast hn)

theorem negative_phase_continuous (n : ℤ) : Continuous (negativePhase n) := by
  unfold negativePhase
  fun_prop

theorem negative_phase_deriv (n : ℤ) (x : ℝ) :
    HasDerivAt (negativePhase n) (-frequency n*negativePhase n x) x := by
  have h := ((hasDerivAt_id x).ofReal_comp.const_mul (-frequency n)).cexp
  apply h.congr_deriv
  simp only [negativePhase,id_eq,Complex.ofReal_one,mul_one]
  ring

theorem negative_phase_second_deriv (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y => -frequency n*negativePhase n y)
      (frequency n^2*negativePhase n x) x := by
  apply ((negative_phase_deriv n x).const_mul (-frequency n)).congr_deriv
  ring

theorem exp_negative_frequency (n : ℤ) : exp (-frequency n)=1 := by
  have he : -frequency n=((-n : ℤ) : ℂ)*(2*(Real.pi : ℂ)*I) := by
    unfold frequency
    push_cast
    ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

theorem negative_phase_period_endpoint (n : ℤ) : negativePhase n 1=negativePhase n 0 := by
  simp [negativePhase,exp_negative_frequency]

theorem negative_phase_integral {n : ℤ} (hn : n≠0) :
    (∫ x in (0 : ℝ)..1,negativePhase n x)=0 := by
  unfold negativePhase
  rw [integral_exp_mul_complex (neg_ne_zero.mpr (frequency_ne_zero hn))]
  simp [exp_negative_frequency]

/-- The coefficient is the pinned Mathlib continuous Fourier coefficient on the unit interval. -/
theorem boundary_fourier_eq_mathlib (N : ℕ) (n : ℤ) :
    boundaryFourierCoefficient N n=
      fourierCoeffOn (by norm_num : (0 : ℝ)<1) (fun x => (realBoundary N x : ℂ)^2) n := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero,div_one,one_smul]
  unfold boundaryFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [fourier_coe_apply]
  simp only [Int.cast_neg,smul_eq_mul]
  have he : 2*(Real.pi : ℂ)*I*(-(n : ℂ))*(x : ℂ)= -frequency n*(x : ℂ) := by
    unfold frequency
    ring
  rw [he]
  simp only [negativePhase,sub_zero,Complex.ofReal_one,div_one,mul_comm]

/-- Title: `Continuous Fourier coefficients from the value and derivative jumps`. -/
theorem boundary_fourier_jump_formula (N : ℕ) {n : ℤ} (hn : n≠0) :
    boundaryFourierCoefficient N n=
      (1/frequency n)*(∑ j ∈ Finset.range N.factorial,
        (valueJump N (grid N.factorial j) : ℂ)*negativePhase n (grid N.factorial j))+
      (1/frequency n^2)*(∑ j ∈ Finset.range N.factorial,
        (slopeJump N (grid N.factorial j) : ℂ)*negativePhase n (grid N.factorial j)) := by
  have hp := negative_phase_period_endpoint n
  have hw := boundary_distributional_second_derivative N (negativePhase n)
    (fun x => -frequency n*negativePhase n x) (fun x => frequency n^2*negativePhase n x)
    (negative_phase_deriv n) (negative_phase_second_deriv n)
    (continuous_const.mul (negative_phase_continuous n)) hp (by rw [hp])
  rw [negative_phase_integral hn,mul_zero,zero_add] at hw
  have hint : (∫ x in (0 : ℝ)..1,(realBoundary N x : ℂ)^2*(frequency n^2*negativePhase n x))=
      frequency n^2*boundaryFourierCoefficient N n := by
    unfold boundaryFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    ring
  rw [hint] at hw
  have hsum : (∑ j ∈ Finset.range N.factorial,
      ((slopeJump N (grid N.factorial j) : ℂ)*negativePhase n (grid N.factorial j)-
       (valueJump N (grid N.factorial j) : ℂ)*(-frequency n*negativePhase n (grid N.factorial j))))=
      frequency n*(∑ j ∈ Finset.range N.factorial,
        (valueJump N (grid N.factorial j) : ℂ)*negativePhase n (grid N.factorial j))+
      (∑ j ∈ Finset.range N.factorial,
        (slopeJump N (grid N.factorial j) : ℂ)*negativePhase n (grid N.factorial j)) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum] at hw
  apply mul_left_cancel₀ (pow_ne_zero 2 (frequency_ne_zero hn))
  rw [hw]
  field_simp [frequency_ne_zero hn]

end NField.Alignment.BoundaryFourierCoefficients
