/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedDistribution

/-! # Literal Fourier coefficients of the weighted clock square -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedFourier

open scoped BigOperators
open MeasureTheory CommonResetGram CommonResetWeightedSampling
open CommonResetWeightedCells CommonResetWeightedDistribution

def angularFrequency (n : ℤ) : ℂ := 2*Real.pi*Complex.I*n

def fourierTest (n : ℤ) (x : ℝ) : ℂ := Complex.exp (-angularFrequency n*x)

def weightedFourierCoefficient (N : ℕ) (c : ℕ → ℝ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, (weightedProfile N c x^2 : ℂ)*fourierTest n x

theorem angularFrequency_ne_zero {n : ℤ} (hn : n ≠ 0) : angularFrequency n ≠ 0 := by
  unfold angularFrequency
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hn)

theorem fourierTest_derivative (n : ℤ) (x : ℝ) :
    HasDerivAt (fourierTest n) (-angularFrequency n*fourierTest n x) x := by
  convert! (((hasDerivAt_id x).ofReal_comp).const_mul (-angularFrequency n)).cexp using 1 <;>
    simp only [fourierTest, id_eq, Complex.ofReal_one] <;> ring

theorem fourierTest_continuous (n : ℤ) : Continuous (fourierTest n) :=
  continuous_iff_continuousAt.mpr (fun x => (fourierTest_derivative n x).continuousAt)

theorem fourierTest_period (n : ℤ) : fourierTest n 1=fourierTest n 0 := by
  unfold fourierTest angularFrequency
  have he : -(2*(Real.pi : ℂ)*Complex.I*n)*(1 : ℝ)=(-n : ℤ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem fourierTest_integral {n : ℤ} (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, fourierTest n x)=0 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => fourierTest_derivative n x)
    (((fourierTest_continuous n).const_mul (-angularFrequency n)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, fourierTest_period, sub_self] at he
  exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr (angularFrequency_ne_zero hn))

/-- Title: `Every nonzero actual Fourier coefficient is the printed sum of value and slope jumps`. -/
theorem weighted_fourier_jump_formula {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) {n : ℤ} (hn : n ≠ 0) :
    weightedFourierCoefficient N c n =
      (∑ k ∈ Finset.range D, (valueJump N D c k : ℂ)*fourierTest n ((k : ℝ)/D))/angularFrequency n+
      (∑ k ∈ Finset.range D, (slopeJump N D c k : ℂ)*fourierTest n ((k : ℝ)/D))/(angularFrequency n)^2 := by
  have hfreq := angularFrequency_ne_zero hn
  have hd (x : ℝ) : HasDerivAt (fun y => -angularFrequency n*fourierTest n y)
      ((angularFrequency n)^2*fourierTest n x) x := by
    convert! (fourierTest_derivative n x).const_mul (-angularFrequency n) using 1 <;> ring
  have he := weighted_circle_second_derivative hD hdiv c
    (fourierTest n) (fun x => -angularFrequency n*fourierTest n x)
    (fun x => (angularFrequency n)^2*fourierTest n x)
    (fourierTest_derivative n) hd ((fourierTest_continuous n).const_mul _)
    (fourierTest_period n) (by rw [fourierTest_period])
  rw [fourierTest_integral hn, mul_zero, zero_add] at he
  have hleft : (∫ x in (0 : ℝ)..1,
      (weightedProfile N c x^2 : ℂ)*((angularFrequency n)^2*fourierTest n x)) =
      (angularFrequency n)^2*weightedFourierCoefficient N c n := by
    rw [weightedFourierCoefficient, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hleft] at he
  have hright : (∑ k ∈ Finset.range D,
      ((slopeJump N D c k : ℂ)*fourierTest n ((k : ℝ)/D)-
        (valueJump N D c k : ℂ)*(-angularFrequency n*fourierTest n ((k : ℝ)/D)))) =
      (∑ k ∈ Finset.range D, (slopeJump N D c k : ℂ)*fourierTest n ((k : ℝ)/D))+
        angularFrequency n*∑ k ∈ Finset.range D, (valueJump N D c k : ℂ)*fourierTest n ((k : ℝ)/D) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hright] at he
  field_simp [hfreq]
  linear_combination he

/-- Title: `Every finite weighted profile has the literal circle Fourier identity with no auxiliary hypotheses`. -/
theorem weighted_fourier_formula (N : ℕ) (c : ℕ → ℝ) {n : ℤ} (hn : n ≠ 0) :
    weightedFourierCoefficient N c n =
      (∑ k ∈ Finset.range N.factorial,
        (valueJump N N.factorial c k : ℂ)*fourierTest n ((k : ℝ)/N.factorial))/angularFrequency n+
      (∑ k ∈ Finset.range N.factorial,
        (slopeJump N N.factorial c k : ℂ)*fourierTest n ((k : ℝ)/N.factorial))/(angularFrequency n)^2 :=
  weighted_fourier_jump_formula (Nat.factorial_pos N)
    (fun j hj => Nat.dvd_factorial (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2) c hn

end NField.Alignment.CommonResetWeightedFourier
