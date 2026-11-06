/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionRationalFourierKernel
open scoped BigOperators

def expPolynomial (z : ℂ) : ℂ := ∑ m ∈ Finset.range 24, z^m/(m.factorial : ℂ)
def taylorError : ℝ := 25/((24 : ℝ)*(Nat.factorial 24 : ℝ))
def squareError (e : ℝ) : ℝ := (2+e)*e

theorem taylorError_nonneg : 0 ≤ taylorError := by unfold taylorError; positivity

theorem expPolynomial_error {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z-expPolynomial z‖ ≤ taylorError := by
  have he := Complex.exp_bound hz (by norm_num : 0 < (24 : ℕ))
  have hp : ‖z‖^24 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  apply he.trans
  unfold taylorError
  have hn : 0 ≤ (25 : ℝ)*((Nat.factorial 24 : ℝ)*24)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_right hp hn
  norm_num only [Nat.succ_eq_add_one, Nat.reduceAdd] at ⊢
  convert h using 1 <;> ring

theorem square_error {x y : ℂ} {e : ℝ}
    (hx : ‖x‖=1) (he : 0 ≤ e) (hxy : ‖x-y‖ ≤ e) :
    ‖x^2-y^2‖ ≤ squareError e := by
  have hy : ‖y‖ ≤ 1+e := by
    have h := norm_sub_le x (x-y)
    have hEq : x-(x-y)=y := by ring
    rw [hEq, hx] at h
    linarith
  have ha : ‖x+y‖ ≤ 2+e := (norm_add_le x y).trans (by linarith)
  rw [show x^2-y^2=(x-y)*(x+y) by ring, norm_mul]
  calc
    _ ≤ e*(2+e) := mul_le_mul hxy ha (norm_nonneg _) he
    _ = squareError e := by unfold squareError; ring

def anglePolynomial (x : ℝ) : ℂ := (expPolynomial (((x/4 : ℝ) : ℂ)*Complex.I))^4

theorem anglePolynomial_error {x : ℝ} (hx : |x| ≤ 4) :
    ‖Complex.exp ((x : ℂ)*Complex.I)-anglePolynomial x‖ ≤ squareError (squareError taylorError) := by
  let z : ℂ := ((x/4 : ℝ) : ℂ)*Complex.I
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, show |(4 : ℝ)|=4 by norm_num]
    linarith
  have hu : ‖Complex.exp z‖=1 := Complex.norm_exp_ofReal_mul_I (x/4)
  have h1 := square_error hu taylorError_nonneg (expPolynomial_error hz)
  have h2 := square_error (by rw [norm_pow,hu]; norm_num : ‖(Complex.exp z)^2‖=1)
    (by unfold squareError; positivity [taylorError_nonneg]) h1
  have hexp : Complex.exp ((x : ℂ)*Complex.I)=(Complex.exp z)^4 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [z]
    push_cast
    ring
  rw [hexp]
  simpa only [← pow_mul, show (2 : ℕ)*2=4 by norm_num, anglePolynomial] using h2

def piMidpoint : ℝ := 3141592653589793238465/10^21
def piRadius : ℝ := 1/(2*10^20)
def trigRadius : ℝ := piRadius+squareError (squareError taylorError)

theorem piMidpoint_error : |Real.pi-piMidpoint| ≤ piRadius := by
  have hl := Real.pi_gt_d20
  have hu := Real.pi_lt_d20
  rw [abs_le]
  norm_num [piMidpoint,piRadius] at ⊢
  constructor <;> linarith

theorem piMidpoint_bounds : 0 ≤ piMidpoint ∧ piMidpoint ≤ 4 := by
  norm_num [piMidpoint]

theorem ratio_phase_error {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.pi*r-piMidpoint*r| ≤ piRadius := by
  rw [← sub_mul,abs_mul,abs_of_nonneg hr0]
  have hp : 0 ≤ piRadius := by unfold piRadius; positivity
  have hb := mul_le_mul_of_nonneg_left hr1 hp
  exact (mul_le_mul_of_nonneg_right piMidpoint_error hr0).trans (by simpa using hb)

theorem cos_ratio_enclosure {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.cos (Real.pi*r)-(anglePolynomial (piMidpoint*r)).re| ≤ trigRadius := by
  have hx : |piMidpoint*r| ≤ 4 := by
    rw [abs_of_nonneg (mul_nonneg piMidpoint_bounds.1 hr0)]
    exact (mul_le_mul_of_nonneg_left hr1 piMidpoint_bounds.1).trans
      (by simpa using piMidpoint_bounds.2)
  have h := (Complex.abs_re_le_norm _).trans (anglePolynomial_error hx)
  simp only [Complex.sub_re,Complex.exp_ofReal_mul_I_re] at h
  have hphase := (Real.abs_cos_sub_cos_le (Real.pi*r) (piMidpoint*r)).trans
    (ratio_phase_error hr0 hr1)
  have ha := abs_sub_le (Real.cos (Real.pi*r)) (Real.cos (piMidpoint*r))
    (anglePolynomial (piMidpoint*r)).re
  unfold trigRadius
  linarith

theorem sin_ratio_enclosure {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.sin (Real.pi*r)-(anglePolynomial (piMidpoint*r)).im| ≤ trigRadius := by
  have hx : |piMidpoint*r| ≤ 4 := by
    rw [abs_of_nonneg (mul_nonneg piMidpoint_bounds.1 hr0)]
    exact (mul_le_mul_of_nonneg_left hr1 piMidpoint_bounds.1).trans
      (by simpa using piMidpoint_bounds.2)
  have h := (Complex.abs_im_le_norm _).trans (anglePolynomial_error hx)
  simp only [Complex.sub_im,Complex.exp_ofReal_mul_I_im] at h
  have hphase := (Real.abs_sin_sub_sin_le (Real.pi*r) (piMidpoint*r)).trans
    (ratio_phase_error hr0 hr1)
  have ha := abs_sub_le (Real.sin (Real.pi*r)) (Real.sin (piMidpoint*r))
    (anglePolynomial (piMidpoint*r)).im
  unfold trigRadius
  linarith
end NField.Alignment.CollisionRationalFourierKernel
