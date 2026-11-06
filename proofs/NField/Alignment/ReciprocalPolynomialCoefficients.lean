/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealReciprocalTaylor

/-! # Literal coefficients of the finite real reciprocal expansion -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalPolynomialCoefficients
open scoped BigOperators
open RealPolynomialMomentBox RealReciprocalTaylor

def coefficient (Q x : ℝ) {n : ℕ} (j : Fin n) : ℝ :=
  Q/x * (-1/x)^(j.val+1)

theorem coefficient_ne_zero (Q x : ℝ) (hQ : Q ≠ 0) (hx : x ≠ 0)
    {n : ℕ} (j : Fin n) : coefficient Q x j ≠ 0 := by
  unfold coefficient
  exact mul_ne_zero (div_ne_zero hQ hx) (pow_ne_zero _ (div_ne_zero (by norm_num) hx))

theorem coefficient_abs (Q x : ℝ) (hQ : 0 ≤ Q) (hx : 0 < x)
    {n : ℕ} (j : Fin n) : |coefficient Q x j| = Q/x^(j.val+2) := by
  unfold coefficient
  rw [abs_mul, abs_pow, abs_div, abs_div]
  simp only [abs_of_nonneg hQ, abs_of_pos hx, abs_neg, abs_one, one_div]
  rw [inv_pow, ← div_eq_mul_inv, div_div, ← pow_succ']

theorem reciprocal_taylor_polynomial (Q x z : ℝ) (n : ℕ) :
    reciprocalTaylor Q x z n = Q/x+∑ j : Fin n, coefficient Q x j*z^(j.val+1) := by
  unfold reciprocalTaylor
  rw [Finset.sum_range_succ', mul_add]
  simp only [pow_zero, mul_one]
  simp only [coefficient]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Q/x*(-1/x)^(j+1)*z^(j+1))]
  rw [Finset.mul_sum]
  have he : (∑ j ∈ Finset.range n, Q/x*(-z/x)^(j+1)) =
      ∑ j ∈ Finset.range n, Q/x*(-1/x)^(j+1)*z^(j+1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show -z/x = (-1/x)*z by ring, mul_pow]
    ring
  simpa only [coefficient, Fin.val_mk, add_comm] using congrArg (fun t => t+Q/x) he

theorem taylor_bilinear_character_sum (Q x : ℝ) (H n : ℕ) :
    (∑ a : {a // a ∈ Finset.Icc 1 (H:ℤ)},
      ∑ b : {b // b ∈ Finset.Icc 1 (H:ℤ)},
        realCharacter (reciprocalTaylor Q x ((a.val*b.val:ℤ):ℝ) n)) =
      realCharacter (Q/x)*polynomialBilinear (coefficient Q x (n:=n)) H := by
  simp only [reciprocal_taylor_polynomial, AddChar.map_add_eq_mul,
    polynomialBilinear, Finset.mul_sum]

theorem taylor_bilinear_norm (Q x : ℝ) (H n : ℕ) :
    ‖∑ a : {a // a ∈ Finset.Icc 1 (H:ℤ)},
      ∑ b : {b // b ∈ Finset.Icc 1 (H:ℤ)},
        realCharacter (reciprocalTaylor Q x ((a.val*b.val:ℤ):ℝ) n)‖ =
      ‖polynomialBilinear (coefficient Q x (n:=n)) H‖ := by
  rw [taylor_bilinear_character_sum,norm_mul,realCharacter_norm,one_mul]

end NField.Alignment.ReciprocalPolynomialCoefficients
