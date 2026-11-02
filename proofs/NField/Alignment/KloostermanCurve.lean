/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovPointCount
import Mathlib.FieldTheory.Separable

/-!
# The curve used in the finite-field Kloosterman argument

The polynomial is literally (X^p-X)^2-4ab. Its degree and nonsquareness
are proved, allowing the established Stepanov theorem to be applied.
The trace and L-polynomial connection is a separate remaining step.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanCurve

open Polynomial

noncomputable def curvePolynomial {K : Type*} [Field K] (p : ℕ) (a b : K) : K[X] :=
  (X^p-X)^2-C (4*a*b)

@[simp] theorem curvePolynomial_eval {K : Type*} [Field K]
    (p : ℕ) (a b x : K) :
    (curvePolynomial p a b).eval x = (x^p-x)^2-4*a*b := by
  simp [curvePolynomial]

theorem curvePolynomial_natDegree {K : Type*} [Field K]
    (p : ℕ) (hp : 1 < p) (a b : K) :
    (curvePolynomial p a b).natDegree = 2*p := by
  rw [curvePolynomial, natDegree_sub_C, natDegree_pow,
    FiniteField.X_pow_card_sub_X_natDegree_eq K hp]

theorem artinSchreier_derivative {K : Type*} [Field K]
    (p : ℕ) [CharP K p] : derivative (X^p-X : K[X]) = -1 := by
  simp [derivative_sub, derivative_X_pow]

/-- A direct Bezout identity proves separability of g^2-c when g'=-1. -/
theorem square_sub_constant_separable {K : Type*} [Field K]
    (g : K[X]) (hg : derivative g = -1) (c : K) (hc : c ≠ 0)
    (h2 : (2 : K) ≠ 0) : (g^2-C c).Separable := by
  rw [separable_def']
  refine ⟨C (-c⁻¹), C (-((2:K)⁻¹*c⁻¹))*g, ?_⟩
  simp only [derivative_sub, derivative_pow, derivative_C, sub_zero, hg,
    map_neg, map_mul]
  have hci : C c * C c⁻¹ = (1 : K[X]) := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have h2i : (2 : K[X])*C ((2:K)⁻¹) = 1 := by
    rw [← map_ofNat C 2, ← map_mul, mul_inv_cancel₀ h2, map_one]
  norm_num only [Nat.cast_ofNat, map_ofNat]
  linear_combination hci + (g^2*C c⁻¹)*h2i

/-- A separable polynomial of positive degree cannot be a square. -/
theorem not_isSquare_of_separable {K : Type*} [Field K]
    (f : K[X]) (hsep : f.Separable) (hdeg : 0 < f.natDegree) : ¬IsSquare f := by
  rintro ⟨g, rfl⟩
  have hu := hsep.squarefree g (dvd_refl (g*g))
  have hd := natDegree_eq_zero_of_isUnit (hu.mul hu)
  omega

/-- Nonzero a*b and odd characteristic exclude repeated roots. -/
theorem curvePolynomial_separable {K : Type*} [Field K]
    (p : ℕ) [CharP K p] (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    (curvePolynomial p a b).Separable := by
  apply square_sub_constant_separable _ (artinSchreier_derivative p)
  · have h4 : (4:K) ≠ 0 := by
      have := mul_ne_zero h2 h2
      norm_num only [show (2:K)*2=4 by ring] at this
      exact this
    simpa only [mul_assoc] using mul_ne_zero h4 hab
  · exact h2

/-- The required nonsquare condition holds over the algebraic closure. -/
theorem curvePolynomial_not_isSquare_map {K : Type*} [Field K]
    (p : ℕ) [CharP K p] (hp : 1 < p) (a b : K)
    (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    ¬IsSquare ((curvePolynomial p a b).map (algebraMap K (AlgebraicClosure K))) := by
  apply not_isSquare_of_separable _ (curvePolynomial_separable p a b hab h2).map
  rw [natDegree_map, curvePolynomial_natDegree p hp]
  omega

/-- Odd finite-field cardinality supplies the nonzero factor 2. -/
theorem two_ne_zero_of_odd_card {K : Type*} [Field K] [Fintype K]
    (hodd : Odd (Fintype.card K)) : (2:K) ≠ 0 := by
  intro hz
  letI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hz
  exact StepanovPointCount.char_ne_two_of_odd_card hodd (ringChar.eq K 2)

/-- Apply Stepanov to the actual Kloosterman curve, with its polynomial
conditions discharged. The trace/L-polynomial bridge is not assumed here. -/
theorem curve_point_count_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [CharP K p] (hp : 1 < p) (a b : K) (hab : a*b ≠ 0)
    (hodd : Odd (Fintype.card K)) (hq : 12*p ≤ Fintype.card K) :
    |(StepanovPointCount.pointCount (curvePolynomial p a b) : ℝ)-Fintype.card K| <
      8*p*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) := by
  have hm := curvePolynomial_natDegree p hp a b
  have h := StepanovPointCount.point_count_bound (curvePolynomial p a b)
    (by omega) (by omega) hodd
    (curvePolynomial_not_isSquare_map p hp a b hab (two_ne_zero_of_odd_card hodd))
  rw [hm] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  convert h using 1
  ring

end NField.Alignment.KloostermanCurve
