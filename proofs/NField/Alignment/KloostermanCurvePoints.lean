/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanCurve
import NField.Alignment.ArtinSchreierTrace

/-!
# Actual Kloosterman curve points and trace-zero fibers

Completing the square is a bijection of the ambient finite set, not an
assumed equality of point counts. The Artin-Schreier fibers are then
counted using the actual field trace.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanCurvePoints

open scoped BigOperators
open KloostermanCurve ArtinSchreierTrace

/-- Completing the square, with its nonzero factors explicit. -/
theorem quadratic_eq_zero_iff_square {K : Type*} [Field K]
    (a b v t : K) (ha : a ≠ 0) (h2 : (2:K) ≠ 0) :
    a*t^2-v*t+b = 0 ↔ (2*a*t-v)^2 = v^2-4*a*b := by
  have h4 : (4:K)*a ≠ 0 := by
    have he : (4:K)*a = 2*2*a := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero h2 h2) ha
  constructor
  · intro h
    linear_combination 4*a*h
  · intro h
    have hprod : (4*a)*(a*t^2-v*t+b) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left h4

/-- The coordinate change y=2at-v is bijective. -/
noncomputable def squareCoordinateEquiv {K : Type*} [Field K]
    (a v : K) (ha : a ≠ 0) (h2 : (2:K) ≠ 0) : K ≃ K where
  toFun t := 2*a*t-v
  invFun y := (y+v)/(2*a)
  left_inv t := by field_simp [ha, h2]; ring
  right_inv y := by field_simp [ha, h2]; ring

def quadraticPointCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) (a b : K) : ℕ :=
  (Finset.univ.filter fun xt : K × K =>
    a*xt.2^2-(xt.1^p-xt.1)*xt.2+b = 0).card

/-- Equality of the actual affine point counts by the coordinate bijection. -/
theorem curve_pointCount_eq_quadratic {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) (a b : K) (ha : a ≠ 0) (h2 : (2:K) ≠ 0) :
    StepanovPointCount.pointCount (curvePolynomial p a b) = quadraticPointCount p a b := by
  simp only [StepanovPointCount.pointCount, quadraticPointCount, Finset.card_filter,
    curvePolynomial_eval]
  symm
  apply Fintype.sum_equiv (Equiv.prodCongrRight fun x : K =>
    squareCoordinateEquiv a (x^p-x) ha h2)
  rintro ⟨x,t⟩
  change (if a*t^2-(x^p-x)*t+b=0 then (1:ℕ) else 0) =
    if (2*a*t-(x^p-x))^2=(x^p-x)^2-4*a*b then 1 else 0
  simp only [quadratic_eq_zero_iff_square a b (x^p-x) t ha h2]
  rfl

/-- The quadratic equation excludes t=0 and is the inverse-phase equation. -/
theorem quadratic_eq_zero_iff_inverse {K : Type*} [Field K]
    (a b v t : K) (hb : b ≠ 0) :
    a*t^2-v*t+b = 0 ↔ t ≠ 0 ∧ v = a*t+b/t := by
  constructor
  · intro h
    have ht : t ≠ 0 := by intro hz; subst t; exact hb (by simpa using h)
    refine ⟨ht, ?_⟩
    apply (sub_eq_iff_eq_add').mp
    apply (eq_div_iff ht).mpr
    linear_combination -h
  · rintro ⟨ht,h⟩
    field_simp [ht] at h
    linear_combination -h

/-- The zero-trace inverse phases, excluding t=0. -/
noncomputable def traceZeroCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) : ℕ :=
  (Finset.univ.filter fun t : K => t ≠ 0 ∧
    Algebra.trace (ZMod p) K (a*t+b/t) = 0).card

/-- The quadratic count is p times the actual trace-zero count. -/
theorem quadratic_pointCount_eq_trace {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hb : b ≠ 0) :
    quadraticPointCount p a b = p*traceZeroCount p a b := by
  classical
  simp only [quadraticPointCount, Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [traceZeroCount, Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [quadratic_eq_zero_iff_inverse a b _ t hb]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ne_eq, not_false_eq_true, true_and]
    rw [← Finset.card_filter, artinSchreier_fiber_card p]
    split_ifs <;> simp

/-- The actual curve count equals p times the zero-trace inverse-phase count. -/
theorem curve_pointCount_eq_trace {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    StepanovPointCount.pointCount (curvePolynomial p a b) = p*traceZeroCount p a b := by
  rw [curve_pointCount_eq_quadratic p a b (left_ne_zero_of_mul hab) h2,
    quadratic_pointCount_eq_trace p a b (right_ne_zero_of_mul hab)]

end NField.Alignment.KloostermanCurvePoints
