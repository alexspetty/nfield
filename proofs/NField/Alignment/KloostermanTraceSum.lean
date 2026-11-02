/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanCurvePoints
import NField.Alignment.InverseAdditiveCompletion

/-!
# Kloosterman trace sums and the actual curve count

Finite additive-character orthogonality gives the sum over all prime-field
frequencies. The zero frequency is retained exactly. This does not yet
supply the individual square-root estimate or its L-polynomial proof.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanTraceSum

open scoped BigOperators
open KloostermanCurve KloostermanCurvePoints

/-- The actual extension-field Kloosterman sum, with trace to ZMod p. -/
noncomputable def traceKloostermanSum {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) (m : ZMod p) : ℂ :=
  ∑ t : K, if t = 0 then 0 else
    ZMod.stdAddChar (m*Algebra.trace (ZMod p) K (a*t+b/t))

/-- Exact prime-field additive orthogonality. -/
theorem prime_character_orthogonality (p : ℕ) [Fact p.Prime] (v : ZMod p) :
    (∑ m : ZMod p, ZMod.stdAddChar (m*v)) = if v=0 then (p:ℂ) else 0 := by
  by_cases hv : v=0
  · simp [hv]
  · rw [if_neg hv]
    simpa only [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hv)

/-- Summing over every frequency gives p times the trace-zero count. -/
theorem sum_traceKloosterman_eq_trace_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) :
    (∑ m : ZMod p, traceKloostermanSum p a b m) = p*traceZeroCount p a b := by
  classical
  simp only [traceKloostermanSum]
  rw [Finset.sum_comm]
  simp only [traceZeroCount, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t=0
  · simp [ht]
  · simp only [ht, if_false, ne_eq, not_false_eq_true, true_and]
    rw [prime_character_orthogonality]
    split_ifs <;> simp

/-- The all-frequency trace sum is the actual curve point count. -/
theorem sum_traceKloosterman_eq_curve_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    (∑ m : ZMod p, traceKloostermanSum p a b m) =
      (StepanovPointCount.pointCount (curvePolynomial p a b) : ℂ) := by
  rw [sum_traceKloosterman_eq_trace_count, curve_pointCount_eq_trace p a b hab h2,
    Nat.cast_mul]

/-- The zero frequency contributes exactly q-1. -/
theorem traceKloosterman_zero {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) :
    traceKloostermanSum p a b 0 = (Fintype.card K : ℂ)-1 := by
  classical
  have hcard : 1 ≤ Fintype.card K := Fintype.card_pos
  simp [traceKloostermanSum, Finset.sum_ite, Finset.filter_ne', Nat.cast_sub hcard]

/-- Remove the zero frequency with its exact contribution retained. -/
theorem nonzero_trace_sum_sub_one {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    (∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, traceKloostermanSum p a b m)-1 =
      (StepanovPointCount.pointCount (curvePolynomial p a b) : ℂ)-Fintype.card K := by
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod p)))
    (f := traceKloostermanSum p a b) (Finset.mem_univ (0 : ZMod p))
  rw [traceKloosterman_zero, sum_traceKloosterman_eq_curve_count p a b hab h2] at hsplit
  linear_combination hsplit

/-- Stepanov controls the exact frequency aggregate; individual sums are
not yet bounded by this result. -/
theorem nonzero_trace_sum_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (hodd : Odd (Fintype.card K))
    (hq : 12*p ≤ Fintype.card K) :
    ‖(∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, traceKloostermanSum p a b m)-1‖ <
      8*p*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) := by
  rw [nonzero_trace_sum_sub_one p a b hab (two_ne_zero_of_odd_card hodd)]
  have h := curve_point_count_bound p (Fact.out : p.Prime).one_lt a b hab hodd hq
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using h

/-- At the prime field, the original completion sum is this actual trace
sum at m=1, a=-t, b=j*r. This is an identity, not its missing estimate. -/
theorem complete_inverse_eq_traceKloosterman (p : ℕ) [Fact p.Prime]
    (r : ℕ) (j t : ZMod p) :
    InverseAdditiveCompletion.completeInverseSum r j t =
      traceKloostermanSum p (-t) (j*r) 1 := by
  classical
  unfold InverseAdditiveCompletion.completeInverseSum traceKloostermanSum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x=0
  · simp [hx]
  · have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [dif_pos hu, if_neg hx]
    simp only [one_mul, Algebra.trace_self_apply]
    congr 1
    rw [Units.val_inv_eq_inv_val, hu.unit_spec]
    ring

end NField.Alignment.KloostermanTraceSum
