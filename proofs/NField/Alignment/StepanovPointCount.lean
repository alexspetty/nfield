/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovSelectedPointBound
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The finite-field point-count estimate in Stepanov's method

The actual number of pairs (x,y) with y^2=f(x) differs from the field
cardinality by less than 4*deg(f)*ceil(sqrt(q)), under the source's degree,
odd-cardinality and algebraic-closure nonsquare hypotheses.
This is the point-count ingredient, not yet the Kloosterman estimate.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovPointCount

open scoped BigOperators
open Polynomial StepanovParameters StepanovSelectedPointBound

/-- Roots of f together with one selected quadratic-character class. -/
def characterClass {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (sign : ℤ) : Finset K :=
  Finset.univ.filter fun x => quadraticChar K (f.eval x) = 0 ∨
    quadraticChar K (f.eval x) = sign

theorem char_ne_two_of_odd_card {K : Type*} [Field K] [Fintype K]
    (hodd : Odd (Fintype.card K)) : ringChar K ≠ 2 := by
  intro h
  have heven := FiniteField.even_card_of_char_two h
  obtain ⟨n, hn⟩ := hodd
  omega

/-- The optimized power-value bound applies to each quadratic-character
class, retaining the roots of f in both selected sets. -/
theorem character_class_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree < Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K)))) (sign : ℤ) :
    ((characterClass f sign).card : ℝ) < (Fintype.card K : ℝ)/2 +
      2*f.natDegree*order (Fintype.card K) := by
  have hchar := char_ne_two_of_odd_card hodd
  have hexp : (Fintype.card K-1)/2 = Fintype.card K/2 := by
    obtain ⟨n, hn⟩ := hodd
    omega
  apply selected_point_bound f hm hmq hodd hns (sign : K)
  intro x hx
  rcases (Finset.mem_filter.mp hx).2 with hz | hs
  · exact Or.inl (quadraticChar_eq_zero_iff.mp hz)
  · right
    rw [hexp, ← quadraticChar_eq_pow_of_char_ne_two' hchar, hs]

/-- Either signed character sum is controlled by its selected class count.
The inequality also accounts for points where f vanishes. -/
theorem signed_character_sum_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1) :
    (sign : ℝ) * ∑ x : K, (quadraticChar K (f.eval x) : ℝ) ≤
      2*((characterClass f sign).card : ℝ) - Fintype.card K := by
  have hpoint (x : K) : (sign : ℝ)*(quadraticChar K (f.eval x) : ℝ) ≤
      2*(if quadraticChar K (f.eval x) = 0 ∨ quadraticChar K (f.eval x) = sign
        then (1 : ℝ) else 0)-1 := by
    rcases hsign with rfl | rfl <;>
      rcases quadraticChar_isQuadratic K (f.eval x) with h | h | h <;> norm_num [h]
  have hcard : ((characterClass f sign).card : ℝ) =
      ∑ x : K, if quadraticChar K (f.eval x) = 0 ∨ quadraticChar K (f.eval x) = sign
        then (1 : ℝ) else 0 := by
    simp only [characterClass, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  calc
    _ = ∑ x : K, (sign : ℝ)*(quadraticChar K (f.eval x) : ℝ) := Finset.mul_sum ..
    _ ≤ ∑ x : K, (2*(if quadraticChar K (f.eval x) = 0 ∨ quadraticChar K (f.eval x) = sign
        then (1 : ℝ) else 0)-1) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hcard]; simp

/-- The quadratic-character sum obeys the source's two-sided constant. -/
theorem quadratic_character_sum_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree < Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K)))) :
    |∑ x : K, (quadraticChar K (f.eval x) : ℝ)| <
      4*f.natDegree*order (Fintype.card K) := by
  have hp := character_class_bound f hm hmq hodd hns 1
  have hn := character_class_bound f hm hmq hodd hns (-1)
  have hsp := signed_character_sum_le f 1 (Or.inl rfl)
  have hsn := signed_character_sum_le f (-1) (Or.inr rfl)
  norm_num only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hsp hsn
  apply abs_lt.mpr
  constructor <;> linarith

/-- The actual affine point count, as a finite set of ordered pairs. -/
def pointCount {K : Type*} [Field K] [Fintype K] [DecidableEq K] (f : K[X]) : ℕ :=
  (Finset.univ.filter fun xy : K × K => xy.2^2 = f.eval xy.1).card

/-- Split the actual pair count into its fibers over x. -/
theorem pointCount_eq_sum {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) :
    pointCount f = ∑ x : K, (Finset.univ.filter fun y : K => y^2 = f.eval x).card := by
  simp only [pointCount, Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- The exact point-count/character identity, with all roots included. -/
theorem pointCount_eq_card_add_character_sum {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hchar : ringChar K ≠ 2) :
    (pointCount f : ℝ) = Fintype.card K + ∑ x : K, (quadraticChar K (f.eval x) : ℝ) := by
  have hfiber (x : K) :
      ((Finset.univ.filter fun y : K => y^2 = f.eval x).card : ℝ) =
        (quadraticChar K (f.eval x) : ℝ)+1 := by
    have h := quadraticChar_card_sqrts hchar (f.eval x)
    simp only [Set.toFinset_setOf] at h
    exact_mod_cast h
  rw [pointCount_eq_sum, Nat.cast_sum]
  simp_rw [hfiber]
  rw [Finset.sum_add_distrib]
  simp [add_comm]

/-- The source's finite-field point-count theorem. The weak q>=6m
hypothesis becomes strict because q is odd. Parameter selection, auxiliary
existence/nonvanishing, and translation are all proved upstream. -/
theorem point_count_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree ≤ Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K)))) :
    |(pointCount f : ℝ) - Fintype.card K| <
      4*f.natDegree*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) := by
  have hstrict : 6*f.natDegree < Fintype.card K := by
    obtain ⟨n, hn⟩ := hodd
    omega
  rw [pointCount_eq_card_add_character_sum f (char_ne_two_of_odd_card hodd),
    add_sub_cancel_left]
  exact quadratic_character_sum_bound f hm hstrict hodd hns

end NField.Alignment.StepanovPointCount
