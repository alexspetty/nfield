/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovConstraintSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Rounded parameters for Stepanov's point-count bound

The real block cutoff is rounded upward, while the largest block exponent
uses J-1. This retains the strict upper bound needed for the source constant.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovParameters

open scoped BigOperators

noncomputable def order (q : ℕ) : ℕ := Nat.ceil (Real.sqrt q)

def coefficientDegree (q m : ℕ) : ℕ := (q-m-1)/2

noncomputable def blockCount (q m ell : ℕ) : ℕ :=
  Nat.ceil ((ell : ℝ)/2 + (ell : ℝ)^2*m/q)

/-- The coefficient range is maximal for the strict degree restriction. -/
theorem coefficient_degree_bounds (q m : ℕ) (hmq : m < q) :
    2*coefficientDegree q m + m < q ∧ q ≤ 2*(coefficientDegree q m+1)+m := by
  unfold coefficientDegree
  omega

/-- The rounded square root is positive, squares above q, and fits below
q/3 in the range used by the source. -/
theorem order_bounds (q : ℕ) (hq : 18 ≤ q) :
    0 < order q ∧ q ≤ (order q)^2 ∧ 3*order q ≤ q := by
  have hqr : (18 : ℝ) ≤ q := by exact_mod_cast hq
  have hspos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
  have hlo := Nat.le_ceil (Real.sqrt (q : ℝ))
  have hhi := Nat.ceil_lt_add_one (Real.sqrt_nonneg (q : ℝ))
  have hquarter : Real.sqrt (q : ℝ) ≤ (q : ℝ)/4 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  refine ⟨Nat.ceil_pos.mpr hspos, ?_, ?_⟩
  · change q ≤ (Nat.ceil (Real.sqrt (q : ℝ)))^2
    exact_mod_cast (show (q : ℝ) ≤ (Nat.ceil (Real.sqrt (q : ℝ)) : ℝ)^2 by nlinarith)
  · change 3 * Nat.ceil (Real.sqrt (q : ℝ)) ≤ q
    exact_mod_cast (show (3 : ℝ) * Nat.ceil (Real.sqrt (q : ℝ)) ≤ q by nlinarith)

/-- Both sides of the ceiling are used: enough blocks for dimension
counting, but a strictly smaller last exponent for the degree bound. -/
theorem block_count_bounds (q m ell : ℕ) (hq : 0 < q) (hm : 0 < m) (hell : 0 < ell) :
    0 < blockCount q m ell ∧
    (ell : ℝ)/2 + (ell : ℝ)^2*m/q ≤ blockCount q m ell ∧
    ((blockCount q m ell-1 : ℕ) : ℝ) < (ell : ℝ)/2 + (ell : ℝ)^2*m/q := by
  have hp : (0 : ℝ) < (ell : ℝ)/2 + (ell : ℝ)^2*m/q := by positivity
  have hJ : 0 < blockCount q m ell := Nat.ceil_pos.mpr hp
  refine ⟨hJ, Nat.le_ceil _, ?_⟩
  apply Nat.lt_ceil.mp
  change blockCount q m ell - 1 < blockCount q m ell
  omega

/-- The source's numerical dimension argument, before specializing the
integer parameters. T represents the triangular number ell*(ell-1)/2. -/
theorem dimension_inequality_real (q m ell R J T : ℝ)
    (hq : 0 < q) (hm : 1 ≤ m) (hell : 0 < ell)
    (hsmall : 6*m < q) (hellq : 3*ell ≤ q)
    (hR : 2*R+m < q) (hslots : q ≤ 2*(R+1)+m)
    (hJ : ell/2+ell^2*m/q ≤ J) (hT : 2*T ≤ ell^2) :
    ell*(R+J)+T*(m-1) < 2*J*(R+1) := by
  have hdelta : 0 < J-ell/2 := by
    have hterm : 0 < ell^2*m/q := by positivity
    linarith
  have hJpos : 0 < J := by linarith
  have hgap : q/2 < q-m-ell := by linarith
  have hquot : ell^2*m ≤ (J-ell/2)*q :=
    (div_le_iff₀ hq).mp (by linarith)
  have hproduct := mul_lt_mul_of_pos_left hgap hdelta
  have hmain : ell^2*m/2 < (J-ell/2)*(q-m-ell) := by nlinarith
  have hvars : J*(q-m) ≤ 2*J*(R+1) := by
    nlinarith [mul_nonneg (le_of_lt hJpos) (show 0 ≤ 2*(R+1)+m-q by linarith)]
  have hfirst : ell*(R+J) < ell*((q-m)/2+J) :=
    mul_lt_mul_of_pos_left (by linarith) hell
  have hsecond : T*(m-1) ≤ ell^2/2*(m-1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- The actual rounded parameters discharge the finite-dimensional
existence theorem's strict scalar inequality. -/
theorem rounded_dimension_inequality (q m : ℕ) (hm : 3 ≤ m) (hmq : 6*m < q) :
    (∑ k : Fin (order q),
      (coefficientDegree q m + blockCount q m (order q) + k.val*(m-1))) <
      2*blockCount q m (order q)*(coefficientDegree q m+1) := by
  have hq : 18 ≤ q := by omega
  obtain ⟨hell, _, hellq⟩ := order_bounds q hq
  obtain ⟨hR, hslots⟩ := coefficient_degree_bounds q m (by omega)
  obtain ⟨_, hJ, _⟩ := block_count_bounds q m (order q) (by omega) (by omega) hell
  have htri : 2*(order q*(order q-1)/2) ≤ (order q)^2 := by
    have hdiv := Nat.div_mul_le_self (order q*(order q-1)) 2
    have hsub : order q-1 ≤ order q := Nat.sub_le _ _
    nlinarith
  have h := dimension_inequality_real (q : ℝ) m (order q) (coefficientDegree q m)
    (blockCount q m (order q)) (order q*(order q-1)/2 : ℕ)
    (by positivity) (by exact_mod_cast (show 1 ≤ m by omega))
    (by exact_mod_cast hell) (by exact_mod_cast hmq) (by exact_mod_cast hellq)
    (by exact_mod_cast hR) (by exact_mod_cast hslots) hJ (by exact_mod_cast htri)
  rw [StepanovConstraintSpace.equation_count]
  have hm1r : ((m-1 : ℕ) : ℝ) = (m : ℝ)-1 := by
    simp only [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
  exact_mod_cast (show (order q : ℝ)*(coefficientDegree q m + blockCount q m (order q)) +
    ((order q*(order q-1)/2 : ℕ) : ℝ)*((m-1 : ℕ) : ℝ) <
      2*(blockCount q m (order q) : ℝ)*(coefficientDegree q m+1) by rwa [hm1r])

/-- The exact degree budget with the real block cutoff. Keeping the strict
last-index bound preserves the source's constant. -/
theorem degree_budget_real (q m ell R d last : ℝ)
    (hq : 0 < q) (hm : 3 ≤ m) (hellq : 3*ell ≤ q)
    (hd : 2*d+1 = q) (hR : 2*R+m < q)
    (hlast : last < ell/2+ell^2*m/q) :
    R+(ell+d)*m+last*q < ell*q/2+ell^2*m+m*q := by
  have hlastq : last*q < ell*q/2+ell^2*m := by
    calc
      _ < (ell/2+ell^2*m/q)*q := mul_lt_mul_of_pos_right hlast hq
      _ = _ := by field_simp
  have hellm : ell*m ≤ q*m/3 := by
    nlinarith [mul_nonneg (show 0 ≤ m by linarith) (show 0 ≤ q-3*ell by linarith)]
  have hmq : q/2+q*m/3 ≤ m*q/2 := by
    nlinarith [mul_nonneg (le_of_lt hq) (show 0 ≤ m-3 by linarith)]
  have hdm := congrArg (fun x : ℝ => x*m) hd
  nlinarith

/-- A root count at the rounded parameters has the printed one-sided
constant, with every dimension/degree parameter already fixed. -/
theorem rounded_card_bound (q m d N : ℕ) (hm : 3 ≤ m) (hmq : 6*m < q)
    (hd : 2*d+1 = q)
    (hbound : N*order q ≤ coefficientDegree q m + (order q+d)*m +
      (blockCount q m (order q)-1)*q) :
    (N : ℝ) < (q : ℝ)/2 + 2*m*order q := by
  have hq : 18 ≤ q := by omega
  obtain ⟨hell, hsq, hellq⟩ := order_bounds q hq
  obtain ⟨hR, _⟩ := coefficient_degree_bounds q m (by omega)
  obtain ⟨_, _, hlast⟩ := block_count_bounds q m (order q) (by omega) (by omega) hell
  have hdegree := degree_budget_real (q : ℝ) m (order q) (coefficientDegree q m) d
    (blockCount q m (order q)-1 : ℕ) (by positivity) (by exact_mod_cast hm)
    (by exact_mod_cast hellq) (by exact_mod_cast hd) (by exact_mod_cast hR) hlast
  have hboundr : (N : ℝ)*order q ≤ (coefficientDegree q m : ℝ) +
      (order q+d : ℝ)*m + ((blockCount q m (order q)-1 : ℕ) : ℝ)*q := by
    exact_mod_cast hbound
  have hellr : (0 : ℝ) < order q := by exact_mod_cast hell
  have hsqmul : (m : ℝ)*q ≤ m*(order q : ℝ)^2 := by
    gcongr
    exact_mod_cast hsq
  by_contra! h
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hellr)
  nlinarith

end NField.Alignment.StepanovParameters
