/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanMonicCoefficients

/-!
# Evaluation of every polynomial-character coefficient

The actual monic-polynomial sums are 1, the prime Kloosterman sum, p,
and then zero in every degree at least three.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanCoefficientEvaluation

open scoped BigOperators
open Polynomial KloostermanPolynomialCharacter KloostermanMonicCoefficients KloostermanTraceSum

theorem degreeCoefficient_one (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    degreeCoefficient p a b m 1 = traceKloostermanSum p a b m := by
  rw [degreeCoefficient_eq_sum_coefficients]
  simp only [polynomialFromCoefficients_one, traceKloostermanSum, Algebra.trace_self_apply]
  apply Fintype.sum_equiv ((Equiv.funUnique (Fin 1) (ZMod p)).trans (Equiv.neg (ZMod p)))
  intro c
  change polynomialCharacter p a b m (X+C (c 0)) =
    if -c 0=0 then 0 else ZMod.stdAddChar (m*(a*(-c 0)+b/(-c 0)))
  simpa only [map_neg, sub_neg_eq_add] using polynomialCharacter_X_sub_C p a b m (-c 0)

/-- The surviving constant coefficient in degree two is exactly -b/a. -/
theorem quadratic_phase_zero_iff {K : Type*} [Field K]
    (a b m c : K) (ha : a ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) :
    -m*a-m*b/c = 0 ↔ c = -b/a := by
  constructor
  · intro h
    apply (eq_div_iff ha).mpr
    have h' : m*(a*c+b)=0 := by
      field_simp [hc] at h
      linear_combination -h
    have h'' := (mul_eq_zero.mp h').resolve_left hm
    linear_combination h''
  · intro h
    have h' : c*a = -b := (eq_div_iff ha).mp h
    field_simp [hc]
    linear_combination -m*h'

theorem degreeCoefficient_two (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    degreeCoefficient p a b m 2 = (p : ℂ) := by
  rw [degreeCoefficient_eq_sum_coefficients]
  have hparam : (∑ c : Fin 2 → ZMod p,
      polynomialCharacter p a b m (polynomialFromCoefficients 2 c)) =
      ∑ z : ZMod p × ZMod p, if z.1=0 then 0 else
        ZMod.stdAddChar (-m*a*z.2-m*b*(z.2/z.1)) := by
    apply Fintype.sum_equiv (finTwoArrowEquiv (ZMod p))
    intro c
    rw [character_from_coefficients p a b m 2 (by omega)]
    rfl
  rw [hparam, Fintype.sum_prod_type]
  have hroot : -b/a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hinner (c : ZMod p) : (∑ d : ZMod p, if c=0 then 0 else
      ZMod.stdAddChar (-m*a*d-m*b*(d/c))) = if c = -b/a then (p:ℂ) else 0 := by
    by_cases hc : c=0
    · subst c
      simp [Ne.symm hroot]
    · simp only [hc, if_false]
      have hphase (d : ZMod p) : -m*a*d-m*b*(d/c) = d*(-m*a-m*b/c) := by ring
      simp_rw [hphase]
      rw [prime_character_orthogonality]
      simp only [quadratic_phase_zero_iff a b m c ha hm hc]
  simp_rw [hinner]
  simp

/-- Translating only the next coefficient multiplies the character by a
fixed nontrivial phase once degree >= 3. -/
theorem character_top_coefficient_shift (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) (hn : 3≤n) (c : Fin n → ZMod p) :
    polynomialCharacter p a b m (polynomialFromCoefficients n
      (c + Pi.single (⟨n-1,by omega⟩ : Fin n) 1)) =
      ZMod.stdAddChar (-m*a)*polynomialCharacter p a b m (polynomialFromCoefficients n c) := by
  rw [character_from_coefficients p a b m n (by omega),
    character_from_coefficients p a b m n (by omega)]
  have h0 : (⟨0,by omega⟩ : Fin n) ≠ ⟨n-1,by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only at this; omega
  have h1 : (⟨1,by omega⟩ : Fin n) ≠ ⟨n-1,by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only at this; omega
  simp only [Pi.add_apply, Pi.single_apply, h0, h1,
    if_false, if_true, add_zero]
  split_ifs with hc
  · simp
  · rw [← AddChar.map_add_eq_mul]
    congr 1
    ring

/-- All higher-degree monic-polynomial sums vanish by a permutation of
one genuine coefficient coordinate and additive-character nontriviality. -/
theorem degreeCoefficient_eq_zero_of_three_le (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hm : m ≠ 0) (n : ℕ) (hn : 3≤n) :
    degreeCoefficient p a b m n = 0 := by
  rw [degreeCoefficient_eq_sum_coefficients]
  let F : (Fin n → ZMod p) → ℂ := fun c =>
    polynomialCharacter p a b m (polynomialFromCoefficients n c)
  let e := Equiv.addRight (Pi.single (⟨n-1,by omega⟩ : Fin n) 1 : Fin n → ZMod p)
  have hsum : (∑ c, F c) = ZMod.stdAddChar (-m*a)*(∑ c, F c) := by
    calc
      _ = ∑ c, F (e c) := (Equiv.sum_comp e F).symm
      _ = _ := by
        simp only [F, e, Equiv.coe_addRight, character_top_coefficient_shift p a b m n hn]
        rw [Finset.mul_sum]
  have hphase : ZMod.stdAddChar (-m*a) ≠ 1 := by
    intro h
    have hz : -m*a = 0 := ZMod.injective_stdAddChar
      (h.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
    exact mul_ne_zero (neg_ne_zero.mpr hm) ha hz
  have hprod : (1-ZMod.stdAddChar (-m*a))*(∑ c, F c)=0 := by
    linear_combination hsum
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (Ne.symm hphase))

end NField.Alignment.KloostermanCoefficientEvaluation
