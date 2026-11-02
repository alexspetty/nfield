/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanCoefficientEvaluation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The actual polynomial-character L-series is quadratic

Every coefficient is the sum over actual monic polynomials. The quadratic
formula follows from the proved coefficient evaluations. Its two factors
are constructed algebraically. The extension-field trace relation and
root-modulus estimates remain separate obligations.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanQuadraticLSeries

open scoped BigOperators
open KloostermanMonicCoefficients KloostermanCoefficientEvaluation KloostermanTraceSum

noncomputable def formalLSeries (p : ℕ) [Fact p.Prime] (a b m : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (degreeCoefficient p a b m)

noncomputable def quadraticLPolynomial (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) : Polynomial ℂ :=
  1+Polynomial.C (traceKloostermanSum p a b m)*Polynomial.X+
    Polynomial.C (p:ℂ)*Polynomial.X^2

/-- A complete formula for every actual monic-polynomial coefficient. -/
theorem degreeCoefficient_cases (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) (n : ℕ) :
    degreeCoefficient p a b m n =
      if n=0 then 1 else if n=1 then traceKloostermanSum p a b m else
        if n=2 then (p:ℂ) else 0 := by
  split_ifs with h0 h1 h2
  · subst n; exact degreeCoefficient_zero p a b m
  · subst n; exact degreeCoefficient_one p a b m
  · subst n; exact degreeCoefficient_two p a b m ha hb hm
  · exact degreeCoefficient_eq_zero_of_three_le p a b m ha hm n (by omega)

/-- The actual formal L-series equals the source quadratic polynomial. -/
theorem formalLSeries_eq_quadratic (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    formalLSeries p a b m = (quadraticLPolynomial p a b m : PowerSeries ℂ) := by
  ext n
  rw [formalLSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe,
    degreeCoefficient_cases p a b m ha hb hm]
  simp only [quadraticLPolynomial, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  by_cases h0 : n=0
  · subst n; norm_num
  by_cases h1 : n=1
  · subst n; norm_num
  by_cases h2 : n=2
  · subst n; norm_num
  simp only [h0,h1,h2,Ne.symm h1,if_false,mul_zero,add_zero]

/-- The two roots of the reciprocal quadratic have the source sum and product. -/
theorem exists_quadratic_factors (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    ∃ α β : ℂ, α+β = -traceKloostermanSum p a b m ∧ α*β = p ∧
      quadraticLPolynomial p a b m =
        (1-Polynomial.C α*Polynomial.X)*(1-Polynomial.C β*Polynomial.X) := by
  let S := traceKloostermanSum p a b m
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (S^2-4*(p:ℂ)) (by omega : 0<2)
  let α := (-S+z)/2
  let β := (-S-z)/2
  have hs : α+β = -S := by dsimp [α,β]; ring
  have hp : α*β = (p:ℂ) := by
    dsimp [α,β]
    linear_combination -hz/4
  refine ⟨α,β,hs,hp,?_⟩
  unfold quadraticLPolynomial
  have hsC := congrArg Polynomial.C hs
  have hpC := congrArg Polynomial.C hp
  simp only [map_add, map_neg, map_mul] at hsC hpC
  linear_combination (Polynomial.X : Polynomial ℂ)*hsC - Polynomial.X^2*hpC

/-- The formal L-series factors through the actual two reciprocal roots.
No bound on their moduli is asserted. -/
theorem formalLSeries_factors (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    ∃ α β : ℂ, α+β = -traceKloostermanSum p a b m ∧ α*β = p ∧
      formalLSeries p a b m =
        (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X) := by
  obtain ⟨α,β,hs,hp,hfactor⟩ := exists_quadratic_factors p a b m
  refine ⟨α,β,hs,hp,?_⟩
  rw [formalLSeries_eq_quadratic p a b m ha hb hm, hfactor]
  simp

/-- The algebraic recurrence for the actual reciprocal roots. Connecting
these power sums to extension-field Kloosterman sums remains to be proved. -/
theorem root_power_sum_recurrence (S P α β : ℂ)
    (hs : α+β = -S) (hp : α*β=P) (n : ℕ) :
    α^(n+2)+β^(n+2) = -S*(α^(n+1)+β^(n+1))-P*(α^n+β^n) := by
  rw [← hp, ← hs]
  simp only [pow_succ]
  ring

end NField.Alignment.KloostermanQuadraticLSeries
