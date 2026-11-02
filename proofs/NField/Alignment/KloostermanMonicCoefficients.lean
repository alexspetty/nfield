/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanPolynomialCharacter

/-!
# Actual monic polynomials and their Kloosterman coefficient sums

Monic degree-n polynomials are parametrized by all n lower coefficients.
The coefficient sum is defined over the actual polynomial subtype.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanMonicCoefficients

open scoped BigOperators
open Polynomial KloostermanPolynomialCharacter

abbrev MonicDegree (K : Type*) [Field K] (n : ℕ) :=
  {f : K[X] // f.Monic ∧ f.natDegree=n}

noncomputable def monicCoefficientEquiv (K : Type*) [Field K] (n : ℕ) :
    MonicDegree K n ≃ (Fin n → K) :=
  (monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv

noncomputable instance monicDegreeFintype (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    Fintype (MonicDegree K n) :=
  Fintype.ofEquiv (Fin n → K) (monicCoefficientEquiv K n).symm

noncomputable def polynomialFromCoefficients {K : Type*} [Field K]
    (n : ℕ) (c : Fin n → K) : K[X] :=
  ((monicCoefficientEquiv K n).symm c).val

theorem polynomialFromCoefficients_monic {K : Type*} [Field K]
    (n : ℕ) (c : Fin n → K) : (polynomialFromCoefficients n c).Monic :=
  ((monicCoefficientEquiv K n).symm c).property.1

theorem polynomialFromCoefficients_natDegree {K : Type*} [Field K]
    (n : ℕ) (c : Fin n → K) : (polynomialFromCoefficients n c).natDegree=n :=
  ((monicCoefficientEquiv K n).symm c).property.2

theorem polynomialFromCoefficients_coeff_lt {K : Type*} [Field K]
    (n : ℕ) (c : Fin n → K) (i : ℕ) (hi : i<n) :
    (polynomialFromCoefficients n c).coeff i = c ⟨i,hi⟩ := by
  change (X^n+((degreeLTEquiv K n).symm c).val).coeff i = _
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add]
  exact congrFun ((degreeLTEquiv K n).apply_symm_apply c) ⟨i,hi⟩

theorem polynomialFromCoefficients_nextCoeff {K : Type*} [Field K]
    (n : ℕ) (hn : 0<n) (c : Fin n → K) :
    (polynomialFromCoefficients n c).nextCoeff = c ⟨n-1,by omega⟩ := by
  rw [nextCoeff, polynomialFromCoefficients_natDegree, if_neg (by omega)]
  exact polynomialFromCoefficients_coeff_lt n c (n-1) (by omega)

@[simp] theorem polynomialFromCoefficients_zero {K : Type*} [Field K]
    (c : Fin 0 → K) : polynomialFromCoefficients 0 c = 1 := by
  simp [polynomialFromCoefficients, monicCoefficientEquiv, monicEquivDegreeLT,
    degreeLTEquiv]

@[simp] theorem polynomialFromCoefficients_one {K : Type*} [Field K]
    (c : Fin 1 → K) : polynomialFromCoefficients 1 c = X+C (c 0) := by
  simp [polynomialFromCoefficients, monicCoefficientEquiv, monicEquivDegreeLT,
    degreeLTEquiv]

/-- Actual sum over all monic degree-n polynomials, including those with
zero constant term (whose character value is zero). -/
noncomputable def degreeCoefficient (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) : ℂ :=
  ∑ f : MonicDegree (ZMod p) n, polynomialCharacter p a b m f.val

theorem degreeCoefficient_eq_sum_coefficients (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) :
    degreeCoefficient p a b m n = ∑ c : Fin n → ZMod p,
      polynomialCharacter p a b m (polynomialFromCoefficients n c) := by
  unfold degreeCoefficient
  exact Fintype.sum_equiv (monicCoefficientEquiv (ZMod p) n) _ _
    (fun f => by simp only [polynomialFromCoefficients, Equiv.symm_apply_apply])

/-- The complete coefficient formula, with constant, next and linear
coefficients taken from three actual coordinates when n>=3. -/
theorem character_from_coefficients (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) (hn : 2≤n) (c : Fin n → ZMod p) :
    polynomialCharacter p a b m (polynomialFromCoefficients n c) =
      if c ⟨0,by omega⟩=0 then 0 else
        ZMod.stdAddChar (-m*a*c ⟨n-1,by omega⟩-
          m*b*(c ⟨1,by omega⟩/c ⟨0,by omega⟩)) := by
  rw [polynomialCharacter_monic p a b m _ (polynomialFromCoefficients_monic n c),
    polynomialFromCoefficients_nextCoeff n (by omega),
    polynomialFromCoefficients_coeff_lt n c 0 (by omega),
    polynomialFromCoefficients_coeff_lt n c 1 (by omega)]

theorem degreeCoefficient_zero (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    degreeCoefficient p a b m 0 = 1 := by
  rw [degreeCoefficient_eq_sum_coefficients]
  simp

end NField.Alignment.KloostermanMonicCoefficients
