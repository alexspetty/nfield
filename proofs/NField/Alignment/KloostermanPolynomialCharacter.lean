/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanTraceSum
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The polynomial character in the Kloosterman L-series

The coefficient formula is normalized by the leading coefficient. Its
multiplicativity on all actual polynomials is proved, including vanishing
constant terms. Constants use nextCoeff=0.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanPolynomialCharacter

open scoped BigOperators
open Polynomial

noncomputable def polynomialCharacter (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f : (ZMod p)[X]) : ℂ :=
  if f.coeff 0=0 then 0 else
    ZMod.stdAddChar (-m*a*(f.nextCoeff/f.leadingCoeff)-m*b*(f.coeff 1/f.coeff 0))

/-- On monic polynomials the leading coefficient is one. -/
theorem polynomialCharacter_monic (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f : (ZMod p)[X]) (hf : f.Monic) :
    polynomialCharacter p a b m f = if f.coeff 0=0 then 0 else
      ZMod.stdAddChar (-m*a*f.nextCoeff-m*b*(f.coeff 1/f.coeff 0)) := by
  simp only [polynomialCharacter, hf.leadingCoeff, div_one]

@[simp] theorem polynomialCharacter_one (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    polynomialCharacter p a b m 1 = 1 := by
  simp [polynomialCharacter, nextCoeff, coeff_one]

@[simp] theorem polynomialCharacter_zero (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    polynomialCharacter p a b m 0 = 0 := by
  simp [polynomialCharacter]

/-- The next coefficient of a product, including constant and zero polynomials. -/
theorem nextCoeff_product {K : Type*} [Field K] (f g : K[X]) :
    (f*g).nextCoeff = f.leadingCoeff*g.nextCoeff+f.nextCoeff*g.leadingCoeff := by
  rw [← coeff_one_reverse, reverse_mul_of_domain, mul_coeff_one,
    coeff_zero_reverse, coeff_zero_reverse, coeff_one_reverse, coeff_one_reverse]

/-- The normalized source character is multiplicative on all polynomials. -/
theorem polynomialCharacter_mul (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f g : (ZMod p)[X]) :
    polynomialCharacter p a b m (f*g) =
      polynomialCharacter p a b m f * polynomialCharacter p a b m g := by
  unfold polynomialCharacter
  rw [mul_coeff_zero]
  by_cases hf0 : f.coeff 0=0
  · simp [hf0]
  by_cases hg0 : g.coeff 0=0
  · simp [hg0]
  have hf : f ≠ 0 := by intro h; simp [h] at hf0
  have hg : g ≠ 0 := by intro h; simp [h] at hg0
  have hfl : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hgl : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
  simp only [hf0, hg0, mul_ne_zero hf0 hg0, if_false]
  rw [nextCoeff_product, leadingCoeff_mul, mul_coeff_one, ← AddChar.map_add_eq_mul]
  congr 1
  field_simp
  ring

/-- The actual polynomial character as a multiplicative map with zero. -/
noncomputable def polynomialCharacterHom (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) : (ZMod p)[X] →*₀ ℂ where
  toFun := polynomialCharacter p a b m
  map_one' := polynomialCharacter_one p a b m
  map_zero' := polynomialCharacter_zero p a b m
  map_mul' := polynomialCharacter_mul p a b m

/-- Every polynomial-character value has norm at most one. -/
theorem polynomialCharacter_norm_le_one (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f : (ZMod p)[X]) :
    ‖polynomialCharacter p a b m f‖ ≤ 1 := by
  unfold polynomialCharacter
  split_ifs <;> simp [ZMod.stdAddChar_apply]

/-- Multiplicativity on monic polynomials, with the zero-constant cases included. -/
theorem polynomialCharacter_mul_monic (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f g : (ZMod p)[X]) (hf : f.Monic) (hg : g.Monic) :
    polynomialCharacter p a b m (f*g) =
      polynomialCharacter p a b m f * polynomialCharacter p a b m g := by
  rw [polynomialCharacter_monic p a b m (f*g) (hf.mul hg),
    polynomialCharacter_monic p a b m f hf, polynomialCharacter_monic p a b m g hg]
  rw [mul_coeff_zero, hf.nextCoeff_mul hg, mul_coeff_one]
  by_cases hf0 : f.coeff 0=0
  · simp [hf0]
  by_cases hg0 : g.coeff 0=0
  · simp [hg0]
  simp only [hf0, hg0, mul_ne_zero hf0 hg0, if_false]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  field_simp
  ring

/-- On X-t the polynomial character is the literal inverse additive phase. -/
theorem polynomialCharacter_X_sub_C (p : ℕ) [Fact p.Prime]
    (a b m t : ZMod p) :
    polynomialCharacter p a b m (X-C t) = if t=0 then 0 else
      ZMod.stdAddChar (m*(a*t+b/t)) := by
  rw [polynomialCharacter_monic p a b m _ (monic_X_sub_C t)]
  have h0 : (X-C t : (ZMod p)[X]).coeff 0 = -t := by simp
  have h1 : (X-C t : (ZMod p)[X]).coeff 1 = 1 := by simp
  rw [h0, h1, nextCoeff_X_sub_C]
  simp only [neg_eq_zero]
  split_ifs with ht
  · rfl
  · congr 1
    simp only [div_neg, one_div]
    ring

end NField.Alignment.KloostermanPolynomialCharacter
