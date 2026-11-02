/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanMinpolyTrace

/-!
# The actual polynomial character on a minimal polynomial

The extension trace of a*t+b/t is the degree multiplicity times the
coefficient phase of the minimal polynomial. Applying the additive
character gives the exact prime-power weight for every nonzero element.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanMinpolyCharacter
open scoped BigOperators Classical
open Polynomial KloostermanMinpolyTrace KloostermanPolynomialCharacter

/-- The two coefficient ratios give the exact traced inverse-additive phase. -/
theorem trace_inverse_phase {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    (a b : ZMod p) (t : K) (ht : t≠0) :
    Algebra.trace (ZMod p) K
      (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t) =
      (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree : ℕ) *
        (-a*(minpoly (ZMod p) t).nextCoeff-
          b*((minpoly (ZMod p) t).coeff 1/(minpoly (ZMod p) t).coeff 0)) := by
  have hlin : Algebra.trace (ZMod p) K
      (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t) =
      a*Algebra.trace (ZMod p) K t+b*Algebra.trace (ZMod p) K t⁻¹ := by
    simp only [div_eq_mul_inv,← Algebra.smul_def,map_add,map_smul,smul_eq_mul]
  rw [hlin,trace_eq_finrank_mul_minpoly_nextCoeff,trace_inverse t ht,
    finrank_over_adjoin_eq_div]
  ring

/-- Every nonzero element contributes the exact power of its actual
minimal polynomial's character. -/
theorem minpoly_character_pow_eq_trace {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    (a b m : ZMod p) (t : K) (ht : t≠0) :
    polynomialCharacter p a b m (minpoly (ZMod p) t) ^
      (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree) =
      ZMod.stdAddChar (m*Algebra.trace (ZMod p) K
        (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t)) := by
  rw [polynomialCharacter_monic p a b m _ (minpoly.monic (IsIntegral.of_finite (ZMod p) t)),
    if_neg (minpoly.coeff_zero_ne_zero (IsIntegral.of_finite (ZMod p) t) ht),
    ← AddChar.map_nsmul_eq_pow,trace_inverse_phase p a b t ht]
  congr 1
  rw [nsmul_eq_mul]
  ring

/-- The local trace formula for every nonzero root of any actual monic
irreducible polynomial; the polynomial is proved to be the minimal one. -/
theorem irreducible_character_pow_eq_trace {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    (a b m : ZMod p) (g : (ZMod p)[X]) (hg : g.Monic) (hi : Irreducible g)
    (t : K) (ht : t≠0) (hr : aeval t g=0) :
    polynomialCharacter p a b m g ^ (Module.finrank (ZMod p) K / g.natDegree) =
      ZMod.stdAddChar (m*Algebra.trace (ZMod p) K
        (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t)) := by
  have he : g=minpoly (ZMod p) t := minpoly.eq_of_irreducible_of_monic hi hr hg
  rw [he]
  exact minpoly_character_pow_eq_trace p a b m t ht

end NField.Alignment.KloostermanMinpolyCharacter
