/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectrumLandscape
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.ComputeDegree

/-!
# The base-seven cyclotomic obstruction

The exact polynomials in Proposition 4 of Magnitude Decorrelation have a
nonzero squared-magnitude discrepancy at every primitive fourteenth root.
Character existence and the literal sum correspondence are separate below
the reusable polynomial certificate.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeBaseSeven

open scoped BigOperators ComplexConjugate Polynomial

def shortPolynomial (z : ℂ) : ℂ := 1 + 2*z + z^10 + z^12 + z^13

def bernoulliPolynomial (z : ℂ) : ℂ := ∑ j ∈ Finset.Icc 3 9, z^j

def cyclotomicFourteenValue (z : ℂ) : ℂ := z^6-z^5+z^4-z^3+z^2-z+1

def obstructionPolynomial (z : ℂ) : ℂ := 3-2*z^2+3*z^3-3*z^4+2*z^5

def certificateQuotient (z : ℂ) : ℂ :=
  8+32*z+40*z^2+24*z^3+24*z^4+16*z^5-15*z^7-53*z^8-75*z^9-
    65*z^10-71*z^11-61*z^12-15*z^13+16*z^15+24*z^16+24*z^17+
    40*z^18+32*z^19+8*z^20

theorem bernoulliPolynomial_expanded (z : ℂ) :
    bernoulliPolynomial z = z^3+z^4+z^5+z^6+z^7+z^8+z^9 := by
  norm_num [bernoulliPolynomial, Finset.sum_Icc_succ_top]

theorem laurent_certificate (z : ℂ) (hz : z ≠ 0) :
    z^13 * (8*shortPolynomial z*shortPolynomial z⁻¹ -
      7*bernoulliPolynomial z*bernoulliPolynomial z⁻¹ - 4*obstructionPolynomial z) =
      cyclotomicFourteenValue z * certificateQuotient z := by
  rw [bernoulliPolynomial_expanded, bernoulliPolynomial_expanded]
  unfold shortPolynomial obstructionPolynomial cyclotomicFourteenValue certificateQuotient
  field_simp
  ring

theorem primitive_fourteen_pow_seven {z : ℂ} (hz : IsPrimitiveRoot z 14) : z^7 = -1 := by
  have hs : (z^7)^2 = 1 := by simpa only [← pow_mul] using hz.pow_eq_one
  exact (sq_eq_one_iff.mp hs).resolve_left
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))

theorem primitive_fourteen_cyclotomic {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    cyclotomicFourteenValue z = 0 := by
  have hne : z+1 ≠ 0 := by
    intro heq
    have hzneg : z = -1 := by linear_combination heq
    have htwo := hz.pow_ne_one_of_pos_of_lt (l := 2) (by decide) (by decide)
    exact htwo (by simp [hzneg])
  have hprod : (z+1)*cyclotomicFourteenValue z = 0 := by
    have hseven := primitive_fourteen_pow_seven hz
    unfold cyclotomicFourteenValue
    linear_combination hseven
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- The displayed degree-five remainder cannot vanish at a primitive
fourteenth root, whose minimal polynomial has degree six. -/
theorem obstruction_ne_zero {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    obstructionPolynomial z ≠ 0 := by
  let P : ℚ[X] := 3-2*Polynomial.X^2+3*Polynomial.X^3-
    3*Polynomial.X^4+2*Polynomial.X^5
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℚ[X] => p.coeff 5) h
    norm_num [P, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul_X_pow] at hc
  have hdeg : P.natDegree ≤ 5 := by dsimp [P]; compute_degree
  intro hzero
  have heval : Polynomial.aeval z P = 0 := by
    simpa [P, map_ofNat, obstructionPolynomial] using hzero
  have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ z heval) hP
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hz (by decide),
    Polynomial.natDegree_cyclotomic] at hle
  have hfourteen : Nat.totient 14 = 6 := by decide
  rw [hfourteen] at hle
  omega

theorem normSq_discrepancy {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    (8 * (Complex.normSq (shortPolynomial z) : ℂ) -
      7 * (Complex.normSq (bernoulliPolynomial z) : ℂ)) =
        4 * obstructionPolynomial z := by
  have hz0 : z ≠ 0 := hz.ne_zero (by decide)
  have hs : star z = z⁻¹ := (Complex.inv_eq_conj (hz.norm'_eq_one (by decide))).symm
  have hQ : star (shortPolynomial z) = shortPolynomial z⁻¹ := by
    simp [shortPolynomial, hs]
  have hH : star (bernoulliPolynomial z) = bernoulliPolynomial z⁻¹ := by
    simp [bernoulliPolynomial, hs]
  have h := laurent_certificate z hz0
  rw [primitive_fourteen_cyclotomic hz, zero_mul] at h
  have hd := (mul_eq_zero.mp h).resolve_left (pow_ne_zero 13 hz0)
  simp only [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  rw [hQ, hH]
  linear_combination hd

theorem normSq_discrepancy_ne_zero {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    8 * Complex.normSq (shortPolynomial z) -
      7 * Complex.normSq (bernoulliPolynomial z) ≠ 0 := by
  intro hzero
  have hc := congrArg (fun t : ℝ => (t : ℂ)) hzero
  push_cast at hc
  rw [normSq_discrepancy hz] at hc
  exact obstruction_ne_zero hz ((mul_eq_zero.mp hc).resolve_left (by norm_num))

end NField.Alignment.MagnitudeBaseSeven
