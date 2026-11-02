/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanPrimePowerCoefficients
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Minimal polynomials and the trace of a nonzero element and its inverse

The inverse minimal polynomial is the normalized reverse of the actual
minimal polynomial. The trace formulas retain the exact extension-degree
multiplicity; no division by a field characteristic is used.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanMinpolyTrace
open scoped BigOperators Classical
open Polynomial IntermediateField

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

omit [FiniteDimensional F K] in
theorem adjoin_inverse_eq (t : K) : F⟮t⁻¹⟯ = F⟮t⟯ := by
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact (F⟮t⟯).inv_mem (mem_adjoin_simple_self F t)
  · rw [adjoin_simple_le_iff]
    simpa using (F⟮t⁻¹⟯).inv_mem (mem_adjoin_simple_self F t⁻¹)

theorem minpoly_inverse_natDegree (t : K) :
    (minpoly F t⁻¹).natDegree = (minpoly F t).natDegree := by
  rw [← adjoin.finrank (IsIntegral.of_finite F t⁻¹),
    ← adjoin.finrank (IsIntegral.of_finite F t),adjoin_inverse_eq]

/-- Reversal has the original linear coefficient as its next coefficient
when the constant coefficient is nonzero and the degree is positive. -/
theorem nextCoeff_reverse_of_coeff_zero_ne_zero (g : F[X])
    (h0 : g.coeff 0≠0) (hd : 0<g.natDegree) : g.reverse.nextCoeff = g.coeff 1 := by
  have ht : g.natTrailingDegree=0 := natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hr : g.reverse.natDegree=g.natDegree := by rw [reverse_natDegree,ht,Nat.sub_zero]
  rw [nextCoeff,hr,if_neg (by omega),coeff_reverse,revAt_le (Nat.sub_le _ _)]
  congr 1
  omega

/-- The exact normalized reciprocal minimal polynomial. -/
theorem minpoly_inverse (t : K) (ht : t≠0) :
    minpoly F t⁻¹ = (minpoly F t).reverse * C ((minpoly F t).coeff 0)⁻¹ := by
  let g := minpoly F t
  have hg : g.Monic := minpoly.monic (IsIntegral.of_finite F t)
  have h0 : g.coeff 0≠0 := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite F t) ht
  have hl : g.reverse.leadingCoeff=g.coeff 0 := by
    rw [reverse_leadingCoeff,trailingCoeff_eq_coeff_zero h0]
  have hm : (g.reverse*C (g.coeff 0)⁻¹).Monic := by
    rw [Monic,leadingCoeff_mul,leadingCoeff_C,hl,mul_inv_cancel₀ h0]
  have hv : aeval t⁻¹ g.reverse=0 := by
    letI := invertibleOfNonzero ht
    have h := (eval₂_reverse_eq_zero_iff (algebraMap F K) t g).mpr
      (minpoly.aeval F t)
    simpa only [invOf_eq_inv,aeval_def] using h
  have hv' : aeval t⁻¹ (g.reverse*C (g.coeff 0)⁻¹)=0 := by
    rw [aeval_mul,hv,zero_mul]
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite F t⁻¹)) hm (minpoly.dvd F t⁻¹ hv')
  rw [minpoly_inverse_natDegree,natDegree_mul_C (inv_ne_zero h0)]
  exact g.reverse_natDegree_le

/-- The inverse trace is the negative linear/constant coefficient ratio,
multiplied by the actual extension degree over the simple subfield. -/
theorem trace_inverse (t : K) (ht : t≠0) :
    Algebra.trace F K t⁻¹ = (Module.finrank F⟮t⟯ K : F) *
      (-((minpoly F t).coeff 1/(minpoly F t).coeff 0)) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,
    adjoin_inverse_eq,minpoly_inverse t ht,nextCoeff_mul_C,
    nextCoeff_reverse_of_coeff_zero_ne_zero _
      (minpoly.coeff_zero_ne_zero (IsIntegral.of_finite F t) ht)
      (minpoly.natDegree_pos (IsIntegral.of_finite F t)),div_eq_mul_inv]

/-- The degree quotient is an exact natural-number quotient from the tower law. -/
theorem finrank_over_adjoin_eq_div (t : K) :
    Module.finrank F⟮t⟯ K = Module.finrank F K / (minpoly F t).natDegree := by
  have h := Module.finrank_mul_finrank F F⟮t⟯ K
  rw [adjoin.finrank (IsIntegral.of_finite F t)] at h
  rw [← h,Nat.mul_div_right _ (minpoly.natDegree_pos (IsIntegral.of_finite F t))]

theorem minpoly_degree_dvd_finrank (t : K) :
    (minpoly F t).natDegree ∣ Module.finrank F K := by
  refine ⟨Module.finrank F⟮t⟯ K,?_⟩
  simpa only [adjoin.finrank (IsIntegral.of_finite F t)] using
    (Module.finrank_mul_finrank F F⟮t⟯ K).symm

end NField.Alignment.KloostermanMinpolyTrace
