/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanMinpolyCharacter
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Actual minimal-polynomial fibers in a finite field extension

The roots of an irreducible monic polynomial are parametrized by algebra
homomorphisms from its simple quotient field. Finite-field embedding
counts give exactly its degree when that degree divides the extension
degree, and zero otherwise. The zero element and polynomial X are kept.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanMinpolyFibers
open scoped BigOperators Classical
open Polynomial KloostermanMinpolyCharacter KloostermanPolynomialCharacter
  KloostermanFiniteEulerProduct

/-- Roots of an actual monic irreducible are exactly its minimal-polynomial fiber. -/
noncomputable def rootFiberEquiv {F K : Type*} [Field F] [Field K] [Algebra F K]
    (g : F[X]) (hg : g.Monic) (hi : Irreducible g) :
    (AdjoinRoot g →ₐ[F] K) ≃ {t : K // minpoly F t=g} :=
  (AdjoinRoot.equiv K F g hi.ne_zero).trans
    (Equiv.subtypeEquivRight fun t => by
      rw [mem_aroots,and_iff_right hi.ne_zero]
      exact (minpoly.eq_iff_aeval_eq_zero hi hg).symm.trans eq_comm)

/-- Actual fiber cardinality, including absence of roots at nondivisor degrees. -/
theorem card_minpoly_fiber {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype K] (g : F[X]) (hg : g.Monic) (hi : Irreducible g) :
    Fintype.card {t : K // minpoly F t=g} =
      if g.natDegree ∣ Module.finrank F K then g.natDegree else 0 := by
  letI : Fact (Irreducible g) := ⟨hi⟩
  have hd : Module.finrank F (AdjoinRoot g) = g.natDegree :=
    (AdjoinRoot.powerBasis hi.ne_zero).finrank
  rw [← Nat.card_eq_fintype_card,← Nat.card_congr (rootFiberEquiv g hg hi)]
  by_cases h : g.natDegree ∣ Module.finrank F K
  · rw [if_pos h,FiniteField.natCard_algHom_of_finrank_dvd (hd ▸ h),hd]
  · rw [if_neg h]
    have he : IsEmpty (AdjoinRoot g →ₐ[F] K) := not_nonempty_iff.mp
      (by rw [FiniteField.nonempty_algHom_iff_finrank_dvd,hd]; exact h)
    letI := he
    simp

/-- Every actual field element has a monic irreducible minimal polynomial
within the extension degree cutoff. -/
theorem minpoly_mem_boundedIrreducibles {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (t : K) :
    minpoly (ZMod p) t ∈ boundedIrreducibles p (Module.finrank (ZMod p) K) := by
  rw [mem_boundedIrreducibles]
  have ht := IsIntegral.of_finite (ZMod p) t
  exact ⟨minpoly.monic ht,minpoly.irreducible ht,minpoly.natDegree_le t⟩

/-- Zero is retained: its minimal polynomial is X and its character weight
vanishes since the extension degree is positive. -/
theorem element_character_eq_minpoly_weight {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    (a b m : ZMod p) (t : K) :
    (if t=0 then 0 else ZMod.stdAddChar (m*Algebra.trace (ZMod p) K
      (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t))) =
      polynomialCharacter p a b m (minpoly (ZMod p) t) ^
        (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree) := by
  by_cases ht : t=0
  · subst t
    simp [polynomialCharacter,minpoly.zero,Module.finrank_pos.ne']
  · rw [if_neg ht]
    exact (minpoly_character_pow_eq_trace p a b m t ht).symm

end NField.Alignment.KloostermanMinpolyFibers
