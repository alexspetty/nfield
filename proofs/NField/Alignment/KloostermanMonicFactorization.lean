/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanMonicCoefficients
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Unique factorization of the actual monic-polynomial coefficient sums

The degree-n monic polynomials correspond bijectively to multisets of
actual monic irreducibles whose degrees sum to n. Repeated factors are
retained. The character sum is reindexed through this bijection, without
excluding the polynomial X or dividing by a character value.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanMonicFactorization

open scoped BigOperators
open Polynomial UniqueFactorizationMonoid KloostermanMonicCoefficients
  KloostermanPolynomialCharacter

abbrev FactorizationDegree (K : Type*) [Field K] [DecidableEq K] (n : ℕ) :=
  {s : Multiset K[X] // (∀ f ∈ s, f.Monic ∧ Irreducible f) ∧
    (s.map Polynomial.natDegree).sum = n}

/-- Every normalized factor of a monic polynomial is an actual monic
irreducible, not merely an associate class. -/
theorem normalizedFactors_properties {K : Type*} [Field K] [DecidableEq K]
    (f : K[X]) (hf : f.Monic) (g : K[X]) (hg : g ∈ normalizedFactors f) :
    g.Monic ∧ Irreducible g := by
  classical
  have h := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp hg
  exact ⟨h.2.1,h.1⟩

theorem monic_prod_normalizedFactors {K : Type*} [Field K] [DecidableEq K]
    (f : K[X]) (hf : f.Monic) : (normalizedFactors f).prod = f := by
  classical
  rw [prod_normalizedFactors_eq hf.ne_zero, hf.normalize_eq_self]

theorem degree_sum_normalizedFactors {K : Type*} [Field K] [DecidableEq K]
    (f : K[X]) (hf : f.Monic) :
    ((normalizedFactors f).map Polynomial.natDegree).sum = f.natDegree := by
  rw [← Polynomial.natDegree_multiset_prod_of_monic _
    (fun g hg => (normalizedFactors_properties f hf g hg).1),
    monic_prod_normalizedFactors f hf]

theorem normalizedFactors_prod_monic_irreducible {K : Type*} [Field K] [DecidableEq K]
    (s : Multiset K[X]) (hs : ∀ f ∈ s, f.Monic ∧ Irreducible f) :
    normalizedFactors s.prod = s := by
  classical
  rw [normalizedFactors_prod_eq s (fun f hf => (hs f hf).2)]
  calc
    s.map normalize = s.map id := Multiset.map_congr rfl
      (fun f hf => (hs f hf).1.normalize_eq_self)
    _ = s := Multiset.map_id _

/-- Unique factorization preserves the exact total degree. -/
noncomputable def monicFactorizationEquiv (K : Type*) [Field K] [DecidableEq K] (n : ℕ) :
    MonicDegree K n ≃ FactorizationDegree K n where
  toFun f := ⟨normalizedFactors f.val,
    normalizedFactors_properties f.val f.property.1,
    (degree_sum_normalizedFactors f.val f.property.1).trans f.property.2⟩
  invFun s := ⟨s.val.prod,
    by simpa using Polynomial.monic_multiset_prod_of_monic s.val id (fun f hf => (s.property.1 f hf).1),
    (Polynomial.natDegree_multiset_prod_of_monic _
      (fun f hf => (s.property.1 f hf).1)).trans s.property.2⟩
  left_inv f := Subtype.ext (monic_prod_normalizedFactors f.val f.property.1)
  right_inv s := Subtype.ext (normalizedFactors_prod_monic_irreducible s.val s.property.1)

noncomputable instance factorizationDegreeFintype (K : Type*) [Field K] [DecidableEq K]
    [Fintype K] (n : ℕ) : Fintype (FactorizationDegree K n) :=
  Fintype.ofEquiv (MonicDegree K n) (monicFactorizationEquiv K n)

/-- Multiplicativity retains every repeated irreducible factor. -/
theorem character_normalizedFactors (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f : (ZMod p)[X]) (hf : f.Monic) :
    polynomialCharacter p a b m f =
      ((normalizedFactors f).map (polynomialCharacter p a b m)).prod := by
  calc
    polynomialCharacter p a b m f =
        polynomialCharacterHom p a b m (normalizedFactors f).prod := by
      rw [monic_prod_normalizedFactors f hf]; rfl
    _ = _ := map_multiset_prod (polynomialCharacterHom p a b m) _

/-- The actual coefficient sum, reindexed by unique irreducible
factorization. This is the finite combinatorial expansion underlying the
Euler product; the power-series product identity is a separate theorem. -/
theorem degreeCoefficient_eq_factorization_sum (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) :
    degreeCoefficient p a b m n =
      ∑ s : FactorizationDegree (ZMod p) n,
        (s.val.map (polynomialCharacter p a b m)).prod := by
  classical
  unfold degreeCoefficient
  apply Fintype.sum_equiv (monicFactorizationEquiv (ZMod p) n)
  intro f
  exact character_normalizedFactors p a b m f.val f.property.1

end NField.Alignment.KloostermanMonicFactorization
