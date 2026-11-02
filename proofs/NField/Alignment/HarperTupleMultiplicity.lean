/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTuplePolynomial
import NField.Alignment.HarperPrimeEvenMoment

/-!
# Actual prime-product tuple multiplicities

Prime factorization identifies each coordinate of the exponent vector of
an ordered tuple. The generating-polynomial coefficient bound therefore
applies to the actual natural-number product fibers, including repeated
primes and prime-square substitutions. Empty cutoffs and order zero are
included in the finite constructions.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperTupleMultiplicity

open scoped BigOperators
open HarperTuplePolynomial HarperMomentExpansion HarperMomentReduction
  HarperPrimeTaylorComparison CollisionMertensInput

theorem atom_factorization (P : ℝ) (a : Atom P) (p : {p : ℕ // p ∈ primesUpTo P}) :
    (atomIndex P a).factorization p.val = atomExponent a p := by
  classical
  obtain ⟨r, b⟩ := a
  have hr := (primesUpTo_mem.mp r.property).1
  by_cases h : r = p
  · subst r
    cases b <;> simp [atomIndex, atomExponent, hr.factorization, hr.factorization_pow]
  · have hn : r.val ≠ p.val := fun he => h (Subtype.ext he)
    cases b <;> simp [atomIndex, atomExponent, hr.factorization, hr.factorization_pow, h, hn]

/-- Every exponent coordinate is the multiplicity of its prime in the actual integer product. -/
theorem tuple_factorization (P : ℝ) (k : ℕ) (t : Fin k → Atom P)
    (p : {p : ℕ // p ∈ primesUpTo P}) :
    (tupleIndex k (atomIndex P) t).factorization p.val = tupleExponent k t p := by
  unfold tupleIndex tupleExponent
  rw [Nat.factorization_prod_apply (fun j _ => (atomIndex_bounds P (t j)).1.ne')]
  simp only [Finsupp.finsetSum_apply, atom_factorization]

theorem tupleExponent_eq_of_product_eq (P : ℝ) (k : ℕ) (t u : Fin k → Atom P)
    (h : tupleIndex k (atomIndex P) t = tupleIndex k (atomIndex P) u) :
    tupleExponent k t = tupleExponent k u := by
  ext p
  rw [← tuple_factorization, ← tuple_factorization, h]

/-- A fixed product and tuple length fix the number of square atoms, even across different multisets. -/
theorem squareCount_eq_of_product_eq (P : ℝ) (k : ℕ) (t u : Fin k → Atom P)
    (h : tupleIndex k (atomIndex P) t = tupleIndex k (atomIndex P) u) :
    squareCount k t = squareCount k u := by
  have he := congrArg exponentWeight (tupleExponent_eq_of_product_eq P k t u h)
  simp only [tupleExponent_weight] at he
  omega

theorem tupleMultiplicity_le_exponentMultiplicity (P : ℝ) (k : ℕ) (t : Fin k → Atom P) :
    tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) ≤
      exponentMultiplicity k (tupleExponent k t) := by
  classical
  letI : DecidableEq {p : ℕ // p ∈ primesUpTo P} := Classical.decEq _
  unfold tupleMultiplicity exponentMultiplicity
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    tupleExponent_eq_of_product_eq P k u t (Finset.mem_filter.mp hu).2⟩

/-- The actual product-fiber bound, with the stronger factor two per square. -/
theorem tupleMultiplicity_le_factorial_two (P : ℝ) (k : ℕ) (t : Fin k → Atom P) :
    tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) ≤
      k.factorial * 2 ^ squareCount k t :=
  (tupleMultiplicity_le_exponentMultiplicity P k t).trans (tuple_count_le_factorial_two k t)

/-- The precise factor-four bound used in the printed Harper estimate. -/
theorem tupleMultiplicity_le_factorial_four (P : ℝ) (k : ℕ) (t : Fin k → Atom P) :
    tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) ≤
      k.factorial * 4 ^ squareCount k t :=
  (tupleMultiplicity_le_exponentMultiplicity P k t).trans (tuple_count_le_factorial_four k t)

theorem square_weight_product {ι : Type*} (k : ℕ) (t : Fin k → ι × Bool) (c : ℝ) :
    (∏ j, if (t j).2 then c else 1) = c ^ squareCount k t := by
  classical
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, squareCount]

end NField.Alignment.HarperTupleMultiplicity
