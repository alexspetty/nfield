/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HasseDerivativeFactor
import NField.Alignment.HasseFiniteField
import NField.Alignment.HasseRootCount

/-!
# Stepanov's auxiliary polynomial: derivative constraints and root bound

The polynomial has the two coefficient families used in the elementary
point-count argument. These results translate explicit quotient constraints
into multiplicity and a degree bound on the number of selected points.
The existence of nonzero coefficient families satisfying the constraints,
and nonvanishing of the resulting polynomial, remain to be proved.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovAuxiliary

open scoped BigOperators
open Polynomial HasseDerivativeFactor HasseFiniteField HasseRootCount

/-- The auxiliary polynomial, with q-th powers in the outer monomials. -/
noncomputable def auxiliary {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (r s : ℕ → K[X]) (ell d J : ℕ) : K[X] :=
  ∑ j ∈ Finset.range J,
    (r j * f ^ ell + s j * f ^ (ell + d)) * X ^ (j * Fintype.card K)

/-- Low-order Hasse derivatives at field points have a common factor.
This is the exact constraint formula before specializing f(a)^d. -/
theorem auxiliary_hasse_eval {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : f ≠ 0) (r s : ℕ → K[X]) (ell d J : ℕ)
    (a : K) {k : ℕ} (hk : k ≤ ell) (hkq : k < Fintype.card K) :
    (hasseDeriv k (auxiliary f r s ell d J)).eval a =
      (f.eval a) ^ (ell-k) * ∑ j ∈ Finset.range J,
        ((quotientMap f hf ell k (r j)).eval a +
          (quotientMap f hf (ell+d) k (s j)).eval a * (f.eval a)^d) * a^j := by
  unfold auxiliary
  rw [map_sum, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hasse_mul_X_pow_mul_card_eval _ a j hkq, map_add, eval_add,
    hasse_mul_pow_factor f hf (r j) ell k,
    hasse_mul_pow_factor f hf (s j) (ell+d) k]
  simp only [eval_mul, eval_pow]
  rw [show ell + d - k = ell - k + d by omega, pow_add]
  ring

/-- Vanishing quotient constraints give the root-count bound. No existence
or nonzero conclusion is hidden in this implication. -/
theorem card_mul_order_le_auxiliary_degree {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : f ≠ 0) (r s : ℕ → K[X]) (ell d J n : ℕ)
    (hn : n ≤ ell + 1) (hnq : n ≤ Fintype.card K) (points : Finset K)
    (haux : auxiliary f r s ell d J ≠ 0)
    (hconstraints : ∀ a ∈ points, ∀ k < n,
      (∑ j ∈ Finset.range J,
        ((quotientMap f hf ell k (r j)).eval a +
          (quotientMap f hf (ell+d) k (s j)).eval a * (f.eval a)^d) * a^j) = 0) :
    points.card * n ≤ (auxiliary f r s ell d J).natDegree := by
  apply card_mul_order_le_natDegree _ haux
  intro a ha k hk
  rw [auxiliary_hasse_eval f hf r s ell d J a (by omega) (by omega),
    hconstraints a ha k hk, mul_zero]

end NField.Alignment.StepanovAuxiliary
