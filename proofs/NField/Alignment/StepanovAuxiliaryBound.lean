/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovAuxiliaryDegree
import NField.Alignment.StepanovNonvanishing

/-!
# Stepanov's root bound from polynomial constraints

The auxiliary polynomial is now proved nonzero from its coefficient family.
The remaining existence step is to find a nonzero bounded family satisfying
the displayed homogeneous polynomial constraints. This file does not assume
or conclude a complete point-count or Kloosterman estimate.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovAuxiliaryBound

open scoped BigOperators
open Polynomial HasseDerivativeFactor StepanovAuxiliary
open StepanovAuxiliaryDegree StepanovNonvanishing

/-- Polynomial constraints force the low-order Hasse derivatives to vanish
both at roots of f and at points with the selected power value. -/
theorem auxiliary_hasse_eval_eq_zero_of_constraint {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : f ≠ 0) (r s : ℕ → K[X]) (ell d J : ℕ)
    (value a : K) {k : ℕ} (hk : k < ell) (hkq : k < Fintype.card K)
    (hconstraint : constraint f hf r s ell d J k value = 0)
    (ha : f.eval a = 0 ∨ (f.eval a)^d = value) :
    (hasseDeriv k (auxiliary f r s ell d J)).eval a = 0 := by
  rw [auxiliary_hasse_eval f hf r s ell d J a hk.le hkq]
  rcases ha with ha | ha
  · rw [ha, zero_pow (Nat.sub_pos_of_lt hk).ne', zero_mul]
  · have hc := congrArg (Polynomial.eval a) hconstraint
    simp only [constraint, eval_finsetSum, eval_mul, eval_add, eval_C,
      eval_pow, eval_X, eval_zero, mul_comm value] at hc
    simp only [ha]
    rw [hc, mul_zero]

/-- The actual auxiliary degree yields a root-count estimate once a
nonzero coefficient family satisfying the homogeneous constraints is given.
Auxiliary nonvanishing is derived from the source's nonsquare hypothesis. -/
theorem card_mul_order_le_of_constraints {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : f ≠ 0) (r s : ℕ → K[X]) (ell d J R : ℕ)
    (value : K) (points : Finset K)
    (hd : 2*d+1 = Fintype.card K) (hell : ell ≤ Fintype.card K)
    (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hR : 2*R + f.natDegree < Fintype.card K)
    (hr : ∀ j < J, (r j).natDegree ≤ R)
    (hs : ∀ j < J, (s j).natDegree ≤ R)
    (hne : ∃ j < J, r j ≠ 0 ∨ s j ≠ 0)
    (hconstraints : ∀ k < ell, constraint f hf r s ell d J k value = 0)
    (hpoints : ∀ a ∈ points, f.eval a = 0 ∨ (f.eval a)^d = value) :
    points.card * ell ≤ R + (ell+d)*f.natDegree + (J-1)*Fintype.card K := by
  have haux := auxiliary_ne_zero f r s ell d J hd hf0 hns
    (by intro j hj; have := hr j hj; omega)
    (by intro j hj; have := hs j hj; omega) hne
  apply le_trans (HasseRootCount.card_mul_order_le_natDegree
    (auxiliary f r s ell d J) haux points ell ?_)
    (auxiliary_natDegree_le f r s ell d J R hr hs)
  intro a ha k hk
  exact auxiliary_hasse_eval_eq_zero_of_constraint f hf r s ell d J value a hk
    (hk.trans_le hell) (hconstraints k hk) (hpoints a ha)

end NField.Alignment.StepanovAuxiliaryBound
