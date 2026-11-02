/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Low Hasse derivatives of finite-field powers

At points of a finite field of cardinality q, powers h^q contribute only
their order-zero term to Hasse derivatives of order less than q. These
identities justify the X^(j*q) factors in Stepanov's auxiliary polynomial.
They are not a point-count estimate or an existence proof for that polynomial.
-/

set_option autoImplicit false
namespace NField.Alignment.HasseFiniteField

open scoped BigOperators
open Polynomial

/-- Positive Hasse derivatives below q vanish at every field point on a
q-th power. Taylor coefficients avoid any factorial division. -/
theorem hasse_pow_card_eval_eq_zero {K : Type*} [Field K] [Fintype K]
    (h : K[X]) (a : K) {k : ℕ} (hk : 0 < k) (hkq : k < Fintype.card K) :
    (hasseDeriv k (h ^ Fintype.card K)).eval a = 0 := by
  rw [← taylor_coeff, taylor_pow, ← FiniteField.expand_card]
  rw [coeff_expand (Fintype.card_pos : 0 < Fintype.card K), if_neg]
  exact fun hd => (Nat.le_of_dvd hk hd).not_gt hkq

/-- Below the field cardinality, a q-th-power factor may be treated as a
constant when evaluating the Hasse derivative at a field point. -/
theorem hasse_mul_pow_card_eval {K : Type*} [Field K] [Fintype K]
    (g h : K[X]) (a : K) {k : ℕ} (hkq : k < Fintype.card K) :
    (hasseDeriv k (g * h ^ Fintype.card K)).eval a =
      (hasseDeriv k g).eval a * h.eval a := by
  rw [hasseDeriv_mul, eval_finsetSum]
  rw [Finset.sum_eq_single (k, 0)]
  · simp [FiniteField.pow_card]
  · intro ij hij hne
    have hij' := Finset.mem_antidiagonal.mp hij
    have hj : 0 < ij.2 := by
      by_contra! hz
      have heq : ij = (k, 0) := Prod.ext (by omega) (by omega)
      exact hne heq
    rw [eval_mul, hasse_pow_card_eval_eq_zero h a hj (by omega), mul_zero]
  · simp

/-- The monomial version used in the auxiliary-polynomial sum. -/
theorem hasse_mul_X_pow_mul_card_eval {K : Type*} [Field K] [Fintype K]
    (g : K[X]) (a : K) (j : ℕ) {k : ℕ} (hkq : k < Fintype.card K) :
    (hasseDeriv k (g * X ^ (j * Fintype.card K))).eval a =
      (hasseDeriv k g).eval a * a ^ j := by
  simpa only [pow_mul, eval_pow, eval_X] using
    hasse_mul_pow_card_eval g (X ^ j) a hkq

end NField.Alignment.HasseFiniteField
