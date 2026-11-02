/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovParameters

/-!
# The optimized one-sided finite-field point bound

The rounded parameters discharge the auxiliary construction. Translation
removes its nonzero-constant-term restriction without changing cardinality
or the nonsquare condition over the algebraic closure.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovSelectedPointBound

open scoped BigOperators
open Polynomial StepanovParameters

/-- The optimized bound before translating away a zero constant term. -/
theorem selected_point_bound_nonzero_constant {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree < Fintype.card K)
    (hodd : Odd (Fintype.card K)) (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (value : K) (points : Finset K)
    (hpoints : ∀ a ∈ points,
      f.eval a = 0 ∨ (f.eval a)^((Fintype.card K-1)/2) = value) :
    (points.card : ℝ) < (Fintype.card K : ℝ)/2 +
      2*f.natDegree*order (Fintype.card K) := by
  have hf : f ≠ 0 := by intro h; simp [h] at hm
  have hd : 2*((Fintype.card K-1)/2)+1 = Fintype.card K := by
    obtain ⟨t, ht⟩ := hodd
    omega
  have hq : 18 ≤ Fintype.card K := by omega
  obtain ⟨hell, _, hellq⟩ := order_bounds (Fintype.card K) hq
  obtain ⟨hJ, _, _⟩ := block_count_bounds (Fintype.card K) f.natDegree
    (order (Fintype.card K)) (by omega) (by omega) hell
  have hR := (coefficient_degree_bounds (Fintype.card K) f.natDegree (by omega)).1
  have hdim := rounded_dimension_inequality (Fintype.card K) f.natDegree hm hmq
  apply rounded_card_bound (Fintype.card K) f.natDegree ((Fintype.card K-1)/2)
    points.card hm hmq hd
  exact StepanovConstraintSpace.card_mul_order_bound f hf (by omega)
    (order (Fintype.card K)) ((Fintype.card K-1)/2)
    (blockCount (Fintype.card K) f.natDegree (order (Fintype.card K)))
    (coefficientDegree (Fintype.card K) f.natDegree) hJ value points hd
    (by omega) hf0 hns hR hdim hpoints

/-- Translation preserves the algebraic-closure nonsquare obstruction. -/
theorem not_isSquare_taylor_map {K : Type*} [Field K]
    (f : K[X]) (t : K)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K)))) :
    ¬ IsSquare ((taylor t f).map (algebraMap K (AlgebraicClosure K))) := by
  intro h
  have h' := h.map (taylorAlgHom (-(algebraMap K (AlgebraicClosure K) t)))
  change IsSquare (taylor (-(algebraMap K (AlgebraicClosure K) t))
    ((taylor t f).map (algebraMap K (AlgebraicClosure K)))) at h'
  apply hns
  simpa only [map_taylor, taylor_taylor, neg_add_cancel,
    taylor_zero] using h'

/-- The source one-sided point bound with no constant-term assumption.
It includes roots of f together with the selected power-value class. -/
theorem selected_point_bound {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree < Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (value : K) (points : Finset K)
    (hpoints : ∀ a ∈ points,
      f.eval a = 0 ∨ (f.eval a)^((Fintype.card K-1)/2) = value) :
    (points.card : ℝ) < (Fintype.card K : ℝ)/2 +
      2*f.natDegree*order (Fintype.card K) := by
  classical
  have hf : f ≠ 0 := by intro h; simp [h] at hm
  have hcard : (f.natDegree : Cardinal) < Cardinal.mk K := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast (show f.natDegree < Fintype.card K by omega)
  obtain ⟨t, ht⟩ := f.exists_eval_ne_zero_of_natDegree_lt_card hf hcard
  let shifted := points.image (fun a => a-t)
  have hcount : shifted.card = points.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    simpa only [sub_add_cancel] using congrArg (fun x => x+t) hab
  have hshift : ∀ a ∈ shifted,
      (taylor t f).eval a = 0 ∨ ((taylor t f).eval a)^((Fintype.card K-1)/2) = value := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simpa only [taylor_eval, sub_add_cancel] using hpoints b hb
  have h := selected_point_bound_nonzero_constant (taylor t f)
    (by simpa only [natDegree_taylor] using hm)
    (by simpa only [natDegree_taylor] using hmq) hodd
    (by simpa only [taylor_eval, zero_add] using ht)
    (not_isSquare_taylor_map f t hns) value shifted hshift
  simpa only [hcount, natDegree_taylor] using h

end NField.Alignment.StepanovSelectedPointBound
