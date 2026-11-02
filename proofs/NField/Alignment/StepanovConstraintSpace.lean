/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovAuxiliaryBound
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Nonzero solutions of Stepanov's homogeneous constraints

The domain consists of two finite families of bounded-degree polynomials.
Each derivative constraint is represented by exactly the coefficients allowed
by its degree bound. A strict dimension inequality yields a nonzero solution.
Choosing the numerical parameters for the final point-count estimate is a
separate step.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovConstraintSpace

open scoped BigOperators
open Polynomial HasseDerivativeFactor StepanovAuxiliaryDegree

/-- Extend a finite bounded-degree family by zero. -/
noncomputable def extend {K : Type*} [Field K] {J R : ℕ}
    (v : Fin J → degreeLT K (R+1)) (j : ℕ) : K[X] :=
  if h : j < J then (v ⟨j,h⟩ : K[X]) else 0

theorem extend_add {K : Type*} [Field K] {J R : ℕ}
    (v w : Fin J → degreeLT K (R+1)) (j : ℕ) :
    extend (v+w) j = extend v j + extend w j := by
  unfold extend
  split_ifs <;> simp

theorem extend_smul {K : Type*} [Field K] {J R : ℕ}
    (c : K) (v : Fin J → degreeLT K (R+1)) (j : ℕ) :
    extend (c • v) j = c • extend v j := by
  unfold extend
  split_ifs <;> simp

theorem extend_natDegree_le {K : Type*} [Field K] {J R : ℕ}
    (v : Fin J → degreeLT K (R+1)) (j : ℕ) : (extend v j).natDegree ≤ R := by
  unfold extend
  split_ifs with h
  · apply natDegree_le_of_degree_le
    apply mem_degreeLE.mp
    rw [← degreeLT_succ_eq_degreeLE]
    exact (v ⟨j,h⟩).property
  · simp

/-- A derivative-constraint polynomial depends linearly on both families. -/
noncomputable def constraintMap {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (ell d J R k : ℕ) (value : K) :
    ((Fin J → degreeLT K (R+1)) × (Fin J → degreeLT K (R+1))) →ₗ[K] K[X] where
  toFun v := constraint f hf (extend v.1) (extend v.2) ell d J k value
  map_add' v w := by
    simp only [constraint, Prod.fst_add, Prod.snd_add, extend_add, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' c v := by
    change constraint f hf (extend (c • v.1)) (extend (c • v.2)) ell d J k value =
      c • constraint f hf (extend v.1) (extend v.2) ell d J k value
    simp only [constraint, extend_smul, map_smul,
      mul_smul_comm, ← smul_add, smul_mul_assoc, Finset.smul_sum]

/-- Scalar equations for the low-degree coefficients of every constraint. -/
noncomputable def equationMap {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (ell d J R : ℕ) (value : K) :
    ((Fin J → degreeLT K (R+1)) × (Fin J → degreeLT K (R+1))) →ₗ[K]
      ((k : Fin ell) → Fin (R+J+k.val*(f.natDegree-1)) → K) :=
  LinearMap.pi fun k => LinearMap.pi fun i =>
    (lcoeff K i.val).comp (constraintMap f hf ell d J R k.val value)

/-- The strict variable-versus-equation count produces a nonzero family
satisfying all polynomial constraints, with no solvability assumption. -/
theorem exists_nonzero_constraint_solution {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (ell d J R : ℕ) (hJ : 0 < J) (value : K)
    (hdim : (∑ k : Fin ell, (R+J+k.val*(f.natDegree-1))) < 2*J*(R+1)) :
    ∃ r s : ℕ → K[X],
      (∀ j < J, (r j).natDegree ≤ R) ∧
      (∀ j < J, (s j).natDegree ≤ R) ∧
      (∃ j < J, r j ≠ 0 ∨ s j ≠ 0) ∧
      ∀ k < ell, constraint f hf r s ell d J k value = 0 := by
  classical
  let L := equationMap f hf ell d J R value
  have hdegree_rank (n : ℕ) : Module.finrank K (degreeLT K n) = n := by
    rw [(degreeLTEquiv K n).finrank_eq, Module.finrank_pi, Fintype.card_fin]
  have hdom : Module.finrank K
      ((Fin J → degreeLT K (R+1)) × (Fin J → degreeLT K (R+1))) = 2*J*(R+1) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, hdegree_rank,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    ring
  have hcod : Module.finrank K
      ((k : Fin ell) → Fin (R+J+k.val*(f.natDegree-1)) → K) =
      ∑ k : Fin ell, (R+J+k.val*(f.natDegree-1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_fin]
  have hnotinj : ¬ Function.Injective L := by
    intro h
    have hle := L.finrank_le_finrank_of_injective h
    rw [hdom, hcod] at hle
    omega
  have hex : ∃ v, L v = 0 ∧ v ≠ 0 := by
    by_contra! h
    apply hnotinj
    exact (injective_iff_map_eq_zero L).mpr h
  obtain ⟨v, hv, hv0⟩ := hex
  refine ⟨extend v.1, extend v.2, fun j _ => extend_natDegree_le _ j,
    fun j _ => extend_natDegree_le _ j, ?_, ?_⟩
  · by_contra! h
    apply hv0
    apply Prod.ext
    · funext j
      apply Subtype.ext
      simpa [extend, j.isLt] using (h j.val j.isLt).1
    · funext j
      apply Subtype.ext
      simpa [extend, j.isLt] using (h j.val j.isLt).2
  · intro k hk
    have hbound := constraint_natDegree_le f hf hdeg (extend v.1) (extend v.2)
      ell d J k R value hk.le (fun j _ => extend_natDegree_le _ j)
      (fun j _ => extend_natDegree_le _ j)
    ext i
    rw [coeff_zero]
    by_cases hi : i < R+J+k*(f.natDegree-1)
    · exact congrFun (congrFun hv ⟨k,hk⟩) ⟨i,hi⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Exact count of scalar constraint coefficients, retaining the triangular
sum rather than replacing it by a larger uniform bound. -/
theorem equation_count (ell R J m : ℕ) :
    (∑ k : Fin ell, (R+J+k.val*(m-1))) =
      ell*(R+J) + (ell*(ell-1)/2)*(m-1) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => R+J+k*(m-1)) ell]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_id, ← Finset.sum_mul, Finset.sum_range_id]
  ring

/-- The root bound now follows from a numerical dimension inequality.
No coefficient-existence, constraint-solvability or auxiliary-nonvanishing
hypothesis remains. Parameter optimization is still required for the final
point-count theorem. -/
theorem card_mul_order_bound {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (ell d J R : ℕ) (hJ : 0 < J) (value : K) (points : Finset K)
    (hd : 2*d+1 = Fintype.card K) (hell : ell ≤ Fintype.card K)
    (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hR : 2*R + f.natDegree < Fintype.card K)
    (hdim : (∑ k : Fin ell, (R+J+k.val*(f.natDegree-1))) < 2*J*(R+1))
    (hpoints : ∀ a ∈ points, f.eval a = 0 ∨ (f.eval a)^d = value) :
    points.card * ell ≤ R + (ell+d)*f.natDegree + (J-1)*Fintype.card K := by
  obtain ⟨r, s, hr, hs, hne, hc⟩ :=
    exists_nonzero_constraint_solution f hf hdeg ell d J R hJ value hdim
  exact StepanovAuxiliaryBound.card_mul_order_le_of_constraints
    f hf r s ell d J R value points hd hell hf0 hns hR hr hs hne hc hpoints

end NField.Alignment.StepanovConstraintSpace
