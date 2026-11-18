/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EuclideanClocks
import Mathlib.Algebra.Ring.GeomSum
/-! # Nilpotence and the complete finite inverse of the signed clock fold -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.EuclideanFold

open scoped BigOperators

instance foldEndDistribNeg (N : ℕ) : HasDistribNeg (Module.End ℝ (FoldSource N)) where
  neg_neg f := by apply LinearMap.ext; intro x; exact neg_neg (f x)
  neg_mul f g := by rfl
  mul_neg f g := by apply LinearMap.ext; intro x; exact map_neg f (g x)

theorem transport_power_basis_zero (k : ℕ) {N : ℕ} (s : FoldClock N)
    (h : clockDenominator s ≤ k) :
    (clockTransport N ^ k) (clockBasis s) = 0 := by
  induction k generalizing s with
  | zero => have := clock_bounds s; omega
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, transport_basis]
    by_cases hs : Nonterminal s
    · rw [clockImage, dif_pos hs, map_smul]
      have hd := successor_strict_descent s hs
      rw [ih (successorClock s hs) (by omega), smul_zero]
    · rw [clockImage, dif_neg hs, map_zero]

theorem transport_nilpotent (N : ℕ) : clockTransport N ^ N = 0 := by
  apply Finsupp.lhom_ext
  intro s c
  have hs : Finsupp.single s c = c • clockBasis s := by
    simp [clockBasis, Finsupp.smul_single]
  rw [hs, map_smul, transport_power_basis_zero N s (clock_bounds s).2.1]
  simp

def foldInverse (N : ℕ) : Module.End ℝ (FoldSource N) :=
  ∑ j ∈ Finset.range N, (-(clockTransport N)) ^ j

theorem negative_transport_power (N : ℕ) : (-(clockTransport N)) ^ N = 0 := by
  rw [neg_pow (clockTransport N) N, transport_nilpotent, mul_zero]

theorem inverse_fold_right (N : ℕ) :
    foldInverse N * (1 + clockTransport N) = 1 := by
  have h := geom_sum_mul_neg (-(clockTransport N)) N
  rw [sub_neg_eq_add (α := Module.End ℝ (FoldSource N)) 1 (clockTransport N),
    negative_transport_power, sub_zero (1 : Module.End ℝ (FoldSource N))] at h
  exact h

theorem inverse_fold_left (N : ℕ) :
    (1 + clockTransport N) * foldInverse N = 1 := by
  have h := mul_neg_geom_sum (-(clockTransport N)) N
  rw [sub_neg_eq_add (α := Module.End ℝ (FoldSource N)) 1 (clockTransport N),
    negative_transport_power, sub_zero (1 : Module.End ℝ (FoldSource N))] at h
  exact h

def clockFoldEquiv (N : ℕ) : FoldSource N ≃ₗ[ℝ] FoldSource N :=
  { (1 + clockTransport N : Module.End ℝ (FoldSource N)) with
    invFun := foldInverse N
    left_inv := fun x => by
      have h := congrArg (fun f : Module.End ℝ (FoldSource N) => f x) (inverse_fold_right N)
      exact h
    right_inv := fun x => by
      have h := congrArg (fun f : Module.End ℝ (FoldSource N) => f x) (inverse_fold_left N)
      exact h }

theorem fold_equiv_linear_map (N : ℕ) :
    (clockFoldEquiv N).toLinearMap = 1 + clockTransport N := rfl

theorem inverse_equiv_linear_map (N : ℕ) :
    (clockFoldEquiv N).symm.toLinearMap = foldInverse N := by
  ext x
  rfl

theorem inverse_all_internal_depths (N : ℕ) (x : FoldSource N) :
    foldInverse N x =
      ∑ j ∈ Finset.range N, ((-(clockTransport N)) ^ j) x := by
  simp only [foldInverse, LinearMap.sum_apply]

theorem inverse_terminal_basis {N : ℕ} (s : FoldClock N) (hs : ¬Nonterminal s) :
    foldInverse N (clockBasis s) = clockBasis s := by
  have h := congrArg (fun f : Module.End ℝ (FoldSource N) => f (clockBasis s))
    (inverse_fold_right N)
  simpa only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    transport_terminal s hs, add_zero] using h

theorem inverse_basis_recursion {N : ℕ} (s : FoldClock N) (hs : Nonterminal s) :
    foldInverse N (clockBasis s) = clockBasis s -
      clockSign s • foldInverse N (clockBasis (successorClock s hs)) := by
  apply eq_sub_iff_add_eq.mpr
  have h := congrArg (fun f : Module.End ℝ (FoldSource N) => f (clockBasis s))
    (inverse_fold_right N)
  simpa only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    transport_nonterminal s hs, map_add, map_smul] using h

theorem inverse_scalar_reading (N : ℕ) (reading : FoldSource N →ₗ[ℝ] ℝ)
    (x : FoldSource N) :
    reading (foldInverse N x) =
      ∑ j ∈ Finset.range N, reading (((-(clockTransport N)) ^ j) x) := by
  rw [inverse_all_internal_depths]
  simp only [map_sum]

end NField.ResetForests.EuclideanFold
