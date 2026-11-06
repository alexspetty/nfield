/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExponentialPrecisionInverse
import Mathlib.Algebra.BigOperators.Intervals

/-! The product identity and the complex Hermitian quadratic form printed in the proof. -/

namespace NField.Alignment.ExponentialDistanceKernel

open scoped BigOperators ComplexConjugate
open Matrix

/-- Title: `Kernel entries are products of adjacent ratios`. -/
theorem kernel_interval_product (x : ℕ → ℝ) (τ : ℝ) {i j : ℕ}
    (hij : i ≤ j) (hx : x i ≤ x j) :
    kernel x τ i j = ∏ k ∈ Finset.Ico i j, Real.exp (-(x (k + 1) - x k) / τ) := by
  rw [← Real.exp_sum]
  unfold kernel
  congr 1
  have hsum : (∑ k ∈ Finset.Ico i j, (x (k + 1) - x k)) = x j - x i :=
    Finset.sum_Ico_sub (f := x) hij
  rw [abs_of_nonpos (sub_nonpos.mpr hx), ← Finset.sum_div, Finset.sum_neg_distrib, hsum]
  ring

theorem complex_difference_mulVec_zero {n : ℕ} (r : Fin n → ℝ)
    (v : Fin (n + 1) → ℂ) :
    ((difference r).map (algebraMap ℝ ℂ) *ᵥ v) 0 = v 0 := by
  simp [mulVec, dotProduct, Matrix.map_apply, difference_zero, apply_ite]

theorem complex_difference_mulVec_succ {n : ℕ} (r : Fin n → ℝ)
    (v : Fin (n + 1) → ℂ) (i : Fin n) :
    ((difference r).map (algebraMap ℝ ℂ) *ᵥ v) i.succ =
      v i.succ - (r i : ℂ) * v i.castSucc := by
  have hc (j : Fin (n + 1)) : (algebraMap ℝ ℂ) (difference r i.succ j) =
      (if j = i.succ then 1 else 0) - (r i : ℂ) * (if j = i.castSucc then 1 else 0) := by
    have hne : i.castSucc ≠ i.succ := ne_of_lt Fin.castSucc_lt_succ
    by_cases hs : j = i.succ <;> by_cases ht : j = i.castSucc <;> simp [hs, ht, hne, hne.symm]
  simp only [mulVec, dotProduct, Matrix.map_apply, hc, sub_mul, Finset.sum_sub_distrib]
  simp

theorem complex_precision_factor {n : ℕ} (r : Fin n → ℝ) :
    (precision r).map (algebraMap ℝ ℂ) =
      ((difference r).map (algebraMap ℝ ℂ))ᴴ *
        diagonal (fun i => ((innovation r i : ℝ) : ℂ)⁻¹) *
          (difference r).map (algebraMap ℝ ℂ) := by
  rw [precision, Matrix.map_mul, Matrix.map_mul]
  congr 2
  · ext i j
    simp [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  · ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.map_apply, Matrix.diagonal_apply, hij]

theorem precision_complex_quadratic {n : ℕ} (r : Fin n → ℝ) (v : Fin (n + 1) → ℂ) :
    star v ⬝ᵥ ((precision r).map (algebraMap ℝ ℂ) *ᵥ v) =
      ((‖v 0‖ ^ 2 + ∑ i : Fin n,
        ‖v i.succ - (r i : ℂ) * v i.castSucc‖ ^ 2 / (1 - r i ^ 2) : ℝ) : ℂ) := by
  rw [complex_precision_factor, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  have hnorm (z : ℂ) (a : ℝ) : star z * ((a : ℂ)⁻¹ * z) = ((‖z‖ ^ 2 / a : ℝ) : ℂ) := by
    rw [Complex.sq_norm, Complex.ofReal_div, Complex.normSq_eq_conj_mul_self]
    change star z * ((a : ℂ)⁻¹ * z) = (star z * z) / (a : ℂ)
    ring
  simp only [hnorm]
  rw [Fin.sum_univ_succ]
  simp only [complex_difference_mulVec_zero, complex_difference_mulVec_succ, innovation,
    Fin.cases_zero, Fin.cases_succ, div_one, Complex.ofReal_add, Complex.ofReal_sum]

/-- Title: `The inverse has the Hermitian sum of squares formula`. -/
theorem kernel_inverse_complex_quadratic {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) (v : Fin (n + 1) → ℂ) :
    star v ⬝ᵥ (((kernel x τ)⁻¹).map (algebraMap ℝ ℂ) *ᵥ v) =
      ((‖v 0‖ ^ 2 + ∑ i : Fin n,
        ‖v i.succ - (adjacentRatio x τ i : ℂ) * v i.castSucc‖ ^ 2 /
          (1 - adjacentRatio x τ i ^ 2) : ℝ) : ℂ) := by
  rw [kernel_inverse x hx hτ]
  exact precision_complex_quadratic _ _

end NField.Alignment.ExponentialDistanceKernel
