/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExponentialDistanceKernel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Adjacent differences diagonalize the actual exponential covariance. -/

namespace NField.Alignment.ExponentialDistanceKernel

open scoped BigOperators
open Matrix

noncomputable def difference {n : ℕ} (r : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.cases (Pi.single 0 1)
    (fun i => Pi.single i.succ 1 - r i • Pi.single i.castSucc 1)

noncomputable def innovation {n : ℕ} (r : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 1 (fun i => 1 - r i ^ 2)

@[simp] theorem difference_zero {n : ℕ} (r : Fin n → ℝ) (j : Fin (n + 1)) :
    difference r 0 j = if j = 0 then 1 else 0 := by
  simp [difference, Pi.single_apply, eq_comm]

@[simp] theorem difference_succ {n : ℕ} (r : Fin n → ℝ) (i : Fin n)
    (j : Fin (n + 1)) :
    difference r i.succ j = (if j = i.succ then 1 else 0) -
      r i * (if j = i.castSucc then 1 else 0) := by
  simp [difference, Pi.single_apply, eq_comm]

@[simp] theorem difference_mul_zero {n : ℕ} (r : Fin n → ℝ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    (difference r * M) 0 j = M 0 j := by
  simp [Matrix.mul_apply]

@[simp] theorem difference_mul_succ {n : ℕ} (r : Fin n → ℝ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n) (j : Fin (n + 1)) :
    (difference r * M) i.succ j = M i.succ j - r i * M i.castSucc j := by
  simp [Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]

@[simp] theorem mul_difference_transpose_zero {n : ℕ} (r : Fin n → ℝ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    (M * (difference r)ᵀ) i 0 = M i 0 := by
  simp [Matrix.mul_apply, Matrix.transpose_apply]

@[simp] theorem mul_difference_transpose_succ {n : ℕ} (r : Fin n → ℝ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) (j : Fin n) :
    (M * (difference r)ᵀ) i j.succ = M i j.succ - r j * M i j.castSucc := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, mul_sub, Finset.sum_sub_distrib,
    mul_comm, mul_left_comm, ← Finset.mul_sum]

@[simp] theorem difference_mulVec_zero {n : ℕ} (r : Fin n → ℝ)
    (v : Fin (n + 1) → ℝ) :
    (difference r *ᵥ v) 0 = v 0 := by simp [mulVec, dotProduct]

@[simp] theorem difference_mulVec_succ {n : ℕ} (r : Fin n → ℝ)
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    (difference r *ᵥ v) i.succ = v i.succ - r i * v i.castSucc := by
  simp [mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]

theorem difference_injective {n : ℕ} (r : Fin n → ℝ) :
    Function.Injective (difference r).mulVec := by
  intro v w h
  funext i
  induction i using Fin.induction with
  | zero => simpa using congrFun h 0
  | succ i ih =>
    have hi := congrFun h i.succ
    simpa [ih] using hi

theorem difference_isUnit {n : ℕ} (r : Fin n → ℝ) : IsUnit (difference r) :=
  Matrix.mulVec_injective_iff_isUnit.mp (difference_injective r)

theorem difference_kernel_below {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (hx : Monotone x) (i : Fin n) (j : Fin (n + 1)) (hji : j ≤ i.castSucc) :
    (difference (adjacentRatio x τ) * kernel x τ) i.succ j = 0 := by
  rw [difference_mul_succ, adjacent_left x τ hx i j hji, sub_self]

theorem difference_kernel_above {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (hx : Monotone x) (i : Fin n) (j : Fin (n + 1)) (hij : i.succ ≤ j) :
    (difference (adjacentRatio x τ) * kernel x τ) i.succ j =
      (1 - adjacentRatio x τ i ^ 2) * kernel x τ i.succ j := by
  rw [difference_mul_succ, adjacent_right x τ hx i j hij]
  ring

theorem difference_covariance {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (hx : Monotone x) :
    difference (adjacentRatio x τ) * kernel x τ * (difference (adjacentRatio x τ))ᵀ =
      diagonal (innovation (adjacentRatio x τ)) := by
  ext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [innovation]
    | succ j =>
      rw [mul_difference_transpose_succ, difference_mul_zero, difference_mul_zero]
      rw [kernel_symm x τ 0 j.succ, kernel_symm x τ 0 j.castSucc]
      rw [adjacent_left x τ hx j 0 (Fin.zero_le _)]
      simp [Matrix.diagonal_apply, innovation, ne_comm]
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [mul_difference_transpose_zero, difference_kernel_below x τ hx i 0 (Fin.zero_le _)]
      simp [Matrix.diagonal_apply]
    | succ j =>
      rw [mul_difference_transpose_succ]
      rcases lt_trichotomy i j with hij | hij | hij
      · have hs : i.succ ≤ j.castSucc := by exact_mod_cast hij
        have ht : i.succ ≤ j.succ := by simpa using (le_of_lt hij)
        rw [difference_kernel_above x τ hx i j.succ ht,
          difference_kernel_above x τ hx i j.castSucc hs]
        rw [kernel_symm x τ i.succ j.succ, kernel_symm x τ i.succ j.castSucc,
          adjacent_left x τ hx j i.succ hs]
        have hne : i.succ ≠ j.succ := by simpa using ne_of_lt hij
        simp [Matrix.diagonal_apply, hne]
        ring
      · subst j
        rw [difference_kernel_above x τ hx i i.succ le_rfl,
          difference_kernel_below x τ hx i i.castSucc le_rfl]
        simp [innovation]
      · have hs : j.succ ≤ i.castSucc := by exact_mod_cast hij
        have ht : j.castSucc ≤ i.castSucc := Fin.castSucc_le_castSucc_iff.mpr (le_of_lt hij)
        rw [difference_kernel_below x τ hx i j.succ hs,
          difference_kernel_below x τ hx i j.castSucc ht]
        have hne : i.succ ≠ j.succ := by simpa using ne_of_gt hij
        simp [Matrix.diagonal_apply, hne]

theorem innovation_pos {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i ∧ r i < 1)
    (i : Fin (n + 1)) : 0 < innovation r i := by
  induction i using Fin.cases with
  | zero => norm_num [innovation]
  | succ i =>
    obtain ⟨h0, h1⟩ := hr i
    simp only [innovation, Fin.cases_succ]
    nlinarith

/-- Title: `The exponential distance matrix is positive definite`.

Strictly ordered labels give a positive-definite exponential distance matrix. -/
theorem kernel_posDef {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) : (kernel x τ).PosDef := by
  have hd : (diagonal (innovation (adjacentRatio x τ))).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (innovation_pos (adjacentRatio_bounds x hx hτ))
  rw [← difference_covariance x τ hx.monotone] at hd
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (difference_isUnit (adjacentRatio x τ))).mp
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hd

end NField.Alignment.ExponentialDistanceKernel
