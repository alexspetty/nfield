/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExponentialPrecisionFactor

/-! The printed precision quadratic form is the actual exponential inverse. -/

namespace NField.Alignment.ExponentialDistanceKernel

open scoped BigOperators
open Matrix

noncomputable def precision {n : ℕ} (r : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (difference r)ᵀ * diagonal (fun i => (innovation r i)⁻¹) * difference r

theorem precision_quadratic {n : ℕ} (r : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    v ⬝ᵥ (precision r *ᵥ v) =
      v 0 ^ 2 + ∑ i : Fin n, (v i.succ - r i * v i.castSucc) ^ 2 / (1 - r i ^ 2) := by
  rw [precision, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal, Pi.mul_apply]
  rw [Fin.sum_univ_succ]
  simp only [difference_mulVec_zero, difference_mulVec_succ, innovation, Fin.cases_zero,
    Fin.cases_succ, inv_one, one_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Title: `The printed precision matrix is a left inverse`. -/
theorem precision_mul_kernel {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) :
    precision (adjacentRatio x τ) * kernel x τ = 1 := by
  let r := adjacentRatio x τ
  have hd : ∀ i, innovation r i ≠ 0 := fun i =>
    ne_of_gt (innovation_pos (adjacentRatio_bounds x hx hτ) i)
  have hdinv : diagonal (fun i => (innovation r i)⁻¹) * diagonal (innovation r) = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    simp [hd]
  have hb : IsUnit (difference r)ᵀ := by
    rw [Matrix.isUnit_transpose]
    exact difference_isUnit r
  letI := hb.invertible
  have hh := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
    (difference r)ᵀ * diagonal (fun i => (innovation r i)⁻¹) * M)
      (difference_covariance x τ hx.monotone)
  change (difference r)ᵀ * diagonal (fun i => (innovation r i)⁻¹) *
      (difference r * kernel x τ * (difference r)ᵀ) =
    (difference r)ᵀ * diagonal (fun i => (innovation r i)⁻¹) * diagonal (innovation r) at hh
  have hright : precision r * kernel x τ * (difference r)ᵀ = (difference r)ᵀ := by
    simpa only [precision, mul_assoc, hdinv, mul_one] using hh
  have := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
    M * ((difference r)ᵀ)⁻¹) hright
  simpa only [Matrix.mul_inv_cancel_right_of_invertible, Matrix.mul_inv_of_invertible] using this

/-- Title: `The precision matrix is the actual inverse`. -/
theorem kernel_inverse {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) :
    (kernel x τ)⁻¹ = precision (adjacentRatio x τ) := by
  letI := (kernel_posDef x hx hτ).isUnit.invertible
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M * (kernel x τ)⁻¹)
    (precision_mul_kernel x hx hτ)
  simpa using h.symm

/-- Title: `The inverse has the real sum of squares formula`.

The literal inverse has the manuscript's sum-of-squares quadratic form. -/
theorem kernel_inverse_quadratic {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) (v : Fin (n + 1) → ℝ) :
    v ⬝ᵥ ((kernel x τ)⁻¹ *ᵥ v) = v 0 ^ 2 +
      ∑ i : Fin n, (v i.succ - adjacentRatio x τ i * v i.castSucc) ^ 2 /
        (1 - adjacentRatio x τ i ^ 2) := by
  rw [kernel_inverse x hx hτ]
  exact precision_quadratic _ _

theorem precision_apply {n : ℕ} (r : Fin n → ℝ) (i j : Fin (n + 1)) :
    precision r i j = ∑ k, difference r k i * (innovation r k)⁻¹ * difference r k j := by
  simp only [precision, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  simp

theorem difference_support {n : ℕ} (r : Fin n → ℝ) (i j : Fin (n + 1))
    (hij : difference r i j ≠ 0) : j.val ≤ i.val ∧ i.val ≤ j.val + 1 := by
  induction i using Fin.cases with
  | zero =>
    by_cases hj : j = 0
    · subst j; simp
    · simp [hj] at hij
  | succ i =>
    by_cases hj : j = i.succ
    · subst j; simp
    by_cases hk : j = i.castSucc
    · subst j; simp
    simp [hj, hk] at hij

/-- Title: `The inverse has tridiagonal support`. -/
theorem precision_tridiagonal {n : ℕ} (r : Fin n → ℝ) (i j : Fin (n + 1))
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) : precision r i j = 0 := by
  rw [precision_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hi : difference r k i = 0
  · simp [hi]
  by_cases hj : difference r k j = 0
  · simp [hj]
  obtain ⟨hi₁, hi₂⟩ := difference_support r k i hi
  obtain ⟨hj₁, hj₂⟩ := difference_support r k j hj
  omega

theorem precision_adjacent {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    precision r i.castSucc i.succ = -r i / (1 - r i ^ 2) := by
  rw [precision_apply, Finset.sum_eq_single i.succ]
  · have hne : i.castSucc ≠ i.succ := ne_of_lt Fin.castSucc_lt_succ
    simp [hne, hne.symm, innovation, div_eq_mul_inv]
  · intro k hk hki
    by_cases hi : difference r k i.castSucc = 0
    · simp [hi]
    by_cases hj : difference r k i.succ = 0
    · simp [hj]
    obtain ⟨hi₁, hi₂⟩ := difference_support r k i.castSucc hi
    obtain ⟨hj₁, hj₂⟩ := difference_support r k i.succ hj
    have heq : k = i.succ := by apply Fin.ext; simp only [Fin.val_succ, Fin.val_castSucc] at *; omega
    exact (hki heq).elim
  · simp

/-- Title: `Every adjacent inverse entry is nonzero`. -/
theorem kernel_inverse_adjacent_ne_zero {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) (i : Fin n) :
    (kernel x τ)⁻¹ i.castSucc i.succ ≠ 0 := by
  rw [kernel_inverse x hx hτ, precision_adjacent]
  exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt (adjacentRatio_bounds x hx hτ i).1))
    (ne_of_gt (innovation_pos (adjacentRatio_bounds x hx hτ) i.succ))

end NField.Alignment.ExponentialDistanceKernel
