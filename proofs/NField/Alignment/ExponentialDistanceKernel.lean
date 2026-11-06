/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! The literal exponential distance kernel and its adjacent-label identities. -/

namespace NField.Alignment.ExponentialDistanceKernel

open scoped BigOperators

noncomputable def kernel {ι : Type*} (x : ι → ℝ) (τ : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (-|x i - x j| / τ)

@[simp] theorem kernel_diag {ι : Type*} (x : ι → ℝ) (τ : ℝ) (i : ι) :
    kernel x τ i i = 1 := by simp [kernel]

theorem kernel_pos {ι : Type*} (x : ι → ℝ) (τ : ℝ) (i j : ι) :
    0 < kernel x τ i j := Real.exp_pos _

theorem kernel_symm {ι : Type*} (x : ι → ℝ) (τ : ℝ) (i j : ι) :
    kernel x τ i j = kernel x τ j i := by simp [kernel, abs_sub_comm]

theorem kernel_isHermitian {ι : Type*} (x : ι → ℝ) (τ : ℝ) :
    (kernel x τ).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, kernel_symm]

/-- Title: `Exponential distances multiply along ordered labels`. -/
theorem kernel_chain {ι : Type*} (x : ι → ℝ) (τ : ℝ) {i j k : ι}
    (hij : x i ≤ x j) (hjk : x j ≤ x k) :
    kernel x τ i j * kernel x τ j k = kernel x τ i k := by
  rw [kernel, kernel, kernel, ← Real.exp_add]
  congr 1
  rw [abs_of_nonpos (sub_nonpos.mpr hij), abs_of_nonpos (sub_nonpos.mpr hjk),
    abs_of_nonpos (sub_nonpos.mpr (hij.trans hjk))]
  ring

noncomputable def adjacentRatio {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (i : Fin n) : ℝ := kernel x τ i.castSucc i.succ

/-- Title: `Adjacent ratios have the printed exponential formula`. -/
theorem adjacentRatio_formula {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (hx : StrictMono x) (i : Fin n) :
    adjacentRatio x τ i = Real.exp (-(x i.succ - x i.castSucc) / τ) := by
  have hi : i.castSucc < i.succ := Fin.castSucc_lt_succ (i := i)
  simp only [adjacentRatio, kernel, abs_of_neg (sub_neg.mpr (hx hi))]
  congr 1
  ring

/-- Title: `Adjacent ratios lie strictly between zero and one`. -/
theorem adjacentRatio_bounds {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) (i : Fin n) :
    0 < adjacentRatio x τ i ∧ adjacentRatio x τ i < 1 := by
  refine ⟨kernel_pos _ _ _ _, ?_⟩
  rw [adjacentRatio_formula x τ hx, Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr (hx (Fin.castSucc_lt_succ (i := i))))) hτ

theorem adjacent_left {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (hx : Monotone x) (i : Fin n) (j : Fin (n + 1)) (hji : j ≤ i.castSucc) :
    kernel x τ i.succ j = adjacentRatio x τ i * kernel x τ i.castSucc j := by
  have h := kernel_chain x τ (hx hji) (hx (Fin.castSucc_lt_succ (i := i)).le)
  rw [kernel_symm x τ j i.castSucc, kernel_symm x τ j i.succ] at h
  exact h.symm.trans (mul_comm _ _)

theorem adjacent_right {n : ℕ} (x : Fin (n + 1) → ℝ) (τ : ℝ)
    (hx : Monotone x) (i : Fin n) (j : Fin (n + 1)) (hij : i.succ ≤ j) :
    kernel x τ i.castSucc j = adjacentRatio x τ i * kernel x τ i.succ j := by
  exact (kernel_chain x τ (hx (Fin.castSucc_lt_succ (i := i)).le) (hx hij)).symm

end NField.Alignment.ExponentialDistanceKernel
