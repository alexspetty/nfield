/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TridiagonalSimpleSpectrum

/-! The manuscript's literal population-weighted exponential quotient. -/

namespace NField.Alignment.ExponentialSpectralQuotient

open scoped BigOperators
open Matrix ExponentialDistanceKernel TridiagonalSimpleSpectrum

noncomputable def degree {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ) (i : ι) : ℝ :=
  ∑ j, pop j * kernel x τ i j

noncomputable def scale {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ) (i : ι) : ℝ :=
  Real.sqrt (pop i) / Real.sqrt (degree x pop τ i)

noncomputable def quotient {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.sqrt (pop i * pop j) * kernel x τ i j /
    Real.sqrt (degree x pop τ i * degree x pop τ j)

noncomputable def perron {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ) (i : ι) : ℝ :=
  Real.sqrt (pop i * degree x pop τ i)

theorem degree_pos {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ)
    (hp : ∀ i, 0 < pop i) (i : ι) : 0 < degree x pop τ i := by
  classical
  apply Finset.sum_pos'
  · intro j hj
    exact (mul_pos (hp j) (kernel_pos x τ i j)).le
  · exact ⟨i, Finset.mem_univ i, mul_pos (hp i) (kernel_pos x τ i i)⟩

theorem scale_pos {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ)
    (hp : ∀ i, 0 < pop i) (i : ι) : 0 < scale x pop τ i :=
  div_pos (Real.sqrt_pos.mpr (hp i)) (Real.sqrt_pos.mpr (degree_pos x pop τ hp i))

theorem perron_pos {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ)
    (hp : ∀ i, 0 < pop i) (i : ι) : 0 < perron x pop τ i :=
  Real.sqrt_pos.mpr (mul_pos (hp i) (degree_pos x pop τ hp i))

/-- Title: `The literal quotient has the diagonal factorization`. -/
theorem quotient_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) :
    quotient x pop τ = diagonal (scale x pop τ) * kernel x τ * diagonal (scale x pop τ) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, quotient, scale]
  rw [Real.sqrt_mul (hp i).le, Real.sqrt_mul (degree_pos x pop τ hp i).le]
  ring

theorem quotient_pos {ι : Type*} [Fintype ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) (i j : ι) :
    0 < quotient x pop τ i j :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (mul_pos (hp i) (hp j))) (kernel_pos x τ i j))
    (Real.sqrt_pos.mpr (mul_pos (degree_pos x pop τ hp i) (degree_pos x pop τ hp j)))

theorem scale_perron {ι : Type*} [Fintype ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) (i : ι) :
    scale x pop τ i * perron x pop τ i = pop i := by
  rw [scale, perron, Real.sqrt_mul (hp i).le]
  have hd : Real.sqrt (degree x pop τ i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (degree_pos x pop τ hp i))
  field_simp
  nlinarith [Real.sq_sqrt (hp i).le]

theorem scale_degree {ι : Type*} [Fintype ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) (i : ι) :
    scale x pop τ i * degree x pop τ i = perron x pop τ i := by
  rw [scale, perron, Real.sqrt_mul (hp i).le]
  have hd : Real.sqrt (degree x pop τ i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (degree_pos x pop τ hp i))
  field_simp
  rw [Real.sq_sqrt (degree_pos x pop τ hp i).le]

/-- Title: `The printed positive vector has eigenvalue one`.

The printed positive Perron vector has eigenvalue exactly one. -/
theorem quotient_perron {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) :
    quotient x pop τ *ᵥ perron x pop τ = perron x pop τ := by
  rw [quotient_factor x pop τ hp, ← mulVec_mulVec, ← mulVec_mulVec]
  have hscale : diagonal (scale x pop τ) *ᵥ perron x pop τ = pop := by
    ext i
    simpa only [mulVec_diagonal] using scale_perron x pop τ hp i
  rw [hscale]
  ext i
  rw [mulVec_diagonal]
  change scale x pop τ i * (∑ j, kernel x τ i j * pop j) = perron x pop τ i
  simpa only [degree, mul_comm] using scale_degree x pop τ hp i

theorem diagonal_scale_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) :
    IsUnit (diagonal (scale x pop τ)) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  ext i
  have hi := congrFun h i
  simp only [mulVec_diagonal] at hi
  exact (mul_left_cancel₀ (ne_of_gt (scale_pos x pop τ hp i))) hi

/-- Title: `The literal quotient is positive definite`. -/
theorem quotient_posDef {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    (quotient x pop τ).PosDef := by
  rw [quotient_factor x pop τ hp]
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (diagonal_scale_isUnit x pop τ hp)).mpr (kernel_posDef x hx hτ)
  simpa only [star_eq_conjTranspose, diagonal_conjTranspose, star_trivial] using h

/-- Title: `The quotient inverse has the printed diagonal factors`. -/
theorem quotient_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x pop : ι → ℝ) (τ : ℝ) (hp : ∀ i, 0 < pop i) :
    (quotient x pop τ)⁻¹ = diagonal (fun i => (scale x pop τ i)⁻¹) *
      (kernel x τ)⁻¹ * diagonal (fun i => (scale x pop τ i)⁻¹) := by
  rw [quotient_factor x pop τ hp, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hdiag : (diagonal (scale x pop τ))⁻¹ = diagonal (fun i => (scale x pop τ i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    ext i j
    simp [ne_of_gt (scale_pos x pop τ hp _)]
  rw [hdiag, mul_assoc]

/-- Title: `The quotient inverse is tridiagonal`. -/
theorem quotient_inverse_tridiagonal {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    Tridiagonal (quotient x pop τ)⁻¹ := by
  intro i j hij
  rw [quotient_inverse x pop τ hp, Matrix.mul_diagonal, Matrix.diagonal_mul,
    kernel_inverse x hx hτ, precision_tridiagonal _ i j hij]
  ring

/-- Title: `Adjacent quotient inverse entries are nonzero`. -/
theorem quotient_inverse_adjacent {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) (i : Fin n) :
    (quotient x pop τ)⁻¹ i.castSucc i.succ ≠ 0 := by
  rw [quotient_inverse x pop τ hp, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (ne_of_gt (scale_pos x pop τ hp _)))
    (kernel_inverse_adjacent_ne_zero x hx hτ i))
    (inv_ne_zero (ne_of_gt (scale_pos x pop τ hp _)))

/-- Title: `The literal quotient has simple eigenvalues`.

The literal quotient has a simple, strictly positive spectrum. -/
theorem quotient_eigenvalues_injective {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    Function.Injective (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues :=
  posDef_eigenvalues_injective_of_inverse (quotient_posDef x pop hx hp hτ)
    (quotient_inverse_tridiagonal x pop hx hp hτ) (quotient_inverse_adjacent x pop hx hp hτ)

end NField.Alignment.ExponentialSpectralQuotient
