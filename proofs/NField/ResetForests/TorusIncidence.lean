/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrimitiveCoordinates
/-! # The literal incidence factorization of the full continuous Gram -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators Matrix
open NField.Alignment SourceMetrics

theorem cutoff_divisor_set {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (Finset.Icc 1 N).filter (fun d => d ∣ n)=n.divisors := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_,hd⟩
    exact ⟨hd,hn.ne'⟩
  · rintro ⟨hd,_⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnN⟩,hd⟩

def divisorIncidence (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i d => if d.val+1 ∣ i.val+1 then 1 else 0

def harmonicDiagonal (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => ((i.val+1 : ℕ) : ℝ))

def jordanDiagonal (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun d => jordanMass (d.val+1))

theorem harmonic_diagonal_inverse (N : ℕ) :
    (harmonicDiagonal N)⁻¹=
      Matrix.diagonal (fun i : Fin N => (((i.val+1 : ℕ) : ℝ))⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [harmonicDiagonal, Matrix.diagonal_mul_diagonal]
  have he : (fun i : Fin N => (((i.val+1 : ℕ) : ℝ))⁻¹*((i.val+1 : ℕ) : ℝ))=
      fun _ => (1 : ℝ) := by
    funext i
    exact inv_mul_cancel₀ (by positivity)
  rw [he, Matrix.diagonal_one]

theorem finite_jordan_incidence (N : ℕ) (i j : Fin N) :
    (∑ d : Fin N, divisorIncidence N i d*jordanMass (d.val+1)*
      divisorIncidence N j d)=(Nat.gcd (i.val+1) (j.val+1) : ℝ)^2 := by
  unfold divisorIncidence
  rw [← sum_source_indices N (fun d =>
    (if d ∣ i.val+1 then (1 : ℝ) else 0)*jordanMass d*
      (if d ∣ j.val+1 then (1 : ℝ) else 0))]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N,
        if d ∣ j.val+1 then (if d ∣ i.val+1 then jordanMass d else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hi : d ∣ i.val+1 <;> by_cases hj : d ∣ j.val+1 <;> simp [hi,hj]
    _ = ∑ d ∈ (j.val+1).divisors, if d ∣ i.val+1 then jordanMass d else 0 := by
      rw [← Finset.sum_filter, cutoff_divisor_set (Nat.succ_pos j.val) (by omega : j.val+1 ≤ N)]
    _ = _ := gcd_jordan_divisor_sum (Nat.succ_pos i.val) (Nat.succ_pos j.val)

theorem continuous_incidence_factorization (N : ℕ) :
    continuousGram N=(1/3 : ℝ) •
      ((harmonicDiagonal N)⁻¹*divisorIncidence N*jordanDiagonal N*
        (divisorIncidence N)ᵀ*(harmonicDiagonal N)⁻¹) := by
  ext i j
  rw [harmonic_diagonal_inverse]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal]
  rw [Matrix.mul_apply]
  simp only [jordanDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have he : (∑ d : Fin N,
      (((i.val+1 : ℕ) : ℝ))⁻¹*divisorIncidence N i d*jordanMass (d.val+1)*
        divisorIncidence N j d)=
      (((i.val+1 : ℕ) : ℝ))⁻¹*(Nat.gcd (i.val+1) (j.val+1) : ℝ)^2 := by
    rw [← finite_jordan_incidence N i j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  simp only [continuousGram, div_eq_mul_inv, mul_inv_rev]
  ring

theorem inverse_diagonal_incidence_coordinates (N : ℕ) (c : Fin N → ℝ) (d : Fin N) :
    ((divisorIncidence N)ᵀ *ᵥ ((harmonicDiagonal N)⁻¹ *ᵥ c)) d=
      divisorCoordinate N (cutoffCoefficients N c) (d.val+1) := by
  have hdiag : (harmonicDiagonal N)⁻¹ *ᵥ c=
      fun h => (((h.val+1 : ℕ) : ℝ))⁻¹*c h := by
    funext h
    rw [harmonic_diagonal_inverse, Matrix.mulVec_diagonal]
  rw [hdiag]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, divisorIncidence,
    divisorCoordinate, sum_source_indices, cutoff_coefficients_succ]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : d.val+1 ∣ h.val+1 <;> simp [hd, div_eq_mul_inv, mul_comm]

end NField.ResetForests.PrimitiveCoordinates
