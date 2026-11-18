/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestBasis
import NField.ResetForests.ResetMasks
/-! # The general mask selects the actual gcd source and full populations -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ResetMasks

open scoped BigOperators Matrix
open NField.Alignment SourceMetrics

def forestMask (N Ω : ℕ) (k : Fin N) : ℝ := if k.val+1 ∣ Ω then 1 else 0

theorem forest_root_eq_iff (N Ω : ℕ) (i j : Fin N) :
    i=forestRoot N Ω j ↔ (j.val+1).gcd Ω=i.val+1 := by
  constructor
  · intro he
    rw [he]
    exact (forest_root_frequency N Ω j).symm
  · intro he
    apply Fin.ext
    have h := forest_root_frequency N Ω j
    omega

theorem collapse_matrix_column (N Ω : ℕ) (j : Fin N) :
    collapseMatrix ℝ N Ω *ᵥ Pi.single j 1=Pi.single (forestRoot N Ω j) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  simp [collapseMatrix, Pi.single_apply]

theorem collapse_matrix_mask (N Ω : ℕ) :
    resetMatrix N*collapseMatrix ℝ N Ω=Matrix.diagonal (forestMask N Ω)*resetMatrix N := by
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  simp only [collapseMatrix, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, resetMatrix, forestMask, forest_root_frequency, Nat.dvd_gcd_iff]
  by_cases hkj : k.val+1 ∣ j.val+1 <;> by_cases hkΩ : k.val+1 ∣ Ω <;> simp [hkj,hkΩ]

theorem saturated_mask_is_collapse (N Ω : ℕ) :
    resetMaskMatrix N (forestMask N Ω)=collapseMatrix ℝ N Ω := by
  exact (reset_mask_unique N (forestMask N Ω) (collapseMatrix ℝ N Ω)
    (collapse_matrix_mask N Ω)).symm

theorem saturated_mask_column (N Ω : ℕ) (j : Fin N) :
    resetMaskMatrix N (forestMask N Ω) *ᵥ Pi.single j 1=
      Pi.single (forestRoot N Ω j) 1 := by
  rw [saturated_mask_is_collapse, collapse_matrix_column]

theorem collapse_matrix_reading (N Ω : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    (collapseMatrix ℝ N Ω *ᵥ c) i=
      Core.collapseSource N Ω (cutoffCoefficients N c) (i.val+1) := by
  simp only [Matrix.mulVec, dotProduct, collapseMatrix, Core.collapseSource,
    Core.sourceIndices, sum_source_indices, cutoff_coefficients_succ]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : i=forestRoot N Ω j
  · have hg := (forest_root_eq_iff N Ω i j).mp he
    simp [he,hg]
  · have hg : (j.val+1).gcd Ω ≠ i.val+1 := (forest_root_eq_iff N Ω i j).not.mp he
    simp [he,hg]

theorem collapse_matrix_mass (N Ω : ℕ) (c : Fin N → ℝ) :
    (∑ i : Fin N, (collapseMatrix ℝ N Ω *ᵥ c) i)=∑ j : Fin N, c j := by
  have h := Core.collapse_total_mass N Ω (cutoffCoefficients N c)
  simp only [Core.sourceIndices] at h
  simp_rw [sum_source_indices, cutoff_coefficients_succ] at h
  simpa only [collapse_matrix_reading] using h

theorem collapse_coherent_reading (N Ω : ℕ) (i : Fin N) :
    (collapseMatrix ℝ N Ω *ᵥ (fun _ => 1)) i=
      Core.collapseSource N Ω (fun _ => 1) (i.val+1) := by
  rw [collapse_matrix_reading]
  simp only [Core.collapseSource, Core.sourceIndices, sum_source_indices, cutoff_coefficients_succ]

def forestPopulation (N Ω : ℕ) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j : Fin N => forestRoot N Ω j=i)).card

theorem collapse_population (N Ω : ℕ) (i : Fin N) :
    (collapseMatrix ℝ N Ω *ᵥ (fun _ => 1)) i=(forestPopulation N Ω i : ℝ) := by
  rw [forestPopulation, PrimitiveCoordinates.real_filter_card]
  simp only [Matrix.mulVec, dotProduct, collapseMatrix, mul_one]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eq_comm]

theorem forest_population_bound (N Ω : ℕ) (i : Fin N) :
    (forestPopulation N Ω i : ℝ) ≤ ((N/(i.val+1) : ℕ) : ℝ) := by
  rw [← collapse_population, collapse_coherent_reading]
  exact Core.collapse_unit_le N Ω (i.val+1)

theorem forest_population_total (N Ω : ℕ) :
    (∑ i : Fin N, (forestPopulation N Ω i : ℝ))=(N : ℝ) := by
  simp_rw [← collapse_population]
  rw [collapse_matrix_mass]
  simp

theorem collapse_outside_row {N Ω : ℕ} (i : Fin N) (hi : ¬i.val+1 ∣ Ω) (j : Fin N) :
    collapseMatrix ℝ N Ω i j=0 := by
  have hne : i ≠ forestRoot N Ω j := by
    intro he
    have h := forest_root_divides N Ω j
    rw [← he] at h
    exact hi h
  simp only [collapseMatrix, hne, if_false]

theorem collapse_transfer_decomposition (N Ω : ℕ) :
    collapseMatrix ℝ N Ω=Matrix.diagonal (forestMask N Ω)+forestTransfer ℝ N Ω := by
  ext i j
  by_cases hij : i=j
  · subst i
    by_cases hj : j.val+1 ∣ Ω
    · simp [collapseMatrix, forestTransfer, forestMask, hj, forest_root_of_mem j hj]
    · have hne : j ≠ forestRoot N Ω j := (ne_of_lt (forest_root_lt_outside j hj)).symm
      simp [collapseMatrix, forestTransfer, forestMask, hj, hne]
  · by_cases hj : j.val+1 ∣ Ω
    · simp [collapseMatrix, forestTransfer, hj, forest_root_of_mem j hj, hij]
    · simp [collapseMatrix, forestTransfer, hij, hj]

def forestCoherent (N Ω : ℕ) : Fin N → ℝ :=
  forestInverse ℝ N Ω *ᵥ (fun _ => 1)

theorem forest_coherent_complete (N Ω : ℕ) :
    forestMatrix ℝ N Ω *ᵥ forestCoherent N Ω=fun _ => (1 : ℝ) := by
  rw [forestCoherent, Matrix.mulVec_mulVec, forest_matrix_inverse, Matrix.one_mulVec]

theorem forest_coherent_population (N Ω : ℕ) (i : Fin N) :
    forestCoherent N Ω i=if i.val+1 ∣ Ω then (forestPopulation N Ω i : ℝ) else 1 := by
  have hread : (collapseMatrix ℝ N Ω *ᵥ (fun _ => 1)) i=
      forestMask N Ω i+(forestTransfer ℝ N Ω *ᵥ (fun _ => 1)) i := by
    rw [collapse_transfer_decomposition, Matrix.add_mulVec, Pi.add_apply,
      Matrix.mulVec_diagonal, mul_one]
  simp only [forestCoherent, forestInverse, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  by_cases hi : i.val+1 ∣ Ω
  · rw [if_pos hi, ← collapse_population]
    simp only [forestMask, hi, if_true] at hread
    exact hread.symm
  · rw [if_neg hi]
    have hc : (collapseMatrix ℝ N Ω *ᵥ (fun _ => 1)) i=0 := by
      simp only [Matrix.mulVec, dotProduct, collapse_outside_row i hi, zero_mul, Finset.sum_const_zero]
    rw [hc] at hread
    simp only [forestMask, hi, if_false, zero_add] at hread
    rw [← hread, add_zero]

theorem forest_covariance_transport (N Ω : ℕ) :
    Matrix.vecMulVec (forestCoherent N Ω) (forestCoherent N Ω)=
      forestInverse ℝ N Ω*QuadraticResponse.originMatrix N*(forestInverse ℝ N Ω)ᵀ := by
  have hO : QuadraticResponse.originMatrix N=Matrix.vecMulVec (fun _ : Fin N => (1 : ℝ)) (fun _ => 1) := by
    ext i j
    simp [QuadraticResponse.originMatrix, Matrix.vecMulVec_apply]
  rw [hO, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rfl

theorem forest_matrix_integer_cast (N Ω : ℕ) :
    (forestMatrix ℤ N Ω).map (Int.castRingHom ℝ)=forestMatrix ℝ N Ω := by
  ext i j
  simp only [Matrix.map_apply, forestMatrix, Matrix.sub_apply, Matrix.one_apply,
    forestTransfer, map_sub]
  split_ifs <;> norm_num

end NField.ResetForests.ResetMasks
