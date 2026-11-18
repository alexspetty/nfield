/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.UpwardMobius
/-! # The full forest source basis over the integers and the reals -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ResetMasks

open scoped BigOperators Matrix
open Module

def forestRoot (N Ω : ℕ) (j : Fin N) : Fin N :=
  ⟨(j.val+1).gcd Ω-1, by
    have hp : 0 < (j.val+1).gcd Ω := Nat.gcd_pos_of_pos_left Ω (Nat.succ_pos j.val)
    have hl : (j.val+1).gcd Ω ≤ j.val+1 := Nat.gcd_le_left Ω (Nat.succ_pos j.val)
    omega⟩

theorem forest_root_frequency (N Ω : ℕ) (j : Fin N) :
    (forestRoot N Ω j).val+1=(j.val+1).gcd Ω := by
  exact Nat.sub_add_cancel (Nat.gcd_pos_of_pos_left Ω (Nat.succ_pos j.val))

theorem forest_root_divides (N Ω : ℕ) (j : Fin N) :
    (forestRoot N Ω j).val+1 ∣ Ω := by
  rw [forest_root_frequency]
  exact Nat.gcd_dvd_right _ _

theorem forest_root_of_mem {N Ω : ℕ} (j : Fin N) (hj : j.val+1 ∣ Ω) :
    forestRoot N Ω j=j := by
  apply Fin.ext
  simp only [forestRoot, Nat.gcd_eq_left hj, Nat.add_sub_cancel]

theorem forest_root_le (N Ω : ℕ) (j : Fin N) : forestRoot N Ω j ≤ j := by
  have h : (j.val+1).gcd Ω ≤ j.val+1 := Nat.gcd_le_left Ω (Nat.succ_pos j.val)
  have hp : 0 < (j.val+1).gcd Ω := Nat.gcd_pos_of_pos_left Ω (Nat.succ_pos j.val)
  change (j.val+1).gcd Ω-1 ≤ j.val
  omega

theorem forest_root_lt_outside {N Ω : ℕ} (j : Fin N) (hj : ¬j.val+1 ∣ Ω) :
    forestRoot N Ω j < j := by
  apply lt_of_le_of_ne (forest_root_le N Ω j)
  intro he
  have h := forest_root_divides N Ω j
  rw [he] at h
  exact hj h

variable (R : Type*) [CommRing R]

def collapseMatrix (N Ω : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if i=forestRoot N Ω j then 1 else 0

def forestTransfer (N Ω : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if j.val+1 ∣ Ω then 0 else if i=forestRoot N Ω j then 1 else 0

def forestMatrix (N Ω : ℕ) : Matrix (Fin N) (Fin N) R :=
  1-forestTransfer R N Ω

def forestInverse (N Ω : ℕ) : Matrix (Fin N) (Fin N) R :=
  1+forestTransfer R N Ω

theorem forest_transfer_square (N Ω : ℕ) :
    forestTransfer R N Ω*forestTransfer R N Ω=0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hj : j.val+1 ∣ Ω
  · apply Finset.sum_eq_zero
    intro k hk
    simp only [forestTransfer, hj, if_true, mul_zero]
  · have hcol (k : Fin N) : forestTransfer R N Ω k j=
        if k=forestRoot N Ω j then 1 else 0 := by
      simp only [forestTransfer, hj, if_false]
    simp_rw [hcol]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [forestTransfer, forest_root_divides, if_true]

theorem forest_matrix_inverse (N Ω : ℕ) :
    forestMatrix R N Ω*forestInverse R N Ω=1 := by
  have he : (1-forestTransfer R N Ω)*(1+forestTransfer R N Ω)=
      1-forestTransfer R N Ω*forestTransfer R N Ω := by noncomm_ring
  rw [forestMatrix, forestInverse, he, forest_transfer_square, sub_zero]

theorem forest_inverse_matrix (N Ω : ℕ) :
    forestInverse R N Ω*forestMatrix R N Ω=1 := by
  have he : (1+forestTransfer R N Ω)*(1-forestTransfer R N Ω)=
      1-forestTransfer R N Ω*forestTransfer R N Ω := by noncomm_ring
  rw [forestMatrix, forestInverse, he, forest_transfer_square, sub_zero]

def forestEquiv (N Ω : ℕ) : (Fin N → R) ≃ₗ[R] (Fin N → R) :=
  LinearEquiv.ofLinear (forestMatrix R N Ω).toLin' (forestInverse R N Ω).toLin'
    (by
      apply LinearMap.ext
      intro x
      change forestMatrix R N Ω *ᵥ (forestInverse R N Ω *ᵥ x)=x
      rw [Matrix.mulVec_mulVec, forest_matrix_inverse, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      change forestInverse R N Ω *ᵥ (forestMatrix R N Ω *ᵥ x)=x
      rw [Matrix.mulVec_mulVec, forest_inverse_matrix, Matrix.one_mulVec])

def forestBasis (N Ω : ℕ) : Basis (Fin N) R (Fin N → R) :=
  (Pi.basisFun R (Fin N)).map (forestEquiv R N Ω)

theorem forest_transfer_single (N Ω : ℕ) (j : Fin N) :
    forestTransfer R N Ω *ᵥ Pi.single j 1=
      if j.val+1 ∣ Ω then 0 else Pi.single (forestRoot N Ω j) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  by_cases hj : j.val+1 ∣ Ω <;> simp [forestTransfer, hj, Pi.single_apply]

theorem forest_basis_apply (N Ω : ℕ) (j : Fin N) :
    forestBasis R N Ω j=
      if j.val+1 ∣ Ω then Pi.single j 1 else
        Pi.single j 1-Pi.single (forestRoot N Ω j) 1 := by
  simp only [forestBasis, Basis.map_apply, Pi.basisFun_apply]
  change forestMatrix R N Ω *ᵥ Pi.single j 1=_
  rw [forestMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, forest_transfer_single]
  by_cases hj : j.val+1 ∣ Ω <;> simp [hj]

theorem forest_transfer_diagonal (N Ω : ℕ) (i : Fin N) :
    forestTransfer R N Ω i i=0 := by
  by_cases hi : i.val+1 ∣ Ω
  · simp [forestTransfer, hi]
  · have hne : i ≠ forestRoot N Ω i := (ne_of_lt (forest_root_lt_outside i hi)).symm
    simp [forestTransfer, hi, hne]

theorem forest_matrix_diagonal (N Ω : ℕ) (i : Fin N) :
    forestMatrix R N Ω i i=1 := by
  simp only [forestMatrix, Matrix.sub_apply, Matrix.one_apply_eq,
    forest_transfer_diagonal, sub_zero]

theorem forest_transfer_upper (N Ω : ℕ) (i j : Fin N) (hji : j < i) :
    forestTransfer R N Ω i j=0 := by
  have hne : i ≠ forestRoot N Ω j := by
    intro he
    have h := forest_root_le N Ω j
    rw [← he] at h
    exact (not_le_of_gt hji) h
  simp only [forestTransfer, hne, if_false]
  split_ifs <;> rfl

theorem forest_matrix_upper (N Ω : ℕ) : (forestMatrix R N Ω).BlockTriangular id := by
  intro i j hji
  have hne : i ≠ j := (ne_of_lt hji).symm
  simp only [forestMatrix, Matrix.sub_apply, Matrix.one_apply_ne hne,
    forest_transfer_upper R N Ω i j hji, sub_zero]

theorem forest_matrix_det (N Ω : ℕ) : (forestMatrix R N Ω).det=1 := by
  rw [Matrix.det_of_upperTriangular (forest_matrix_upper R N Ω)]
  simp only [forest_matrix_diagonal, Finset.prod_const_one]

end NField.ResetForests.ResetMasks
