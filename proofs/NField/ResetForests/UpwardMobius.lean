/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.ResetForests.DivisorBudget
import NField.ResetForests.Sampling
import NField.ResetForests.OrderedWork
import NField.ResetForests.Words
import NField.ResetForests.Carry
import NField.ResetForests.Readout
import NField.ResetForests.CoherentWork
import NField.ResetForests.Targets
import NField.ResetForests.GridWork
import NField.ResetForests.Centered
import NField.ResetForests.CarryClock
import NField.ResetForests.ClockBinary
import NField.ResetForests.PhaseFringe
import NField.ResetForests.LoadTail
import NField.ResetForests.ForestRates
import NField.ResetForests.Opening
import NField.ResetForests.Complement
import NField.ResetForests.WindowExample
import NField.ResetForests.EnergyMatrices
import NField.ResetForests.FibreDirections
import NField.ResetForests.FibreBasisTrace
import NField.ResetForests.GramSectors
import NField.ResetForests.TorusIncidence
import NField.ResetForests.CompleteReset
/-! # The finite upward divisor transform and its literal Möbius inverse -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ResetMasks

open scoped BigOperators Matrix
open NField.Alignment SourceMetrics PrimitiveCoordinates

theorem positive_multiples_sum {d : ℕ} (hd : 0 < d) (N : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, if d ∣ k then f k else 0)=
      ∑ j ∈ Finset.Icc 1 (N/d), f (d*j) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun j _ => d*j) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1,hjN⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hj1,?_⟩,dvd_mul_right d j⟩
    have h := (Nat.le_div_iff_mul_le hd).mp hjN
    simpa only [Nat.mul_comm] using h
  · intro j hj k hk he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hk,hdk⟩
    rcases Finset.mem_Icc.mp hk with ⟨hk1,hkN⟩
    refine ⟨k/d,Finset.mem_Icc.mpr ⟨?_,Nat.div_le_div_right hkN⟩,Nat.mul_div_cancel' hdk⟩
    exact Nat.div_pos (Nat.le_of_dvd hk1 hdk) hd
  · intro j hj
    rfl

def resetMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun k j => if k.val+1 ∣ j.val+1 then 1 else 0

def mobiusMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun d k => if d.val+1 ∣ k.val+1 then
    (ArithmeticFunction.moebius ((k.val+1)/(d.val+1)) : ℝ) else 0

theorem reset_matrix_reading (N : ℕ) (c : Fin N → ℝ) (k : Fin N) :
    (resetMatrix N *ᵥ c) k=Core.resetMass N (cutoffCoefficients N c) (k.val+1) := by
  simp only [resetMatrix, Matrix.mulVec, dotProduct, Core.resetMass,
    Core.sourceIndices, sum_source_indices, cutoff_coefficients_succ]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hd : k.val+1 ∣ j.val+1 <;> simp [hd]

theorem mobius_matrix_reading (N : ℕ) (m : Fin N → ℝ) (d : Fin N) :
    (mobiusMatrix N *ᵥ m) d=
      ∑ j ∈ Finset.Icc 1 (N/(d.val+1)), (ArithmeticFunction.moebius j : ℝ)*
        cutoffCoefficients N m ((d.val+1)*j) := by
  have he : (mobiusMatrix N *ᵥ m) d=
      ∑ k ∈ Finset.Icc 1 N, if d.val+1 ∣ k then
        (ArithmeticFunction.moebius (k/(d.val+1)) : ℝ)*cutoffCoefficients N m k else 0 := by
    rw [sum_source_indices]
    simp only [Matrix.mulVec, dotProduct, mobiusMatrix, cutoff_coefficients_succ]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hd : d.val+1 ∣ k.val+1 <;> simp [hd]
  rw [he, positive_multiples_sum (Nat.succ_pos d.val)]
  simp only [Nat.mul_div_right _ (Nat.succ_pos d.val)]

theorem reset_mobius_left (N : ℕ) : mobiusMatrix N*resetMatrix N=1 := by
  ext i h
  have hi := Nat.succ_pos i.val
  have he : (mobiusMatrix N*resetMatrix N) i h=
      ∑ k ∈ Finset.Icc 1 N, if i.val+1 ∣ k then
        (if k ∣ h.val+1 then (ArithmeticFunction.moebius (k/(i.val+1)) : ℝ) else 0) else 0 := by
    rw [Matrix.mul_apply, sum_source_indices]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mobiusMatrix, resetMatrix]
    by_cases hik : i.val+1 ∣ k.val+1 <;>
      by_cases hkh : k.val+1 ∣ h.val+1 <;> simp [hik,hkh]
  rw [he, positive_multiples_sum hi]
  simp only [Nat.mul_div_right _ hi]
  by_cases hdiv : i.val+1 ∣ h.val+1
  · have hq : 0 < (h.val+1)/(i.val+1) :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos h.val) hdiv) hi
    have hqN : (h.val+1)/(i.val+1) ≤ N/(i.val+1) :=
      Nat.div_le_div_right (by omega : h.val+1 ≤ N)
    have hfactor := Nat.mul_div_cancel' hdiv
    have hdvd (k : ℕ) : (i.val+1)*k ∣ h.val+1 ↔ k ∣ (h.val+1)/(i.val+1) := by
      conv_lhs => rw [← hfactor]
      exact Nat.mul_dvd_mul_iff_left hi
    simp_rw [hdvd]
    rw [← Finset.sum_filter, cutoff_divisor_set hq hqN, moebius_divisor_sum]
    by_cases hh : i=h
    · subst h
      simp
    · have hq1 : (h.val+1)/(i.val+1) ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hfactor
        apply hh
        exact Fin.ext (by omega)
      simp [hq1, hh]
  · have hdvd (k : ℕ) : ¬(i.val+1)*k ∣ h.val+1 := by
      intro hk
      exact hdiv (dvd_trans (dvd_mul_right (i.val+1) k) hk)
    have hih : i ≠ h := by
      intro hh
      apply hdiv
      rw [hh]
    simp [hdvd, hih]

theorem reset_mobius_right (N : ℕ) : resetMatrix N*mobiusMatrix N=1 :=
  mul_eq_one_comm.mp (reset_mobius_left N)

theorem reset_matrix_inverse (N : ℕ) : (resetMatrix N)⁻¹=mobiusMatrix N :=
  Matrix.inv_eq_left_inv (reset_mobius_left N)

def resetMaskMatrix (N : ℕ) (σ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  mobiusMatrix N*Matrix.diagonal σ*resetMatrix N

theorem reset_mask_formula (N : ℕ) (σ : Fin N → ℝ) :
    resetMaskMatrix N σ=(resetMatrix N)⁻¹*Matrix.diagonal σ*resetMatrix N := by
  rw [reset_matrix_inverse]
  rfl

theorem reset_mask_identity (N : ℕ) (σ : Fin N → ℝ) :
    resetMatrix N*resetMaskMatrix N σ=Matrix.diagonal σ*resetMatrix N := by
  rw [resetMaskMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    reset_mobius_right, Matrix.one_mul]

theorem reset_mask_reading (N : ℕ) (σ c : Fin N → ℝ) (k : Fin N) :
    (resetMatrix N *ᵥ (resetMaskMatrix N σ *ᵥ c)) k=
      σ k*(resetMatrix N *ᵥ c) k := by
  rw [Matrix.mulVec_mulVec, reset_mask_identity, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_diagonal]

theorem reset_mask_unique (N : ℕ) (σ : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : resetMatrix N*A=Matrix.diagonal σ*resetMatrix N) : A=resetMaskMatrix N σ := by
  calc
    A=(mobiusMatrix N*resetMatrix N)*A := by rw [reset_mobius_left, Matrix.one_mul]
    _=resetMaskMatrix N σ := by
      rw [Matrix.mul_assoc, hA]
      simp only [resetMaskMatrix, Matrix.mul_assoc]

end NField.ResetForests.ResetMasks
