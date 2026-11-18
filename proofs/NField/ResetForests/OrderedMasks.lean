/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestGram
/-! # General ordered mask work keeps its skew reading until full completion -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ResetMasks

open scoped BigOperators Matrix
open NField.Alignment SourceMetrics CommonResetGram CommonResetGrid CollisionRampEnergy RademacherThreeTerm

def orderedClockMatrix (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun d j => (arithmeticCoefficientDedekindTerm Q (j.val+1) (d.val+1) : ℝ)

theorem ordered_clock_entry (N Q : ℕ) (d j : Fin N) :
    orderedClockMatrix N Q d j=
      ∑ a ∈ Finset.range (d.val+1),
        midpointRow (j.val+1) ((a : ℝ)/((d.val+1 : ℕ) : ℝ))*
          midpointRow Q ((a : ℝ)/((d.val+1 : ℕ) : ℝ)) := by
  unfold orderedClockMatrix arithmeticCoefficientDedekindTerm
  simp_rw [midpointRow_rational (show 0 < d.val+1 from Nat.succ_pos d.val)]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  ring

def maskedBoundary (N Q : ℕ) (σ c : Fin N → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, cutoffCoefficients N σ k*
    Core.resetMass N (cutoffCoefficients N c) k*
      ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        weightedProfile N (cutoffCoefficients N c) ((a : ℝ)/(k : ℝ))*
          midpointRow Q ((a : ℝ)/(k : ℝ))

theorem reset_mask_mass_interval (N : ℕ) (σ c : Fin N → ℝ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 N) :
    Core.resetMass N (cutoffCoefficients N (resetMaskMatrix N σ *ᵥ c)) k=
      cutoffCoefficients N σ k*Core.resetMass N (cutoffCoefficients N c) k := by
  let i : Fin N := ⟨k-1,by have := Finset.mem_Icc.mp hk; omega⟩
  have hfreq : i.val+1=k := by dsimp [i]; have := (Finset.mem_Icc.mp hk).1; omega
  have h := reset_mask_mass N σ c i
  rw [hfreq] at h
  have hcoef : cutoffCoefficients N σ k=σ i := by
    simp only [cutoffCoefficients, dif_pos hk]
    rfl
  rw [hcoef]
  exact h

theorem masked_boundary_ordered (N Q : ℕ) (σ c : Fin N → ℝ) :
    maskedBoundary N Q σ c=
      Core.orderedBoundary N Q (cutoffCoefficients N (resetMaskMatrix N σ *ᵥ c))
        (cutoffCoefficients N c) := by
  unfold maskedBoundary Core.orderedBoundary
  apply Finset.sum_congr rfl
  intro k hk
  rw [reset_mask_mass_interval N σ c
    (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hk).1; omega,(Finset.mem_Icc.mp hk).2⟩)]

theorem ordered_boundary_matrix (N Q : ℕ) (b c : Fin N → ℝ) :
    Core.orderedBoundary N Q (cutoffCoefficients N b) (cutoffCoefficients N c)=
      2*(b ⬝ᵥ (orderedClockMatrix N Q *ᵥ c)) := by
  rw [Core.ordered_boundary_coefficients]
  simp_rw [sum_source_indices, cutoff_coefficients_succ]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, orderedClockMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem masked_boundary_matrix (N Q : ℕ) (σ c : Fin N → ℝ) :
    maskedBoundary N Q σ c=
      2*((resetMaskMatrix N σ *ᵥ c) ⬝ᵥ (orderedClockMatrix N Q *ᵥ c)) := by
  rw [masked_boundary_ordered, ordered_boundary_matrix]

def clockSymmetric (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (1/2 : ℝ) • (orderedClockMatrix N Q+(orderedClockMatrix N Q)ᵀ)

def clockSkew (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (1/2 : ℝ) • (orderedClockMatrix N Q-(orderedClockMatrix N Q)ᵀ)

theorem ordered_clock_split (N Q : ℕ) :
    orderedClockMatrix N Q=clockSymmetric N Q+clockSkew N Q := by
  ext i j
  simp only [clockSymmetric, clockSkew, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem clock_skew_transpose (N Q : ℕ) : (clockSkew N Q)ᵀ= -clockSkew N Q := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, clockSkew,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.transpose_apply]
  ring

theorem clock_skew_self (N Q : ℕ) (c : Fin N → ℝ) : c ⬝ᵥ (clockSkew N Q *ᵥ c)=0 := by
  have h := Matrix.dotProduct_transpose_mulVec (clockSkew N Q) c c
  rw [clock_skew_transpose, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

def maskedSymmetricReading (N Q : ℕ) (σ c : Fin N → ℝ) : ℝ :=
  2*((resetMaskMatrix N σ *ᵥ c) ⬝ᵥ (clockSymmetric N Q *ᵥ c))

def maskedSkewReading (N Q : ℕ) (σ c : Fin N → ℝ) : ℝ :=
  2*((resetMaskMatrix N σ *ᵥ c) ⬝ᵥ (clockSkew N Q *ᵥ c))

theorem masked_boundary_full_split (N Q : ℕ) (σ c : Fin N → ℝ) :
    maskedBoundary N Q σ c=maskedSymmetricReading N Q σ c+maskedSkewReading N Q σ c := by
  rw [masked_boundary_matrix, ordered_clock_split, Matrix.add_mulVec, dotProduct_add, mul_add]
  rfl

theorem mask_source_complement (N : ℕ) (σ c : Fin N → ℝ) :
    (resetMaskMatrix N σ *ᵥ c)+(resetMaskMatrix N (fun k => 1-σ k) *ᵥ c)=c := by
  rw [← Matrix.add_mulVec, reset_mask_complement, Matrix.one_mulVec]

theorem masked_skew_complement (N Q : ℕ) (σ c : Fin N → ℝ) :
    maskedSkewReading N Q σ c+maskedSkewReading N Q (fun k => 1-σ k) c=0 := by
  rw [maskedSkewReading, maskedSkewReading, ← mul_add, ← add_dotProduct,
    mask_source_complement, clock_skew_self, mul_zero]

theorem masked_boundary_complement (N Q : ℕ) (σ c : Fin N → ℝ) :
    maskedBoundary N Q σ c+maskedBoundary N Q (fun k => 1-σ k) c=
      2*(c ⬝ᵥ (orderedClockMatrix N Q *ᵥ c)) := by
  rw [masked_boundary_matrix, masked_boundary_matrix, ← mul_add, ← add_dotProduct,
    mask_source_complement]

theorem saturated_source_population (N Ω : ℕ) (i : Fin N) :
    (resetMaskMatrix N (forestMask N Ω) *ᵥ (fun _ => 1)) i=(forestPopulation N Ω i : ℝ) := by
  rw [saturated_mask_is_collapse, collapse_population]

theorem saturated_source_bound (N Ω : ℕ) (i : Fin N) :
    (resetMaskMatrix N (forestMask N Ω) *ᵥ (fun _ => 1)) i ≤ ((N/(i.val+1) : ℕ) : ℝ) := by
  rw [saturated_source_population]
  exact forest_population_bound N Ω i

theorem saturated_source_mass (N Ω : ℕ) :
    (∑ i : Fin N, (resetMaskMatrix N (forestMask N Ω) *ᵥ (fun _ => 1)) i)=(N : ℝ) := by
  simp_rw [saturated_source_population]
  exact forest_population_total N Ω

end NField.ResetForests.ResetMasks
