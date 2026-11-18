/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketRecord
import Mathlib.LinearAlgebra.Matrix.BilinearForm
/-! # Rank and exact-record obstructions for symmetric quadratic queries -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketQueries

open scoped BigOperators Matrix

def matrixForm {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) : QuadraticForm ℝ (Fin N → ℝ) :=
  (Matrix.toBilin' B).toQuadraticMap

theorem matrix_form_apply {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    matrixForm B x = x ⬝ᵥ (B *ᵥ x) := by
  simp only [matrixForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply']

theorem symmetric_query_cross {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = B)
    (x y : Fin N → ℝ) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  calc
    x ⬝ᵥ (B *ᵥ y) = x ⬝ᵥ (Bᵀ *ᵥ y) := by rw [hB]
    _ = y ⬝ᵥ (B *ᵥ x) := Matrix.dotProduct_transpose_mulVec B x y

theorem symmetric_query_add {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = B)
    (x y : Fin N → ℝ) :
    (x + y) ⬝ᵥ (B *ᵥ (x + y)) =
      x ⬝ᵥ (B *ᵥ x) + y ⬝ᵥ (B *ᵥ y) + 2 * (x ⬝ᵥ (B *ᵥ y)) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    symmetric_query_cross B hB y x]
  ring

theorem kernel_of_query_translation {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = B)
    (z : Fin N → ℝ) (hz : z ⬝ᵥ (B *ᵥ z) = 0)
    (ht : ∀ x, (x + z) ⬝ᵥ (B *ᵥ (x + z)) = x ⬝ᵥ (B *ᵥ x)) : B *ᵥ z = 0 := by
  ext i
  have h := ht (Pi.single i 1)
  rw [symmetric_query_add B hB, hz] at h
  simp only [single_dotProduct, one_mul] at h
  change (B *ᵥ z) i = 0
  linarith

theorem matrix_form_radical {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = B) :
    (matrixForm B).radical = LinearMap.ker B.mulVecLin := by
  ext z
  rw [QuadraticMap.mem_radical_iff']
  change (matrixForm B z = 0 ∧ ∀ x, matrixForm B (z + x) = matrixForm B x) ↔ B *ᵥ z = 0
  simp only [matrix_form_apply]
  constructor
  · rintro ⟨hz, ht⟩
    apply kernel_of_query_translation B hB z hz
    intro x
    simpa only [add_comm x z] using ht x
  · intro hz
    constructor
    · rw [hz, dotProduct_zero]
    · intro x
      rw [add_comm z x, symmetric_query_add B hB, hz, dotProduct_zero, dotProduct_zero]
      ring

theorem matrix_form_signature_rank {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = B) :
    sigPos (matrixForm B) + sigNeg (matrixForm B) = B.rank := by
  have hs := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := matrixForm B)
  rw [matrix_form_radical B hB] at hs
  have hr := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  change B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = _ at hr
  omega

theorem pullback_right_inverse {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ)
    (R : Matrix (Fin N) (RecordIndex t) ℝ) (hAR : A * R = 1) :
    Rᵀ * pullbackQuery A * R = pairQuery t := by
  calc
    Rᵀ * pullbackQuery A * R = (A * R)ᵀ * pairQuery t * (A * R) := by
      simp only [pullbackQuery, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = pairQuery t := by rw [hAR, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem pullback_query_rank {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ)
    (hA : Function.Surjective A.mulVec) : (pullbackQuery A).rank = 2 * t := by
  obtain ⟨R, hAR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hlo : (pairQuery t).rank ≤ (pullbackQuery A).rank := by
    rw [← pullback_right_inverse A R hAR]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hhi : (pullbackQuery A).rank ≤ 2 * t :=
    (Matrix.rank_mul_le_left Aᵀ (pairQuery t * A)).trans
      ((Matrix.rank_le_card_width Aᵀ).trans_eq (record_index_card t))
  rw [pair_query_rank] at hlo
  omega

theorem exact_linear_record_rank_bound {N d : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : Bᵀ = B) (T : Matrix (Fin d) (Fin N) ℝ) (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ x, x ⬝ᵥ (B *ᵥ x) = f (T *ᵥ x)) : B.rank ≤ d := by
  have hzero : f 0 = 0 := by simpa using (hf 0).symm
  have hk : LinearMap.ker T.mulVecLin ≤ LinearMap.ker B.mulVecLin := by
    intro z hz
    change T *ᵥ z = 0 at hz
    change B *ᵥ z = 0
    apply kernel_of_query_translation B hB z
    · rw [hf z, hz, hzero]
    · intro x
      rw [hf (x + z), hf x, Matrix.mulVec_add, hz, add_zero]
  have hd := Submodule.finrank_mono hk
  have hrB := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hrT := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
  have hT := Matrix.rank_le_card_height T
  change B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = _ at hrB
  change T.rank + Module.finrank ℝ (LinearMap.ker T.mulVecLin) = _ at hrT
  simp only [Fintype.card_fin] at hT
  omega

theorem exact_packet_record_minimum_dimension {N t d : ℕ}
    (A : Matrix (RecordIndex t) (Fin N) ℝ) (hA : Function.Surjective A.mulVec)
    (T : Matrix (Fin d) (Fin N) ℝ) (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ x, x ⬝ᵥ (pullbackQuery A *ᵥ x) = f (T *ᵥ x)) : 2 * t ≤ d := by
  rw [← pullback_query_rank A hA]
  exact exact_linear_record_rank_bound _ (pullback_query_symmetric A) T f hf

end NField.ResetForests.PacketQueries
