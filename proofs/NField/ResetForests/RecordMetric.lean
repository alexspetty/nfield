/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ImageInverse
/-! # Complete record images in the actual positive source metric -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def recordGram (G : Matrix (Fin N) (Fin N) ℝ) (A : Matrix ι (Fin N) ℝ) : Matrix ι ι ℝ :=
  A * G⁻¹ * Aᵀ

omit [Fintype ι] [DecidableEq ι] in
theorem hermitian_transpose (G : Matrix ι ι ℝ) (hG : G.IsHermitian) : Gᵀ = G := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hG

omit [DecidableEq ι] in
theorem transpose_pairing {κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ)
    (x : ι → ℝ) (y : κ → ℝ) : x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
  calc
    _ = y ⬝ᵥ (Aᵀ *ᵥ x) := by
      simpa only [Matrix.transpose_transpose] using Matrix.dotProduct_transpose_mulVec Aᵀ x y
    _ = _ := dotProduct_comm _ _

omit [Fintype ι] [DecidableEq ι] in
theorem record_gram_hermitian (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : (recordGram G A).IsHermitian := by
  simpa only [recordGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose A hG.inv.1

def recordInverse (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : Matrix ι ι ℝ :=
  imageInverse (recordGram G A) (record_gram_hermitian G hG A)

def liftMatrix (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : Matrix (Fin N) ι ℝ :=
  G⁻¹ * Aᵀ * recordInverse G hG A

def sourceWork (G : Matrix (Fin N) (Fin N) ℝ) (x y : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ (G *ᵥ y)

omit [DecidableEq ι] in
theorem record_gram_quadratic (G : Matrix (Fin N) (Fin N) ℝ)
    (A : Matrix ι (Fin N) ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (recordGram G A *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ (G⁻¹ *ᵥ (Aᵀ *ᵥ x)) := by
  unfold recordGram
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, transpose_pairing]

omit [DecidableEq ι] in
theorem record_gram_kernel (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) :
    LinearMap.ker (recordGram G A).mulVecLin = LinearMap.ker Aᵀ.mulVecLin := by
  ext x
  change recordGram G A *ᵥ x = 0 ↔ Aᵀ *ᵥ x = 0
  constructor
  · intro hx
    by_contra ha
    have hp := hG.inv.dotProduct_mulVec_pos ha
    simp only [star_trivial] at hp
    have he := record_gram_quadratic G A x
    rw [hx, dotProduct_zero] at he
    linarith
  · intro hx
    simp only [recordGram, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

omit [DecidableEq ι] in
theorem record_gram_rank (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : (recordGram G A).rank = A.rank := by
  have hH := LinearMap.finrank_range_add_finrank_ker (recordGram G A).mulVecLin
  have hA := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  rw [record_gram_kernel G hG A] at hH
  change (recordGram G A).rank + _ = _ at hH
  change Aᵀ.rank + _ = _ at hA
  rw [Matrix.rank_transpose] at hA
  omega

omit [DecidableEq ι] in
theorem record_gram_range (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) :
    LinearMap.range (recordGram G A).mulVecLin = LinearMap.range A.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, rfl⟩
    refine ⟨G⁻¹ *ᵥ (Aᵀ *ᵥ x), ?_⟩
    change A *ᵥ (G⁻¹ *ᵥ (Aᵀ *ᵥ x)) = recordGram G A *ᵥ x
    simp only [recordGram, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · exact record_gram_rank G hG A

theorem record_inverse_transpose (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : (recordInverse G hG A)ᵀ = recordInverse G hG A :=
  hermitian_transpose _ (image_inverse_hermitian _ _)

theorem metric_inverse_left (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) : G⁻¹ * G = 1 :=
  Matrix.nonsing_inv_mul G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)

theorem metric_inverse_right (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) : G * G⁻¹ = 1 :=
  Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)

theorem record_projection_fixes (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : recordGram G A * recordInverse G hG A * A = A := by
  apply Matrix.mulVec_injective
  funext c
  simp only [← Matrix.mulVec_mulVec]
  apply image_inverse_on_image
  rw [record_gram_range G hG A]
  exact ⟨c, rfl⟩

theorem lift_matrix_readback (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) :
    A *ᵥ (liftMatrix G hG A *ᵥ (A *ᵥ c)) = A *ᵥ c := by
  have hp := congrArg (fun M => M *ᵥ c) (record_projection_fixes G hG A)
  simpa only [liftMatrix, recordGram, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hp

theorem lift_metric_image (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : G * liftMatrix G hG A = Aᵀ * recordInverse G hG A := by
  simp only [liftMatrix, ← Matrix.mul_assoc, metric_inverse_right G hG, Matrix.one_mul]

theorem lift_transpose (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : (liftMatrix G hG A)ᵀ = recordInverse G hG A * A * G⁻¹ := by
  simp only [liftMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    record_inverse_transpose, hermitian_transpose _ hG.inv.1, Matrix.mul_assoc]

theorem lift_metric_vector (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (y : ι → ℝ) :
    G *ᵥ (liftMatrix G hG A *ᵥ y) = Aᵀ *ᵥ (recordInverse G hG A *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, lift_metric_image, ← Matrix.mulVec_mulVec]

theorem lifted_kernel_work_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (y : ι → ℝ) (z : Fin N → ℝ) (hz : A *ᵥ z = 0) :
    sourceWork G (liftMatrix G hG A *ᵥ y) z = 0 := by
  unfold sourceWork
  rw [PacketQueries.symmetric_query_cross G (hermitian_transpose G hG.1)]
  rw [lift_metric_vector, Matrix.dotProduct_transpose_mulVec, hz, dotProduct_zero]

theorem lifted_record_work (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) :
    sourceWork G (liftMatrix G hG A *ᵥ (A *ᵥ c)) (liftMatrix G hG A *ᵥ (A *ᵥ c)) =
      (A *ᵥ c) ⬝ᵥ (recordInverse G hG A *ᵥ (A *ᵥ c)) := by
  unfold sourceWork
  rw [lift_metric_vector, Matrix.dotProduct_transpose_mulVec, lift_matrix_readback]
  exact dotProduct_comm _ _

end NField.ResetForests.RecordGeometry
