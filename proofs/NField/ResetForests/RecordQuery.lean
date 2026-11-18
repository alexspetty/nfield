/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EnteringDimension
/-! # Complete transported quadratic queries and their unique blocks -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def blockReading (C : Matrix ι ι ℝ) (D : Matrix ι κ ℝ) (K : Matrix κ κ ℝ)
    (y : ι → ℝ) (eta : κ → ℝ) : ℝ :=
  y ⬝ᵥ (C *ᵥ y) + 2 * (y ⬝ᵥ (D *ᵥ eta)) + eta ⬝ᵥ (K *ᵥ eta)

omit [DecidableEq ι] in
theorem record_quadratic_add (J : Matrix ι ι ℝ) (hJ : J.IsHermitian) (x y : ι → ℝ) :
    (x + y) ⬝ᵥ (J *ᵥ (x + y)) =
      x ⬝ᵥ (J *ᵥ x) + y ⬝ᵥ (J *ᵥ y) + 2 * (x ⬝ᵥ (J *ᵥ y)) := by
  have hc : y ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ (J *ᵥ y) := by
    calc
      _ = y ⬝ᵥ (Jᵀ *ᵥ x) := by rw [hermitian_transpose J hJ]
      _ = _ := Matrix.dotProduct_transpose_mulVec J y x
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [hc]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem record_pullback_mixed (T : Matrix κ ι ℝ) (J : Matrix κ κ ℝ)
    (y : ι → ℝ) (eta : κ → ℝ) :
    y ⬝ᵥ ((Tᵀ * J) *ᵥ eta) = (T *ᵥ y) ⬝ᵥ (J *ᵥ eta) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

omit [DecidableEq ι] [DecidableEq κ] in
theorem record_pullback_quadratic (T : Matrix κ ι ℝ) (J : Matrix κ κ ℝ) (y : ι → ℝ) :
    y ⬝ᵥ ((Tᵀ * J * T) *ᵥ y) = (T *ᵥ y) ⬝ᵥ (J *ᵥ (T *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, record_pullback_mixed]

omit [DecidableEq ι] [DecidableEq κ] in
theorem two_record_quadratic (J0 : Matrix ι ι ℝ) (J1 : Matrix κ κ ℝ) (hJ1 : J1.IsHermitian)
    (T : Matrix κ ι ℝ) (y : ι → ℝ) (eta : κ → ℝ) :
    y ⬝ᵥ (J0 *ᵥ y) + (T *ᵥ y + eta) ⬝ᵥ (J1 *ᵥ (T *ᵥ y + eta)) =
      blockReading (J0 + Tᵀ * J1 * T) (Tᵀ * J1) J1 y eta := by
  rw [record_quadratic_add J1 hJ1]
  simp only [blockReading, Matrix.add_mulVec, dotProduct_add,
    record_pullback_quadratic, record_pullback_mixed]
  ring

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem transported_query_hermitian (J0 : Matrix ι ι ℝ) (J1 : Matrix κ κ ℝ)
    (hJ0 : J0.IsHermitian) (hJ1 : J1.IsHermitian) (T : Matrix κ ι ℝ) :
    (J0 + Tᵀ * J1 * T).IsHermitian := by
  apply hJ0.add
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul T hJ1

omit [DecidableEq κ] in
theorem complete_record_query {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ)
    (J0 : Matrix ι ι ℝ) (J1 : Matrix κ κ ℝ) (hJ1 : J1.IsHermitian) (c : Fin N → ℝ) :
    (A *ᵥ c) ⬝ᵥ (J0 *ᵥ (A *ᵥ c)) + (B *ᵥ c) ⬝ᵥ (J1 *ᵥ (B *ᵥ c)) =
      blockReading
        (J0 + (laterPrediction G hG A B)ᵀ * J1 * laterPrediction G hG A B)
        ((laterPrediction G hG A B)ᵀ * J1) J1 (A *ᵥ c) (enteringRecord G hG A B *ᵥ c) := by
  rw [later_record_reading G hG A B c]
  exact two_record_quadratic J0 J1 hJ1 _ _ _

theorem symmetric_query_matrix_ext (C C' : Matrix ι ι ℝ) (hC : C.IsHermitian) (hC' : C'.IsHermitian)
    (h : ∀ x, x ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ (C' *ᵥ x)) : C = C' := by
  have hpair (x y : ι → ℝ) : x ⬝ᵥ (C *ᵥ y) = x ⬝ᵥ (C' *ᵥ y) := by
    have he := h (x + y)
    rw [record_quadratic_add C hC, record_quadratic_add C' hC', h x, h y] at he
    linarith
  ext i j
  have he := hpair (Pi.single i 1) (Pi.single j 1)
  simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply'] using he

theorem complete_query_blocks_unique
    (C C' : Matrix ι ι ℝ) (D D' : Matrix ι κ ℝ) (K K' : Matrix κ κ ℝ)
    (hC : C.IsHermitian) (hC' : C'.IsHermitian) (hK : K.IsHermitian) (hK' : K'.IsHermitian)
    (h : ∀ y eta, blockReading C D K y eta = blockReading C' D' K' y eta) :
    C = C' ∧ D = D' ∧ K = K' := by
  have hc : C = C' := symmetric_query_matrix_ext C C' hC hC' (fun y => by
    simpa [blockReading] using h y 0)
  have hk : K = K' := symmetric_query_matrix_ext K K' hK hK' (fun eta => by
    simpa [blockReading] using h 0 eta)
  have hd : D = D' := by
    ext i j
    have he := h (Pi.single i 1) (Pi.single j 1)
    simp only [blockReading, hc, hk, Matrix.mulVec_single_one,
      single_dotProduct, one_mul, Matrix.col_apply'] at he
    linarith
  exact ⟨hc, hd, hk⟩

theorem actual_source_query_blocks_unique {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ)
    (hs : Function.Surjective (Matrix.fromRows A B).mulVec)
    (C C' : Matrix ι ι ℝ) (D D' : Matrix ι κ ℝ) (K K' : Matrix κ κ ℝ)
    (hC : C.IsHermitian) (hC' : C'.IsHermitian) (hK : K.IsHermitian) (hK' : K'.IsHermitian)
    (h : ∀ c, blockReading C D K (A *ᵥ c) (enteringRecord G hG A B *ᵥ c) =
      blockReading C' D' K' (A *ᵥ c) (enteringRecord G hG A B *ᵥ c)) :
    C = C' ∧ D = D' ∧ K = K' := by
  apply complete_query_blocks_unique C C' D D' K K' hC hC' hK hK'
  intro y eta
  obtain ⟨c, hc⟩ := joint_entering_surjective G hG A B hs (Sum.elim y eta)
  have ha : A *ᵥ c = y := by
    funext i
    simpa only [Matrix.fromRows_mulVec, Sum.elim_inl] using congrFun hc (Sum.inl i)
  have he : enteringRecord G hG A B *ᵥ c = eta := by
    funext j
    simpa only [Matrix.fromRows_mulVec, Sum.elim_inr] using congrFun hc (Sum.inr j)
  simpa only [ha, he] using h c

end NField.ResetForests.RecordGeometry
