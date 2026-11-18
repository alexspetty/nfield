/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RecordMetric
/-! # The old, entering and residual sources with all sampled work -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

variable {N : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def laterPrediction (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) : Matrix κ ι ℝ :=
  B * liftMatrix G hG A

def enteringRecord (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) : Matrix κ (Fin N) ℝ :=
  B - laterPrediction G hG A B * A

def oldSource (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) : Fin N → ℝ :=
  liftMatrix G hG A *ᵥ (A *ᵥ c)

def enteringSource (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) : Fin N → ℝ :=
  oldSource G hG (enteringRecord G hG A B) c

def residualSource (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) : Fin N → ℝ :=
  c - oldSource G hG A c - enteringSource G hG A B c

theorem lift_reflexive (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) : liftMatrix G hG A * A * liftMatrix G hG A = liftMatrix G hG A := by
  have hp : recordInverse G hG A * recordGram G A * recordInverse G hG A = recordInverse G hG A :=
    image_inverse_outer _ _
  calc
    _ = G⁻¹ * Aᵀ * (recordInverse G hG A * recordGram G A * recordInverse G hG A) := by
      simp only [liftMatrix, recordGram, Matrix.mul_assoc]
    _ = _ := by rw [hp]; rfl

omit [Fintype κ] [DecidableEq κ] in
theorem entering_record_orthogonal (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) :
    A * G⁻¹ * (enteringRecord G hG A B)ᵀ = 0 := by
  calc
    _ = A * G⁻¹ * Bᵀ - (recordGram G A * recordInverse G hG A * A) * G⁻¹ * Bᵀ := by
      simp only [enteringRecord, laterPrediction, Matrix.transpose_sub, Matrix.transpose_mul,
        lift_transpose, Matrix.mul_sub, recordGram, Matrix.mul_assoc]
    _ = 0 := by rw [record_projection_fixes, sub_self]

omit [Fintype κ] [DecidableEq κ] in
theorem entering_old_lift_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) :
    enteringRecord G hG A B * liftMatrix G hG A = 0 := by
  calc
    _ = B * liftMatrix G hG A - B * (liftMatrix G hG A * A * liftMatrix G hG A) := by
      simp only [enteringRecord, laterPrediction, Matrix.sub_mul, Matrix.mul_assoc]
    _ = 0 := by rw [lift_reflexive, sub_self]

omit [Fintype κ] [DecidableEq κ] in
theorem later_record_reading (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    B *ᵥ c = laterPrediction G hG A B *ᵥ (A *ᵥ c) + enteringRecord G hG A B *ᵥ c := by
  simp only [enteringRecord, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  abel

theorem old_source_reading (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) : A *ᵥ oldSource G hG A c = A *ᵥ c :=
  lift_matrix_readback G hG A c

theorem entering_source_reading (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    enteringRecord G hG A B *ᵥ enteringSource G hG A B c = enteringRecord G hG A B *ᵥ c :=
  lift_matrix_readback G hG _ c

omit [Fintype κ] [DecidableEq κ] in
theorem old_source_entering_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    enteringRecord G hG A B *ᵥ oldSource G hG A c = 0 := by
  rw [oldSource, Matrix.mulVec_mulVec, entering_old_lift_zero, Matrix.zero_mulVec]

theorem entering_source_old_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    A *ᵥ enteringSource G hG A B c = 0 := by
  have hm : A * liftMatrix G hG (enteringRecord G hG A B) = 0 := by
    calc
      _ = (A * G⁻¹ * (enteringRecord G hG A B)ᵀ) * recordInverse G hG (enteringRecord G hG A B) := by
        simp only [liftMatrix, Matrix.mul_assoc]
      _ = 0 := by rw [entering_record_orthogonal, Matrix.zero_mul]
  rw [enteringSource, oldSource, Matrix.mulVec_mulVec, hm, Matrix.zero_mulVec]

theorem residual_old_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    A *ᵥ residualSource G hG A B c = 0 := by
  simp only [residualSource, Matrix.mulVec_sub, old_source_reading,
    entering_source_old_zero, sub_self]

theorem residual_entering_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    enteringRecord G hG A B *ᵥ residualSource G hG A B c = 0 := by
  simp only [residualSource, Matrix.mulVec_sub, old_source_entering_zero,
    entering_source_reading, sub_self, sub_zero]

theorem residual_later_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    B *ᵥ residualSource G hG A B c = 0 := by
  rw [later_record_reading G hG A B, residual_old_zero, residual_entering_zero,
    Matrix.mulVec_zero, add_zero]

theorem old_entering_work_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    sourceWork G (oldSource G hG A c) (enteringSource G hG A B c) = 0 :=
  lifted_kernel_work_zero G hG A _ _ (entering_source_old_zero G hG A B c)

theorem old_residual_work_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    sourceWork G (oldSource G hG A c) (residualSource G hG A B c) = 0 :=
  lifted_kernel_work_zero G hG A _ _ (residual_old_zero G hG A B c)

theorem entering_residual_work_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    sourceWork G (enteringSource G hG A B c) (residualSource G hG A B c) = 0 :=
  lifted_kernel_work_zero G hG _ _ _ (residual_entering_zero G hG A B c)

theorem complete_source_decomposition (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    c = oldSource G hG A c + enteringSource G hG A B c + residualSource G hG A B c := by
  unfold residualSource
  abel

theorem three_source_work (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.IsHermitian)
    (u v z : Fin N → ℝ) :
    sourceWork G (u + v + z) (u + v + z) =
      sourceWork G u u + sourceWork G v v + sourceWork G z z +
        2 * sourceWork G u v + 2 * sourceWork G u z + 2 * sourceWork G v z := by
  unfold sourceWork
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [PacketQueries.symmetric_query_cross G (hermitian_transpose G hG) v u,
    PacketQueries.symmetric_query_cross G (hermitian_transpose G hG) z u,
    PacketQueries.symmetric_query_cross G (hermitian_transpose G hG) z v]
  ring

theorem complete_record_energy (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    sourceWork G c c =
      (A *ᵥ c) ⬝ᵥ (recordInverse G hG A *ᵥ (A *ᵥ c)) +
      (enteringRecord G hG A B *ᵥ c) ⬝ᵥ
        (recordInverse G hG (enteringRecord G hG A B) *ᵥ (enteringRecord G hG A B *ᵥ c)) +
      sourceWork G (residualSource G hG A B c) (residualSource G hG A B c) := by
  have hc := complete_source_decomposition G hG A B c
  have he := congrArg (fun x => sourceWork G x x) hc
  rw [three_source_work G hG.1, old_entering_work_zero, old_residual_work_zero,
    entering_residual_work_zero] at he
  have hu := lifted_record_work G hG A c
  have hv := lifted_record_work G hG (enteringRecord G hG A B) c
  change sourceWork G (oldSource G hG A c) (oldSource G hG A c) = _ at hu
  change sourceWork G (enteringSource G hG A B c) (enteringSource G hG A B c) = _ at hv
  rw [hu, hv] at he
  linarith

end NField.ResetForests.RecordGeometry
