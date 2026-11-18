/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ContinuousRecord
/-! # Exact dimension increase of the joint arithmetic record -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

variable {N : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem joint_record_kernel (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) :
    LinearMap.ker (Matrix.fromRows A B).mulVecLin = LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
  ext c
  change Matrix.fromRows A B *ᵥ c = 0 ↔ A *ᵥ c = 0 ∧ B *ᵥ c = 0
  rw [Matrix.fromRows_mulVec]
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (Sum.inl i)), funext (fun j => congrFun h (Sum.inr j))⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    funext i
    cases i <;> rfl

omit [Fintype κ] [DecidableEq κ] in
theorem joint_entering_kernel (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) :
    LinearMap.ker (Matrix.fromRows A B).mulVecLin =
      LinearMap.ker (Matrix.fromRows A (enteringRecord G hG A B)).mulVecLin := by
  rw [joint_record_kernel, joint_record_kernel]
  ext c
  change (A *ᵥ c = 0 ∧ B *ᵥ c = 0) ↔ (A *ᵥ c = 0 ∧ enteringRecord G hG A B *ᵥ c = 0)
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, ?_⟩
    have he := later_record_reading G hG A B c
    rw [ha, hb, Matrix.mulVec_zero, zero_add] at he
    exact he.symm
  · rintro ⟨ha, he⟩
    refine ⟨ha, ?_⟩
    rw [later_record_reading G hG A B c, ha, he, Matrix.mulVec_zero, add_zero]

omit [Fintype κ] [DecidableEq κ] in
theorem old_entering_kernels_cover (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) :
    LinearMap.ker A.mulVecLin ⊔ LinearMap.ker (enteringRecord G hG A B).mulVecLin = ⊤ := by
  apply le_antisymm le_top
  intro c _
  apply Submodule.mem_sup.mpr
  refine ⟨c - oldSource G hG A c, ?_, oldSource G hG A c, ?_, ?_⟩
  · change A *ᵥ (c - oldSource G hG A c) = 0
    rw [Matrix.mulVec_sub, old_source_reading, sub_self]
  · exact old_source_entering_zero G hG A B c
  · abel

omit [Fintype κ] [DecidableEq κ] in
theorem entering_record_rank_increase (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) :
    (enteringRecord G hG A B).rank = (Matrix.fromRows A B).rank - A.rank := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker A.mulVecLin) (LinearMap.ker (enteringRecord G hG A B).mulVecLin)
  rw [old_entering_kernels_cover G hG A B, finrank_top,
    ← joint_record_kernel, ← joint_entering_kernel G hG A B] at hs
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hE := LinearMap.finrank_range_add_finrank_ker (enteringRecord G hG A B).mulVecLin
  have hJ := LinearMap.finrank_range_add_finrank_ker (Matrix.fromRows A B).mulVecLin
  change A.rank + _ = _ at hA
  change (enteringRecord G hG A B).rank + _ = _ at hE
  change (Matrix.fromRows A B).rank + _ = _ at hJ
  omega

omit [Fintype κ] [DecidableEq κ] in
theorem joint_entering_surjective (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ)
    (hs : Function.Surjective (Matrix.fromRows A B).mulVec) :
    Function.Surjective (Matrix.fromRows A (enteringRecord G hG A B)).mulVec := by
  intro w
  let y : ι → ℝ := fun i => w (Sum.inl i)
  let eta : κ → ℝ := fun j => w (Sum.inr j)
  obtain ⟨c, hc⟩ := hs (Sum.elim y (laterPrediction G hG A B *ᵥ y + eta))
  have ha : A *ᵥ c = y := by
    funext i
    simpa only [Matrix.fromRows_mulVec, Sum.elim_inl] using congrFun hc (Sum.inl i)
  have hb : B *ᵥ c = laterPrediction G hG A B *ᵥ y + eta := by
    funext j
    simpa only [Matrix.fromRows_mulVec, Sum.elim_inr] using congrFun hc (Sum.inr j)
  have he := later_record_reading G hG A B c
  rw [ha, hb] at he
  have heta : enteringRecord G hG A B *ᵥ c = eta := (add_left_cancel he).symm
  refine ⟨c, ?_⟩
  rw [Matrix.fromRows_mulVec, ha, heta]
  funext i
  cases i <;> rfl

end NField.ResetForests.RecordGeometry
