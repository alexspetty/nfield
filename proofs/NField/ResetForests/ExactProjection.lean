/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ExactArithmetic
/-! # Exact linear witnesses for the prescribed metric projections -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open RecordGeometry PrefixGeometry

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projection_from_linear_witness (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c z : Fin N → ℝ) (w : ι → ℝ)
    (hz : G *ᵥ z = Aᵀ *ᵥ w) (hc : A *ᵥ z = A *ᵥ c) :
    oldSource G hG A c = z := by
  let u := oldSource G hG A c
  let d := z - u
  have hd : A *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hc, u, old_source_reading, sub_self]
  have hzd : sourceWork G z d = 0 := by
    rw [work_symm G hG.1]
    unfold sourceWork
    rw [hz, Matrix.dotProduct_transpose_mulVec, hd, dotProduct_zero]
  have hud : sourceWork G u d = 0 := lifted_kernel_work_zero G hG A _ _ hd
  have he : sourceWork G d d = 0 := by
    change sourceWork G (z - u) d = 0
    rw [work_sub_left, hzd, hud, sub_self]
  exact (sub_eq_zero.mp ((source_work_zero_iff G hG d).mp he)).symm

def castVector {κ : Type*} (v : κ → ℚ) : κ → ℝ := fun i => (v i : ℝ)

omit [Fintype ι] [DecidableEq ι] in
theorem cast_vector_mulVec (A : Matrix ι (Fin N) ℚ) (v : Fin N → ℚ) :
    castVector (A *ᵥ v) = A.map (Rat.castHom ℝ) *ᵥ castVector v := by
  funext i
  exact (Rat.castHom ℝ).map_mulVec A v i

theorem rational_projection_witness (G : Matrix (Fin N) (Fin N) ℚ)
    (hG : (G.map (Rat.castHom ℝ)).PosDef)
    (A : Matrix ι (Fin N) ℚ) (c z : Fin N → ℚ) (w : ι → ℚ)
    (hz : G *ᵥ z = Aᵀ *ᵥ w) (hc : A *ᵥ z = A *ᵥ c) :
    oldSource (G.map (Rat.castHom ℝ)) hG (A.map (Rat.castHom ℝ)) (castVector c) =
      castVector z := by
  apply projection_from_linear_witness _ _ _ _ _ (castVector w)
  · ext i
    have h := congrArg (fun x : Fin N → ℚ => (x i : ℝ)) hz
    change ((∑ j, G i j * z j : ℚ) : ℝ) = ((∑ j, A j i * w j : ℚ) : ℝ) at h
    push_cast at h
    exact h
  · rw [← cast_vector_mulVec, ← cast_vector_mulVec, hc]

theorem rational_source_work (G : Matrix (Fin N) (Fin N) ℚ) (x y : Fin N → ℚ) :
    sourceWork (G.map (Rat.castHom ℝ)) (castVector x) (castVector y) =
      ((x ⬝ᵥ (G *ᵥ y) : ℚ) : ℝ) := by
  symm
  exact (Rat.castHom ℝ).map_dotProduct x (G *ᵥ y) |>.trans
    (congrArg (fun v => castVector x ⬝ᵥ v) (cast_vector_mulVec G y))

omit [DecidableEq ι] in
theorem rational_final_readout (A : Matrix ι (Fin N) ℚ) (b : ι → ℚ) (c : Fin N → ℚ) :
    finalReadout (A.map (Rat.castHom ℝ)) (castVector b) (castVector c) =
      ((b ⬝ᵥ (A *ᵥ c) : ℚ) : ℝ) := by
  symm
  exact (Rat.castHom ℝ).map_dotProduct b (A *ᵥ c) |>.trans
    (congrArg (fun v => castVector b ⬝ᵥ v) (cast_vector_mulVec A c))

end NField.ResetForests.ExactCost
