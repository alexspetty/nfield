/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.MinimumWork
/-! # Physical row restrictions and their source-metric projections -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open RecordGeometry

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def restrictedRecord (A : Matrix ι (Fin N) ℝ) (s : Finset ι) : Matrix ι (Fin N) ℝ :=
  fun i j => if i ∈ s then A i j else 0

omit [Fintype ι] in
theorem restricted_reading (A : Matrix ι (Fin N) ℝ) (s : Finset ι)
    (c : Fin N → ℝ) (i : ι) :
    (restrictedRecord A s *ᵥ c) i = if i ∈ s then (A *ᵥ c) i else 0 := by
  classical
  by_cases hi : i ∈ s <;> simp [restrictedRecord, Matrix.mulVec, hi]

omit [Fintype ι] in
theorem restricted_empty (A : Matrix ι (Fin N) ℝ) : restrictedRecord A ∅ = 0 := by
  ext i j
  simp [restrictedRecord]

theorem restricted_univ (A : Matrix ι (Fin N) ℝ) : restrictedRecord A Finset.univ = A := by
  ext i j
  simp [restrictedRecord]

theorem work_symm (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.IsHermitian)
    (x y : Fin N → ℝ) : sourceWork G x y = sourceWork G y x :=
  PacketQueries.symmetric_query_cross G (hermitian_transpose G hG) x y

theorem work_sub_left (G : Matrix (Fin N) (Fin N) ℝ) (x y z : Fin N → ℝ) :
    sourceWork G (x - y) z = sourceWork G x z - sourceWork G y z := by
  simp only [sourceWork, sub_dotProduct]

theorem work_sub_right (G : Matrix (Fin N) (Fin N) ℝ) (x y z : Fin N → ℝ) :
    sourceWork G x (y - z) = sourceWork G x y - sourceWork G x z := by
  simp only [sourceWork, Matrix.mulVec_sub, dotProduct_sub]

theorem work_sum_left {κ : Type*} (G : Matrix (Fin N) (Fin N) ℝ)
    (s : Finset κ) (v : κ → Fin N → ℝ) (z : Fin N → ℝ) :
    sourceWork G (∑ i ∈ s, v i) z = ∑ i ∈ s, sourceWork G (v i) z := by
  simp only [sourceWork, sum_dotProduct]

theorem work_sum_right {κ : Type*} (G : Matrix (Fin N) (Fin N) ℝ)
    (s : Finset κ) (v : κ → Fin N → ℝ) (z : Fin N → ℝ) :
    sourceWork G z (∑ i ∈ s, v i) = ∑ i ∈ s, sourceWork G z (v i) := by
  simp only [sourceWork, Matrix.mulVec_sum, dotProduct_sum]

def dualSpan (G : Matrix (Fin N) (Fin N) ℝ) (A : Matrix ι (Fin N) ℝ) :
    Submodule ℝ (Fin N → ℝ) := LinearMap.range (G⁻¹ * Aᵀ).mulVecLin

theorem projected_source_mem (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) : oldSource G hG A c ∈ dualSpan G A := by
  refine ⟨recordInverse G hG A *ᵥ (A *ᵥ c), ?_⟩
  change (G⁻¹ * Aᵀ) *ᵥ (recordInverse G hG A *ᵥ (A *ᵥ c)) = _
  simp only [oldSource, liftMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem projected_source_kernel (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) :
    A *ᵥ (c - oldSource G hG A c) = 0 := by
  rw [Matrix.mulVec_sub, old_source_reading, sub_self]

omit [DecidableEq ι] in
theorem dual_span_kernel_work (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (x z : Fin N → ℝ)
    (hx : x ∈ dualSpan G A) (hz : A *ᵥ z = 0) : sourceWork G x z = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change sourceWork G ((G⁻¹ * Aᵀ) *ᵥ y) z = 0
  rw [work_symm G hG.1]
  unfold sourceWork
  rw [Matrix.mulVec_mulVec]
  have hm : G * (G⁻¹ * Aᵀ) = Aᵀ := by
    rw [← Matrix.mul_assoc, metric_inverse_right G hG, Matrix.one_mul]
  rw [hm, Matrix.dotProduct_transpose_mulVec, hz, dotProduct_zero]

/-- Membership and orthogonal residual uniquely characterize the actual
source-metric projection; the image inverse is constructed, not assumed. -/
theorem projection_unique (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c x : Fin N → ℝ)
    (hx : x ∈ dualSpan G A) (hr : A *ᵥ (c - x) = 0) :
    x = oldSource G hG A c := by
  let d := x - oldSource G hG A c
  have hd : d ∈ dualSpan G A := (dualSpan G A).sub_mem hx (projected_source_mem G hG A c)
  have hk : A *ᵥ d = 0 := by
    have ha : A *ᵥ x = A *ᵥ c := by
      rw [Matrix.mulVec_sub, sub_eq_zero] at hr
      exact hr.symm
    simp only [d, Matrix.mulVec_sub, old_source_reading, ha, sub_self]
  exact sub_eq_zero.mp ((source_work_zero_iff G hG d).mp (dual_span_kernel_work G hG A d d hd hk))

theorem projection_fixes_dual_span (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (x : Fin N → ℝ) (hx : x ∈ dualSpan G A) :
    oldSource G hG A x = x :=
  (projection_unique G hG A x x hx (by simp)).symm

theorem restricted_nested_readback (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) {s t : Finset ι} (hst : s ⊆ t) (c : Fin N → ℝ) :
    restrictedRecord A s *ᵥ oldSource G hG (restrictedRecord A t) c =
      restrictedRecord A s *ᵥ c := by
  ext i
  rw [restricted_reading, restricted_reading]
  by_cases hi : i ∈ s
  · have he := congrFun (old_source_reading G hG (restrictedRecord A t) c) i
    simpa only [restricted_reading, if_pos hi, if_pos (hst hi)] using he
  · simp only [if_neg hi]

theorem empty_projection (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) :
    oldSource G hG (restrictedRecord A ∅) c = 0 := by
  simp only [restricted_empty, oldSource, Matrix.zero_mulVec, Matrix.mulVec_zero]

theorem full_projection_readback (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c : Fin N → ℝ) :
    A *ᵥ (c - oldSource G hG (restrictedRecord A Finset.univ) c) = 0 := by
  rw [restricted_univ]
  exact projected_source_kernel G hG A c

end NField.ResetForests.PrefixGeometry
