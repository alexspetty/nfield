/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCyclicResidues
import NField.Alignment.ProfiniteResidueTestDensity

/-! # Translates of the increment span the whole mean-zero Haar space -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIncrementCyclicity

open MeasureTheory CollisionPotentialHilbert CollisionPotentialConvergence CollisionOdometerRecurrence
open CollisionPotentialCoboundary
open CollisionTranslationSubspace CollisionCyclicResidues ProfiniteResidueTestDensity

theorem increment_cyclicSpace_eq_meanZeroSpace : cyclicSpace incrementVector=meanZeroSpace := by
  apply le_antisymm increment_cyclicSpace_mean_zero
  intro V hV
  let S := cyclicSpace incrementVector
  let R := V-S.starProjection V
  have hRS : R ∈ Sᗮ := S.sub_starProjection_mem_orthogonal V
  have hRM : R ∈ meanZeroSpace := meanZeroSpace.sub_mem hV
    (increment_cyclicSpace_mean_zero (S.starProjection_apply_mem V))
  have hRone : inner ℝ R oneVector=0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hRM
  have hRzero : R=0 := by
    apply residueVector_L2_separates
    intro L hL a _
    have h := Submodule.inner_left_of_mem_orthogonal (centered_residue_mem hL a) hRS
    rwa [inner_sub_right, inner_smul_right, hRone, mul_zero, sub_zero] at h
  have he : V=S.starProjection V := sub_eq_zero.mp hRzero
  rw [he]
  exact S.starProjection_apply_mem V

theorem literal_increment_cyclic_span (V : HaarL2) :
    V ∈ cyclicSpace incrementVector ↔
      (∫ x, V x ∂ProfiniteRemainderMeasure.phaseHaar)=0 := by
  rw [increment_cyclicSpace_eq_meanZeroSpace, mem_meanZeroSpace]

end NField.Alignment.CollisionIncrementCyclicity
