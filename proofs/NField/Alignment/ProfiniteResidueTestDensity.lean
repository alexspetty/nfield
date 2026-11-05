/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProfinitePeriodicTesting
import NField.Alignment.CollisionConductorProjection

/-! # Locally constant tests are finite residue tables -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ProfiniteResidueTestDensity

open scoped BigOperators
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary ProfiniteOdometerErgodic
open ProfinitePeriodicTesting CollisionConductorProjection CollisionCylinderMeans

theorem locallyConstant_residue_table (f : LocallyConstant Phase ℝ) :
    ∃ L : ℕ, 0<L ∧ (f : C(Phase,ℝ))=
      residueTableMap L (fun a => f (integerPhase (a : ℤ))) := by
  obtain ⟨L,hL,hperiod⟩ := locallyConstant_integer_period f
  letI : NeZero L := ⟨hL.ne'⟩
  have hp : Function.Periodic (fun z : ℤ => f (integerPhase z)) (L : ℤ) := by
    intro z
    change f (integerPhase (z+(L : ℤ)))=f (integerPhase z)
    rw [integerPhase_add, mul_comm]
    exact hperiod (integerPhase z)
  have hmod (z : ℤ) : f (integerPhase z)=f (integerPhase (((z : ZMod L).val : ℕ) : ℤ)) := by
    rw [ZMod.val_intCast]
    have h := hp.sub_int_mul_eq (x := z) (z/L)
    simpa only [Int.cast_id, Int.emod_def, mul_comm] using h.symm
  refine ⟨L,hL,?_⟩
  apply ContinuousMap.coe_injective
  apply integerPhase_dense.equalizer f.continuous (residueTableMap L _).continuous
  funext z
  change f (integerPhase z)=residueTableMap L (fun a => f (integerPhase (a : ℤ)))
    (integerPhase z)
  rw [residueTableMap_value hL, residue_integer]
  exact hmod z

theorem locallyConstant_residue_expansion (f : LocallyConstant Phase ℝ) :
    ∃ L : ℕ, 0<L ∧ ContinuousMap.toLp 2 phaseHaar ℝ (f : C(Phase,ℝ))=
      ∑ a ∈ Finset.range L, f (integerPhase (a : ℤ)) • residueVector L a := by
  obtain ⟨L,hL,hf⟩ := locallyConstant_residue_table f
  refine ⟨L,hL,?_⟩
  rw [hf]
  simp only [residueTableMap, map_sum, map_smul, residueVector]

theorem residueVector_L2_separates (F : HaarL2)
    (hF : ∀ (L : ℕ), 0<L → ∀ a ∈ Finset.range L, inner ℝ F (residueVector L a)=0) : F=0 := by
  apply ext_inner_right ℝ
  intro V
  have he := locallyConstant_L2_dense.equalizer
    (show Continuous (fun W : HaarL2 => inner ℝ F W) from continuous_const.inner continuous_id)
    (show Continuous (fun W : HaarL2 => inner ℝ (0 : HaarL2) W) from
      continuous_const.inner continuous_id)
  have ht : (fun f : LocallyConstant Phase ℝ =>
      inner ℝ F (ContinuousMap.toLp 2 phaseHaar ℝ (f : C(Phase,ℝ))))=
      (fun f : LocallyConstant Phase ℝ =>
      inner ℝ (0 : HaarL2) (ContinuousMap.toLp 2 phaseHaar ℝ (f : C(Phase,ℝ)))) := by
    funext f
    obtain ⟨L,hL,hf⟩ := locallyConstant_residue_expansion f
    rw [hf, inner_sum, inner_zero_left]
    apply Finset.sum_eq_zero
    intro a ha
    rw [inner_smul_right, hF L hL a ha, mul_zero]
  exact congrFun (he ht) V

end NField.Alignment.ProfiniteResidueTestDensity
