/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorProjection
import Mathlib.Analysis.Fourier.ZMod

/-!
# Complete additive character space for the conductor projection

Every real and imaginary character direction on each quotient of period
at most Q is retained. Finite Fourier inversion identifies their span
with the residue-indicator subspace used for the orthogonal projection.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorFourierSpace

open scoped BigOperators Classical
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionJordanVariance CollisionConductorRows CollisionCylinderMeans
open CollisionConductorProjection

def characterPartMap (L : ℕ) (hL : 0<L) (j : ZMod L) (c : ℂ) : C(Phase,ℝ) := by
  letI : NeZero L := ⟨hL.ne'⟩
  exact residueTableMap L (fun a => (c*ZMod.stdAddChar (j*(a : ZMod L))).re)

def characterPartVector (L : ℕ) (hL : 0<L) (j : ZMod L) (c : ℂ) : HaarL2 :=
  ContinuousMap.toLp 2 phaseHaar ℝ (characterPartMap L hL j c)

theorem characterPartMap_value (L : ℕ) (hL : 0<L) (j : ZMod L) (c : ℂ) (x : Phase) :
    letI : NeZero L := ⟨hL.ne'⟩
    characterPartMap L hL j c x=(c*ZMod.stdAddChar (j*(residueHom L x).toAdd)).re := by
  letI : NeZero L := ⟨hL.ne'⟩
  rw [characterPartMap,residueTableMap_value hL,ZMod.natCast_zmod_val]

def additiveConductorSpace (Q : ℕ) : Submodule ℝ HaarL2 :=
  Submodule.span ℝ {v | ∃ (L : ℕ) (hL : 0<L) (j : ZMod L) (c : ℂ),
    L≤Q ∧ v=characterPartVector L hL j c}

theorem characterPartVector_mem {L Q : ℕ} (hL : 0<L) (hLQ : L≤Q)
    (j : ZMod L) (c : ℂ) : characterPartVector L hL j c∈additiveConductorSpace Q := by
  apply Submodule.subset_span
  exact ⟨L,hL,j,c,hLQ,rfl⟩

theorem characterPartVector_mem_residueSpace {L Q : ℕ} (hL : 0<L) (hLQ : L≤Q)
    (j : ZMod L) (c : ℂ) : characterPartVector L hL j c∈conductorSpace Q := by
  letI : NeZero L := ⟨hL.ne'⟩
  simp only [characterPartVector,characterPartMap,residueTableMap,map_sum,map_smul]
  apply Submodule.sum_mem
  intro a ha
  exact (conductorSpace Q).smul_mem _
    (residueVector_mem_conductorSpace hLQ (Finset.mem_range.mp ha))

theorem residueMap_character_expansion {L a : ℕ} (hL : 0<L) (ha : a<L) :
    letI : NeZero L := ⟨hL.ne'⟩
    residueMap L a=∑ j : ZMod L, characterPartMap L hL j
      ((L : ℂ)⁻¹*ZMod.dft (fun b : ZMod L => if b.val=a then (1 : ℂ) else 0) j) := by
  letI : NeZero L := ⟨hL.ne'⟩
  let f : ZMod L → ℂ := fun b => if b.val=a then 1 else 0
  ext x
  let r : ZMod L := (residueHom L x).toAdd
  have hi := congrFun ((ZMod.dft (N := L) (E := ℂ)).symm_apply_apply f) r
  rw [ZMod.invDFT_apply] at hi
  simp only [smul_eq_mul] at hi
  calc
    residueMap L a x=(f r).re := by
      rw [residueMap_eq_value_indicator hL ha]
      dsimp [f,r]
      split_ifs <;> rfl
    _ = ((L : ℂ)⁻¹*∑ j : ZMod L, ZMod.stdAddChar (j*r)*ZMod.dft f j).re :=
      congrArg Complex.re hi.symm
    _ = ∑ j : ZMod L, (((L : ℂ)⁻¹*ZMod.dft f j)*ZMod.stdAddChar (j*r)).re := by
      rw [Finset.mul_sum,Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ = _ := by
      simp only [ContinuousMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [characterPartMap_value]

theorem residueVector_character_expansion {L a : ℕ} (hL : 0<L) (ha : a<L) :
    letI : NeZero L := ⟨hL.ne'⟩
    residueVector L a=∑ j : ZMod L, characterPartVector L hL j
      ((L : ℂ)⁻¹*ZMod.dft (fun b : ZMod L => if b.val=a then (1 : ℂ) else 0) j) := by
  letI : NeZero L := ⟨hL.ne'⟩
  rw [residueVector,residueMap_character_expansion hL ha,map_sum]
  rfl

theorem conductorSpace_eq_additiveConductorSpace (Q : ℕ) :
    conductorSpace Q=additiveConductorSpace Q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hL : 0 < i.1.val := by have := i.2.isLt; omega
    have hLQ : i.1.val≤Q := by have := i.1.isLt; omega
    unfold conductorGenerator
    rw [residueVector_character_expansion hL i.2.isLt]
    apply Submodule.sum_mem
    intro j _
    exact characterPartVector_mem hL hLQ j _
  · apply Submodule.span_le.mpr
    rintro v ⟨L,hL,j,c,hLQ,rfl⟩
    exact characterPartVector_mem_residueSpace hL hLQ j c

instance additiveConductorSpace_finiteDimensional (Q : ℕ) :
    FiniteDimensional ℝ (additiveConductorSpace Q) := by
  rw [← conductorSpace_eq_additiveConductorSpace]
  infer_instance

theorem additive_conductor_projection (Q : ℕ) :
    (additiveConductorSpace Q).starProjection collisionPotential=weightedRows amplitude Q := by
  apply (additiveConductorSpace Q).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← conductorSpace_eq_additiveConductorSpace]
    exact weightedRows_mem_conductorSpace Q
  · intro v hv
    apply cutoff_residual_inner_conductorSpace Q v
    rwa [conductorSpace_eq_additiveConductorSpace]

theorem additive_conductor_tail {Q : ℕ} (hQ : 1≤Q) :
    ‖collisionPotential-(additiveConductorSpace Q).starProjection collisionPotential‖^2=
      (1/27 : ℝ)*∑' q : ℕ, if Q<q then jordanTwo q*(amplitude q)^2 else 0 := by
  rw [additive_conductor_projection]
  simpa only [conductorSpace_projection] using conductor_projection_tail_ge_one hQ

end NField.Alignment.CollisionConductorFourierSpace
