/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralMomentRecurrence
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The closed translation subspace of the actual Haar increment

The space is constructed from integer translates in the real Haar Hilbert
space. Its orthogonal projection commutes with every translation. This
reduces frequency isolation to the odometer's simple eigenspaces.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionTranslationSubspace

open scoped BigOperators
open MeasureTheory CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionPotentialCoboundary CollisionOdometerRecurrence ProfiniteRemainderMeasure

def cyclicSpace (V : HaarL2) : Submodule ℝ HaarL2 :=
  (Submodule.span ℝ (Set.range (fun h : ℤ => shift h V))).topologicalClosure

instance cyclicSpace_complete (V : HaarL2) : CompleteSpace (cyclicSpace V) :=
  inferInstanceAs (CompleteSpace
    ((Submodule.span ℝ (Set.range (fun h : ℤ => shift h V))).topologicalClosure))

theorem translate_mem (V : HaarL2) (h : ℤ) : shift h V ∈ cyclicSpace V :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self h))

theorem self_mem (V : HaarL2) : V ∈ cyclicSpace V := by
  simpa only [shift_zero] using translate_mem V 0

theorem cyclicSpace_shift (V : HaarL2) (h : ℤ) {W : HaarL2}
    (hW : W ∈ cyclicSpace V) : shift h W ∈ cyclicSpace V := by
  let S := Submodule.span ℝ (Set.range (fun z : ℤ => shift z V))
  have hm : S.map (shift h).toLinearMap ≤ S := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_,⟨z,rfl⟩,rfl⟩
    exact ⟨h+z, shift_add h z V⟩
  have hc := (S.topologicalClosure_map (shift h).toContinuousLinearMap).trans
    (Submodule.topologicalClosure_mono hm)
  exact hc ⟨W,hW,rfl⟩

theorem cyclicSpace_projection_shift (V W : HaarL2) (h : ℤ) :
    (cyclicSpace V).starProjection (shift h W) =
      shift h ((cyclicSpace V).starProjection W) := by
  apply (cyclicSpace V).eq_starProjection_of_mem_of_inner_eq_zero
    (cyclicSpace_shift V h (Submodule.starProjection_apply_mem _ _))
  intro Z hZ
  rw [← map_sub]
  have he : shift h (shift (-h) Z)=Z := by rw [← shift_add, add_neg_cancel, shift_zero]
  rw [← he, (shift h).inner_map_map]
  exact (cyclicSpace V).starProjection_inner_eq_zero W _ (cyclicSpace_shift V (-h) hZ)

theorem shift_oneVector (h : ℤ) : shift h oneVector=oneVector := by
  apply Lp.ext
  have ho := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase,ℝ))
  have hot := (translate_measurePreserving h).quasiMeasurePreserving.ae ho
  filter_upwards [shift_coe h oneVector, ho, hot] with x hx hx' htx
  exact hx.trans (htx.trans hx'.symm)

theorem shift_mean_inner (h : ℤ) (V : HaarL2) :
    inner ℝ oneVector (shift h V)=inner ℝ oneVector V := by
  have he := (shift h).inner_map_map oneVector V
  rwa [shift_oneVector] at he

def meanZeroSpace : Submodule ℝ HaarL2 := (ℝ ∙ oneVector)ᗮ

theorem mem_meanZeroSpace (V : HaarL2) :
    V ∈ meanZeroSpace ↔ (∫ x, V x ∂phaseHaar)=0 := by
  rw [meanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_right,
    mean_inner_eq_integral]

theorem incrementVector_mean_inner : inner ℝ oneVector incrementVector=0 := by
  rw [incrementVector, inner_sub_right, shift_mean_inner, sub_self]

theorem increment_cyclicSpace_mean_zero : cyclicSpace incrementVector ≤ meanZeroSpace := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _)
  apply Submodule.span_le.mpr
  rintro _ ⟨h,rfl⟩
  change shift h incrementVector ∈ (ℝ ∙ oneVector)ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    shift_mean_inner, incrementVector_mean_inner]

end NField.Alignment.CollisionTranslationSubspace
