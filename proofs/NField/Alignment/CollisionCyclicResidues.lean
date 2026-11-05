/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCyclicCharacters
import NField.Alignment.CollisionConductorProjection

/-!
# Centered residue indicators in the increment's translation space

Primitive characters sum to the actual Ramanujan rows. Divisor inversion
recovers each centered reset row, and translation places its jump at any
residue. This avoids a separate classification of nonprimitive characters.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCyclicResidues

open scoped BigOperators
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary CollisionOdometerRecurrence
open CollisionTranslationSubspace CollisionCharacterEigenvectors CollisionCyclicCharacters
open CollisionCharacterPairing CollisionParityRows CollisionCylinderMeans
open CollisionConductorProjection CollisionWeightMultiples CollisionRamanujan

theorem ramanujanRow_character_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    ramanujanRow q=∑ a : {a : ℕ // a ∈ primitiveNumerators q}, characterReVector q a.1 := by
  classical
  have hm : ramanujanRowMap q=
      ∑ a : {a : ℕ // a ∈ primitiveNumerators q}, characterReMap q a.1 := by
    ext x
    have h := congrArg Complex.re (ramanujanRowMap_primitiveSum hq x)
    simp only [Complex.ofReal_re, primitiveSum, if_neg (show q ≠ 1 by omega),
      zero_add, Complex.re_sum] at h
    rw [ContinuousMap.sum_apply]
    change ramanujanRowMap q x=∑ a : {a : ℕ // a ∈ primitiveNumerators q},
      (characterMap q a.1 x).re
    rw [Finset.sum_coe_sort (s := primitiveNumerators q)
      (f := fun a : ℕ => (characterMap q a x).re)]
    exact h.trans (by
      apply Finset.sum_congr rfl
      intro a _
      rw [← characterMap_phase])
  rw [ramanujanRow_toLp, hm, map_sum]
  rfl

theorem ramanujanRow_mem {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    ramanujanRow q ∈ cyclicSpace incrementVector := by
  rw [ramanujanRow_character_sum hq]
  apply Submodule.sum_mem
  intro a _
  exact (primitive_character_mem hq (Finset.mem_filter.mp a.2).2).1

theorem resetRow_one : resetRow 1=0 := by
  have hm : residueMap 1 0=(1 : C(Phase,ℝ)) := by
    ext x
    rw [residueMap_eq_value_indicator (by norm_num) (by norm_num)]
    have hv := (residueHom 1 x).toAdd.val_lt
    simp only [show (residueHom 1 x).toAdd.val=0 by omega, if_true, ContinuousMap.one_apply]
  simp only [resetRow, Nat.cast_one, one_smul, residueVector, hm, oneVector, sub_self]

theorem ramanujanRow_one : ramanujanRow 1=0 := by
  simp [ramanujanRow, resetRow_one]

theorem sum_ramanujanRow_divisors {L : ℕ} (hL : 0<L) :
    (∑ q ∈ L.divisors, ramanujanRow q)=resetRow L := by
  exact (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := ramanujanRow) (g := resetRow)).mpr (fun _ _ => rfl) L hL

theorem resetRow_mem {L : ℕ} (hL : 0<L) : resetRow L ∈ cyclicSpace incrementVector := by
  rw [← sum_ramanujanRow_divisors hL]
  apply Submodule.sum_mem
  intro q hq
  have hp := Nat.pos_of_mem_divisors hq
  by_cases hq1 : q=1
  · simp only [hq1, ramanujanRow_one]
    exact Submodule.zero_mem _
  · letI : NeZero q := ⟨hp.ne'⟩
    exact ramanujanRow_mem (by omega)

theorem shifted_residue_zero {L : ℕ} [NeZero L] (a : ℕ) :
    shift (-(a : ℤ)) (residueVector L 0)=residueVector L a := by
  have hL : 0<L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hm : (residueMap L 0).comp (translationMap (-(a : ℤ)))=residueMap L a := by
    ext x
    simp only [ContinuousMap.comp_apply, translationMap, ContinuousMap.coe_mk,
      residueMap, dif_pos hL, residue_translate, Int.cast_neg, Int.cast_natCast,
      Nat.cast_zero]
    have he : -(a : ZMod L)+(residueHom L x).toAdd=0 ↔
        (residueHom L x).toAdd=(a : ZMod L) := by
      constructor
      · intro h
        calc
          _ = (a : ZMod L)+(-(a : ZMod L)+(residueHom L x).toAdd) := by ring
          _ = _ := by rw [h, add_zero]
      · intro h
        rw [h, neg_add_cancel]
    simp only [he]
  rw [residueVector, shift_toLp, hm]
  rfl

theorem centered_residue_mem {L : ℕ} (hL : 0<L) (a : ℕ) :
    residueVector L a-(L : ℝ)⁻¹ • oneVector ∈ cyclicSpace incrementVector := by
  letI : NeZero L := ⟨hL.ne'⟩
  have hs := cyclicSpace_shift incrementVector (-(a : ℤ)) (resetRow_mem hL)
  rw [resetRow, map_sub, map_smul, shifted_residue_zero, shift_oneVector] at hs
  have ht := (cyclicSpace incrementVector).smul_mem ((L : ℝ)⁻¹) hs
  have hLR : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ hLR, one_smul] using ht

end NField.Alignment.CollisionCyclicResidues
