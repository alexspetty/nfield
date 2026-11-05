/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacterPairing

/-!
# Isolating every primitive character in the translation span

Projection commutes with translation. Ergodicity forces a projected
cosine/sine pair to be a scalar multiple of the original pair. Its pairing
with the increment fixes that scalar to one because the amplitude is positive.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCyclicCharacters

open CollisionPotentialHilbert CollisionPotentialCoboundary CollisionOdometerRecurrence
open CollisionCharacterEigenvectors CollisionCharacterPairing CollisionTranslationSubspace
open CollisionSpectralSupport CollisionJordanVariance

theorem primitive_character_mem {q a : ℕ} [NeZero q] (hq : 2 ≤ q) (ha : a.Coprime q) :
    characterReVector q a ∈ cyclicSpace incrementVector ∧
      characterImVector q a ∈ cyclicSpace incrementVector := by
  let S := cyclicSpace incrementVector
  let U := S.starProjection (characterReVector q a)
  let W := S.starProjection (characterImVector q a)
  have hU : shift 1 U=(characterRoot q a).re • U-(characterRoot q a).im • W := by
    change shift 1 (S.starProjection (characterReVector q a))=_
    rw [← cyclicSpace_projection_shift, characterReVector_shift, map_sub, map_smul, map_smul]
  have hW : shift 1 W=(characterRoot q a).im • U+(characterRoot q a).re • W := by
    change shift 1 (S.starProjection (characterImVector q a))=_
    rw [← cyclicSpace_projection_shift, characterImVector_shift, map_add, map_smul, map_smul]
  obtain ⟨c,hcU,hcW⟩ := character_eigenpair_vectors q a U W hU hW
  have hfixed : S.starProjection incrementVector=incrementVector :=
    Submodule.starProjection_eq_self_iff.mpr (self_mem incrementVector)
  have hru : inner ℝ incrementVector U=inner ℝ incrementVector (characterReVector q a) := by
    change inner ℝ incrementVector (S.starProjection (characterReVector q a))=_
    rw [← S.inner_starProjection_left_eq_right, hfixed]
  have hiw : inner ℝ incrementVector W=inner ℝ incrementVector (characterImVector q a) := by
    change inner ℝ incrementVector (S.starProjection (characterImVector q a))=_
    rw [← S.inner_starProjection_left_eq_right, hfixed]
  obtain ⟨hr,hi⟩ := increment_character_pair hq ha
  have hn : -2*amplitude q/3 ≠ 0 := by
    have hp := amplitude_pos hq
    positivity
  rw [hcU, inner_sub_right, inner_smul_right, inner_smul_right, hr, hi,
    mul_zero, sub_zero] at hru
  rw [hcW, inner_add_right, inner_smul_right, inner_smul_right, hr, hi,
    mul_zero, add_zero] at hiw
  have hcr : c.re=1 := (mul_right_cancel₀ hn) (by simpa using hru)
  have hci : c.im=0 := (mul_eq_zero.mp hiw).resolve_right hn
  rw [hcr,hci,one_smul,zero_smul,sub_zero] at hcU
  rw [hcr,hci,one_smul,zero_smul,zero_add] at hcW
  exact ⟨hcU ▸ S.starProjection_apply_mem _, hcW ▸ S.starProjection_apply_mem _⟩

end NField.Alignment.CollisionCyclicCharacters
