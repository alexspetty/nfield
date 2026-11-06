/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitySharpSpine

/-! # An actual unit tail direction perpendicular to native unity -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySpineTailDirection
open scoped BigOperators
open UnityNativeHilbert UnityNativeIsometry UnitySpineBasis UnitySpineExpansion
open UnityShallowSpine UnitySharpSpine

theorem head_later_spine_inner {H h : ℕ} (hh : H≤h) : inner ℝ (head H) (spine h)=0 := by
  rw [head, sum_inner]
  apply Finset.sum_eq_zero
  intro k hk
  rw [real_inner_smul_left, spine_orthonormal.inner_eq_zero (by have := Finset.mem_range.mp hk; omega), mul_zero]

theorem tail_first_spine_inner (H : ℕ) : inner ℝ (tail H) (spine H)=coefficient H := by
  have he := congrArg (fun F : NativeHilbert => inner ℝ F (spine H)) (head_add_tail H)
  rw [inner_add_left, head_later_spine_inner (le_refl H), unity_spine_inner, zero_add] at he
  exact he

theorem coefficient_tailMass (H : ℕ) : (coefficient H)^2=tailMass H/2 := by
  rw [coefficient_sq, pow_succ]
  unfold tailMass
  ring

/-- A concrete unit vector in the tail spine with zero signed unity reading. -/
def tailDirection (H : ℕ) : NativeHilbert :=
  Real.sqrt 2 • (spine H-(coefficient H/tailMass H) • tail H)

theorem unity_tailDirection_inner (H : ℕ) : inner ℝ unity (tailDirection H)=0 := by
  rw [tailDirection, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    unity_spine_inner, unity_tail_inner]
  change Real.sqrt 2*(coefficient H-coefficient H/tailMass H*tailMass H)=0
  rw [div_mul_cancel₀ _ (tailMass_pos H).ne', sub_self, mul_zero]

theorem tail_tailDirection_inner (H : ℕ) : inner ℝ (tail H) (tailDirection H)=0 := by
  rw [tailDirection, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    tail_first_spine_inner, real_inner_self_eq_norm_sq, tail_norm_sq]
  change Real.sqrt 2*(coefficient H-coefficient H/tailMass H*tailMass H)=0
  rw [div_mul_cancel₀ _ (tailMass_pos H).ne', sub_self, mul_zero]

/-- Title: `A concrete transverse tail-spine direction has unit native energy`. -/
theorem tailDirection_norm_sq (H : ℕ) : ‖tailDirection H‖^2=1 := by
  rw [tailDirection, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2), norm_sub_sq_real,
    spine_norm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    tail_norm_sq, real_inner_smul_right, real_inner_comm, tail_first_spine_inner]
  simp only [one_pow]
  change 2*(1-2*(coefficient H/tailMass H*coefficient H)+
    (coefficient H/tailMass H)^2*tailMass H)=1
  have hc := coefficient_tailMass H
  have ht := tailMass_pos H
  field_simp
  nlinarith

theorem tailDirection_head_spine (H h : ℕ) (hh : h<H) :
    inner ℝ (tailDirection H) (spine h)=0 := by
  rw [tailDirection, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    spine_orthonormal.inner_eq_zero (by omega : H≠h), tail_spine_inner H h hh]
  ring

/-- Title: `The equality construction in the tail has zero shallow energy`.

 A vector formed entirely from these two tail directions has no shallow spine energy. -/
theorem tail_combination_energy (H : ℕ) (a b : ℝ) :
    spineEnergy (a • tail H+b • tailDirection H) H=0 := by
  apply Finset.sum_eq_zero
  intro h hh
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    tail_spine_inner H h (Finset.mem_range.mp hh),
    tailDirection_head_spine H h (Finset.mem_range.mp hh)]
  norm_num

theorem parallel_head_energy (H : ℕ) (a b : ℝ) :
    spineEnergy (a • unity+b • head H) H=(a+b)^2*headMass H := by
  calc
    spineEnergy (a • unity+b • head H) H =
        ∑ h∈Finset.range H, (a+b)^2*(coefficient h)^2 := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        unity_spine_inner, head_spine_inner H h (Finset.mem_range.mp hh), sq_abs]
      ring
    _ = (a+b)^2*headMass H := by rw [← Finset.mul_sum, coefficient_sq_sum]; rfl

theorem head_normalizedHead_inner {H : ℕ} (hH : 0<H) :
    inner ℝ (head H) (normalizedHead H)=Real.sqrt (headMass H) := by
  rw [head_eq_unity_sub_tail, inner_sub_left, unity_normalizedHead hH,
    normalizedHead, real_inner_smul_right, tail_head_inner, mul_zero, sub_zero]

theorem parallel_head_exact (H : ℕ) (hH : 0<H) (a b : ℝ) :
    spineEnergy (a • unity+b • head H) H=
      (inner ℝ (a • unity+b • head H) (normalizedHead H))^2 := by
  rw [parallel_head_energy, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    unity_normalizedHead hH, head_normalizedHead_inner hH]
  have hs := Real.sq_sqrt (headMass_pos hH).le
  nlinarith

end NField.Alignment.UnitySpineTailDirection
