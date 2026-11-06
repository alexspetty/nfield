/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitySpineTailDirection

/-! # Equality witnesses for the sharp native shallow-spine estimate -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySpineAttainment
open UnityNativeHilbert UnityNativeIsometry UnitySpineBasis UnitySpineExpansion
open UnityShallowSpine UnitySharpSpine UnitySpineTailDirection

def highFactor (D : ℝ) (H : ℕ) : ℝ := Real.sqrt (D*(1-D)/tailMass H)
def highVector (D : ℝ) (H : ℕ) : NativeHilbert := D • unity-highFactor D H • centeredHead H
def lowVector (D : ℝ) (H : ℕ) : NativeHilbert :=
  (D/tailMass H) • tail H+Real.sqrt (D-D^2/tailMass H) • tailDirection H

theorem highFactor_sq (D : ℝ) (H : ℕ) (hD0 : 0≤D) (hD1 : D≤1) :
    (highFactor D H)^2=D*(1-D)/tailMass H :=
  Real.sq_sqrt (div_nonneg (mul_nonneg hD0 (sub_nonneg.mpr hD1)) (tailMass_pos H).le)

/-- Title: `The upper-regime equality witness has the required unity reading`. -/
theorem highVector_mean (D : ℝ) (H : ℕ) (hH : 0<H) : inner ℝ (highVector D H) unity=D := by
  rw [highVector, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, unity_norm_sq, real_inner_comm, unity_centeredHead hH]
  ring

/-- Title: `The upper-regime equality witness has the required native energy`. -/
theorem highVector_norm_sq (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0≤D) (hD1 : D≤1) :
    ‖highVector D H‖^2=D := by
  rw [highVector, norm_sub_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, unity_norm_sq,
    centeredHead_norm_sq hH, highFactor_sq D H hD0 hD1, real_inner_smul_left,
    real_inner_smul_right, unity_centeredHead hH,
    div_mul_cancel₀ _ (tailMass_pos H).ne']
  ring

theorem centeredHead_normalizedHead (H : ℕ) (hH : 0<H) :
    inner ℝ (centeredHead H) (normalizedHead H)=tailMass H := by
  rw [centeredHead, inner_sub_left, real_inner_self_eq_norm_sq, normalizedHead_norm hH,
    real_inner_smul_left, unity_normalizedHead hH]
  have hs := Real.sq_sqrt (headMass_pos hH).le
  unfold headMass at *
  nlinarith

theorem highFactor_times_tail (D : ℝ) (H : ℕ) (hD0 : 0≤D) (hD1 : D≤1) :
    highFactor D H*tailMass H=Real.sqrt (tailMass H*D*(1-D)) := by
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (tailMass_pos H).le)
    (Real.sqrt_nonneg _)).mp
  change (highFactor D H*tailMass H)^2=Real.sqrt (tailMass H*D*(1-D))^2
  rw [mul_pow, highFactor_sq D H hD0 hD1,
    Real.sq_sqrt (mul_nonneg (mul_nonneg (tailMass_pos H).le hD0) (sub_nonneg.mpr hD1))]
  field_simp

theorem highVector_response (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0≤D) (hD1 : D≤1) :
    inner ℝ (highVector D H) (normalizedHead H)=
      D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D)) := by
  rw [highVector, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    unity_normalizedHead hH, centeredHead_normalizedHead H hH,
    highFactor_times_tail D H hD0 hD1]

theorem sharp_expression_nonneg (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0≤D)
    (htD : tailMass H≤D) :
    0≤D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D)) := by
  have hs := Real.sq_sqrt (headMass_pos hH).le
  apply sub_nonneg.mpr
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hD0 (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, hs]
  unfold headMass
  nlinarith [mul_nonneg hD0 (sub_nonneg.mpr htD)]

/-- Title: `The upper-regime native vector attains sharp shallow forcing`. -/
theorem highVector_attains (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0≤D) (hD1 : D≤1)
    (htD : tailMass H≤D) :
    spineEnergy (highVector D H) H=
      (max (D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))) 0)^2 := by
  have he : highVector D H=(D+highFactor D H*Real.sqrt (headMass H)) • unity+
      (-highFactor D H*(Real.sqrt (headMass H))⁻¹) • head H := by
    unfold highVector centeredHead normalizedHead
    module
  rw [he, parallel_head_exact H hH, ← he, highVector_response D H hH hD0 hD1,
    max_eq_left (sharp_expression_nonneg D H hH hD0 htD)]

theorem low_radical_nonneg (D : ℝ) (H : ℕ) (hD0 : 0≤D) (hDt : D≤tailMass H) :
    0≤D-D^2/tailMass H := by
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (tailMass_pos H)).mpr
  nlinarith

/-- Title: `The tail equality witness has the required unity reading`. -/
theorem lowVector_mean (D : ℝ) (H : ℕ) : inner ℝ (lowVector D H) unity=D := by
  have ht : inner ℝ (tail H) unity=tailMass H := by
    rw [real_inner_comm]
    exact unity_tail_inner H
  have hz : inner ℝ (tailDirection H) unity=0 := by
    rw [real_inner_comm]
    exact unity_tailDirection_inner H
  rw [lowVector, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    ht, hz]
  change D/tailMass H*tailMass H+Real.sqrt (D-D^2/tailMass H)*0=D
  rw [div_mul_cancel₀ _ (tailMass_pos H).ne', mul_zero, add_zero]

/-- Title: `The tail equality witness has the required native energy`. -/
theorem lowVector_norm_sq (D : ℝ) (H : ℕ) (hD0 : 0≤D) (hDt : D≤tailMass H) :
    ‖lowVector D H‖^2=D := by
  rw [lowVector, norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, tail_norm_sq,
    tailDirection_norm_sq, Real.sq_sqrt (low_radical_nonneg D H hD0 hDt),
    real_inner_smul_left, real_inner_smul_right, tail_tailDirection_inner]
  change (D/tailMass H)^2*tailMass H+
    2*(D/tailMass H*(Real.sqrt (D-D^2/tailMass H)*0))+(D-D^2/tailMass H)*1=D
  field_simp
  ring

theorem sharp_expression_nonpos (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0≤D)
    (hDt : D≤tailMass H) :
    D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))≤0 := by
  apply sub_nonpos.mpr
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt (headMass_pos hH).le]
  unfold headMass
  nlinarith [mul_nonneg hD0 (sub_nonneg.mpr hDt)]

/-- Title: `The tail native vector attains sharp shallow forcing`. -/
theorem lowVector_attains (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0≤D) (hDt : D≤tailMass H) :
    spineEnergy (lowVector D H) H=
      (max (D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))) 0)^2 := by
  rw [lowVector, tail_combination_energy, max_eq_right (sharp_expression_nonpos D H hH hD0 hDt)]
  norm_num

/-- Title: `Equality in sharp forcing is attained by actual native vectors`.

 Equality in the sharp forcing bound is attained by actual native Hilbert vectors. -/
theorem sharp_spine_equality_attainable (D : ℝ) (H : ℕ) (hH : 0<H)
    (hD0 : 0≤D) (hD1 : D≤1) :
    ∃F : NativeHilbert, ‖F‖^2=D ∧ inner ℝ F unity=D ∧
      spineEnergy F H=(max (D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))) 0)^2 := by
  rcases le_total (tailMass H) D with htD|hDt
  · exact ⟨highVector D H, highVector_norm_sq D H hH hD0 hD1,
      highVector_mean D H hH, highVector_attains D H hH hD0 hD1 htD⟩
  · exact ⟨lowVector D H, lowVector_norm_sq D H hD0 hDt,
      lowVector_mean D H, lowVector_attains D H hH hD0 hDt⟩

end NField.Alignment.UnitySpineAttainment
