/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityShallowSpine

/-! # Sharp shallow unity forcing in the actual native space -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySharpSpine
open scoped BigOperators
open UnityNativeHilbert UnityNativeIsometry UnitySpineBasis UnitySpineExpansion UnityShallowSpine

def tailMass (H : ℕ) : ℝ := (1/2:ℝ)^H
def headMass (H : ℕ) : ℝ := 1-tailMass H
def normalizedHead (H : ℕ) : NativeHilbert := (Real.sqrt (headMass H))⁻¹ • head H
def centeredHead (H : ℕ) : NativeHilbert := normalizedHead H-Real.sqrt (headMass H) • unity

theorem tailMass_pos (H : ℕ) : 0<tailMass H := by unfold tailMass; positivity
theorem headMass_pos {H : ℕ} (hH : 0<H) : 0<headMass H := by
  have h : (1/2:ℝ)^H<1 := pow_lt_one₀ (by norm_num) (by norm_num) hH.ne'
  exact sub_pos.mpr h

theorem head_norm (H : ℕ) : ‖head H‖=Real.sqrt (headMass H) := by
  unfold headMass tailMass
  rw [← head_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem normalizedHead_norm {H : ℕ} (hH : 0<H) : ‖normalizedHead H‖=1 := by
  rw [normalizedHead, norm_smul, head_norm, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_mul_cancel₀ (Real.sqrt_pos.mpr (headMass_pos hH)).ne']

theorem unity_normalizedHead {H : ℕ} (hH : 0<H) :
    inner ℝ unity (normalizedHead H)=Real.sqrt (headMass H) := by
  rw [normalizedHead, real_inner_smul_right, unity_head_inner]
  change (Real.sqrt (headMass H))⁻¹*headMass H=Real.sqrt (headMass H)
  have hs := Real.sq_sqrt (headMass_pos hH).le
  have hn : Real.sqrt (headMass H)≠0 := (Real.sqrt_pos.mpr (headMass_pos hH)).ne'
  field_simp
  nlinarith

theorem unity_centeredHead {H : ℕ} (hH : 0<H) : inner ℝ unity (centeredHead H)=0 := by
  rw [centeredHead, inner_sub_right, unity_normalizedHead hH, real_inner_smul_right,
    real_inner_self_eq_norm_sq, unity_norm_sq]
  ring

theorem centeredHead_norm_sq {H : ℕ} (hH : 0<H) : ‖centeredHead H‖^2=tailMass H := by
  rw [centeredHead, norm_sub_sq_real, normalizedHead_norm hH, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (headMass_pos hH).le, unity_norm_sq,
    real_inner_smul_right, real_inner_comm, unity_normalizedHead hH]
  have hs := Real.sq_sqrt (headMass_pos hH).le
  unfold headMass at *
  nlinarith

theorem centered_residual_norm (F : NativeHilbert) (D : ℝ)
    (henergy : ‖F‖^2=D) (hmean : inner ℝ F unity=D) :
    ‖F-D • unity‖^2=D*(1-D) := by
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, unity_norm_sq,
    henergy, real_inner_smul_right, hmean]
  ring

theorem centered_residual_mean (F : NativeHilbert) (D : ℝ) (hmean : inner ℝ F unity=D) :
    inner ℝ (F-D • unity) unity=0 := by
  rw [inner_sub_left, hmean, real_inner_smul_left, real_inner_self_eq_norm_sq, unity_norm_sq]
  ring

/-- Title: `The native normalized head has the exact sharp signed lower response`.

 The normalized native head retains the exact sharp signed lower response. -/
theorem normalized_head_response (F : NativeHilbert) (D : ℝ) (H : ℕ) (hH : 0<H)
    (henergy : ‖F‖^2=D) (hmean : inner ℝ F unity=D) :
    D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))≤
      inner ℝ F (normalizedHead H) := by
  have hc := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm (F-D • unity) (centeredHead H))
  rw [sq_abs, mul_pow, centered_residual_norm F D henergy hmean, centeredHead_norm_sq hH] at hc
  have habs : |inner ℝ (F-D • unity) (centeredHead H)|≤
      Real.sqrt (tailMass H*D*(1-D)) := Real.abs_le_sqrt (by nlinarith [hc])
  have hlo := (neg_le_of_abs_le habs)
  rw [centeredHead, inner_sub_right, real_inner_smul_right,
    centered_residual_mean F D hmean, mul_zero, sub_zero,
    inner_sub_left, real_inner_smul_left, unity_normalizedHead hH] at hlo
  linarith

theorem normalized_head_energy_le (F : NativeHilbert) (H : ℕ) (hH : 0<H) :
    (inner ℝ F (normalizedHead H))^2≤spineEnergy F H := by
  have h := head_pairing_sq_le F H
  have hA := headMass_pos hH
  have hs := Real.sq_sqrt hA.le
  have hn : Real.sqrt (headMass H)≠0 := (Real.sqrt_pos.mpr hA).ne'
  have he : (inner ℝ F (normalizedHead H))^2=(inner ℝ F (head H))^2/headMass H := by
    rw [normalizedHead, real_inner_smul_right, mul_pow, inv_pow, hs]
    ring
  rw [he]
  apply (div_le_iff₀ hA).mpr
  simpa only [headMass, tailMass, mul_comm] using h

/-- Title: `The sharp shallow unity-forcing inequality`.

 The paper's exact sharp forcing inequality for the actual native spine. -/
theorem sharp_spine_forcing (F : NativeHilbert) (D : ℝ) (H : ℕ) (hH : 0<H)
    (henergy : ‖F‖^2=D) (hmean : inner ℝ F unity=D) :
    (max (D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))) 0)^2≤spineEnergy F H := by
  have hl := normalized_head_response F D H hH henergy hmean
  have hm : max (D*Real.sqrt (headMass H)-Real.sqrt (tailMass H*D*(1-D))) 0≤
      |inner ℝ F (normalizedHead H)| := max_le (hl.trans (le_abs_self _)) (abs_nonneg _)
  have hs := (sq_le_sq₀ (le_max_right _ _) (abs_nonneg _)).mpr hm
  rw [sq_abs] at hs
  exact hs.trans (normalized_head_energy_le F H hH)

end NField.Alignment.UnitySharpSpine
