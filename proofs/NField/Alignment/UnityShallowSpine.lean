/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitySpineExpansion
import NField.Alignment.UnityHorizonBounds

/-! # The actual residual has quantitatively visible shallow spine energy -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityShallowSpine
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection UnityNativeIsometry UnitySpineBasis UnitySpineExpansion
open UnityPrescribedDetectors UnityDetectorHorizon UnityHorizonBounds

def spineEnergy (F : NativeHilbert) (H : ℕ) : ℝ :=
  ∑ h∈Finset.range H, |inner ℝ F (spine h)|^2

theorem spineEnergy_nonneg (F : NativeHilbert) (H : ℕ) : 0≤spineEnergy F H :=
  Finset.sum_nonneg (fun h _ => sq_nonneg _)

theorem head_pairing_sq_le (F : NativeHilbert) (H : ℕ) :
    (inner ℝ F (head H))^2≤(1-(1/2:ℝ)^H)*spineEnergy F H := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range H) coefficient
    (fun h => inner ℝ F (spine h))
  rw [coefficient_sq_sum] at h
  simpa only [head, inner_sum, real_inner_smul_right, spineEnergy, sq_abs] using h

theorem tail_pairing_bound (F : NativeHilbert) (H : ℕ) :
    |inner ℝ F (tail H)|≤Real.sqrt ((1/2:ℝ)^H*‖F‖^2) := by
  apply Real.abs_le_sqrt
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm F (tail H))
  simpa only [sq_abs, mul_pow, tail_norm_sq, mul_comm] using h

theorem head_pairing_lower (F : NativeHilbert) (D : ℝ) (H : ℕ)
    (henergy : ‖F‖^2=D) (hmean : inner ℝ F unity=D) :
    D-Real.sqrt ((1/2:ℝ)^H*D) ≤ inner ℝ F (head H) := by
  have ht := tail_pairing_bound F H
  rw [henergy] at ht
  have he := congrArg (fun f : NativeHilbert => inner ℝ F f) (head_add_tail H)
  rw [inner_add_right, hmean] at he
  have hu := (le_abs_self (inner ℝ F (tail H))).trans ht
  linarith

/-- Title: `The full native head and tail give the displayed energy certificate`.

 The literal head/tail certificate, with the complete native tail retained. -/
theorem head_tail_energy_lower (F : NativeHilbert) (D : ℝ) (H : ℕ) (hH : 0<H)
    (henergy : ‖F‖^2=D) (hmean : inner ℝ F unity=D) :
    (max (D-Real.sqrt ((1/2:ℝ)^H*D)) 0)^2/(1-(1/2:ℝ)^H)≤spineEnergy F H := by
  have hpow : (1/2:ℝ)^H<1 := pow_lt_one₀ (by norm_num) (by norm_num) hH.ne'
  have hl := head_pairing_lower F D H henergy hmean
  have hm : max (D-Real.sqrt ((1/2:ℝ)^H*D)) 0≤|inner ℝ F (head H)| :=
    max_le (hl.trans (le_abs_self _)) (abs_nonneg _)
  have hs := (sq_le_sq₀ (le_max_right _ _) (abs_nonneg _)).mpr hm
  rw [sq_abs] at hs
  apply (div_le_iff₀ (by linarith : 0<1-(1/2:ℝ)^H)).mpr
  simpa only [mul_comm] using hs.trans (head_pairing_sq_le F H)

/-- Title: `The actual shallow residual obeys the precise quarter-deficit bound`.

 The exact displayed quarter-deficit lower bound at the intrinsic shallow horizon. -/
theorem prescribed_shallow_energy (N : ℕ) :
    (deficit N)^2/(4*(1-(1/2:ℝ)^(horizon N)))≤
      spineEnergy (UnityNativeHilbert.residual N) (horizon N) := by
  have hD := deficit_pos N
  have ht := horizon_tail_bound N
  have hH : 0<horizon N := by have := horizon_ge_two N; omega
  have hpow : (1/2:ℝ)^(horizon N)<1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hH.ne'
  have hsqrt : Real.sqrt ((1/2:ℝ)^(horizon N)*deficit N)≤deficit N/2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h := mul_le_mul_of_nonneg_right ht hD.le
    nlinarith
  have hl := head_pairing_lower (UnityNativeHilbert.residual N) (deficit N) (horizon N)
    rfl (residual_inner_unity N)
  have hh : deficit N/2 ≤ inner ℝ (UnityNativeHilbert.residual N) (head (horizon N)) := by linarith
  have hh0 : 0 ≤ inner ℝ (UnityNativeHilbert.residual N) (head (horizon N)) := by linarith
  have hsq := (sq_le_sq₀ (by positivity : (0:ℝ)≤deficit N/2) hh0).mpr hh
  have hc := head_pairing_sq_le (UnityNativeHilbert.residual N) (horizon N)
  apply (div_le_iff₀ (by positivity : 0<4*(1-(1/2:ℝ)^(horizon N)))).mpr
  nlinarith

/-- Title: `At least one quarter of squared deficit is visible on the shallow spine`. -/
theorem prescribed_shallow_quarter (N : ℕ) :
    (deficit N)^2/4≤spineEnergy (UnityNativeHilbert.residual N) (horizon N) := by
  have hh := prescribed_shallow_energy N
  have hH : 0<horizon N := by have := horizon_ge_two N; omega
  have hp : (1/2:ℝ)^(horizon N)<1 := pow_lt_one₀ (by norm_num) (by norm_num) hH.ne'
  have ht : 0≤(1/2:ℝ)^(horizon N) := by positivity
  exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (by nlinarith : 4*(1-(1/2:ℝ)^(horizon N))≤4)).trans hh

end NField.Alignment.UnityShallowSpine
