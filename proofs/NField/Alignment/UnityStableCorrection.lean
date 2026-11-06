/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityGramPseudoinverse

/-! # Native gain certified by uncertain signed readings -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityStableCorrection
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection UnityFiniteGram UnityGramPseudoinverse
variable {ι : Type*} [Fintype ι]

/-- The source's thresholded correction coefficient. -/
def correctionScale (C ε R : ℝ) : ℝ := if ε<R then C⁻¹*(1-ε/R) else 0

/-- A measured reading vector retains its signed lower response under a norm error bound. -/
theorem measured_response_lower (b measured : EuclideanSpace ℝ ι) (ε : ℝ)
    (he : ‖measured-b‖≤ε) :
    ‖measured‖^2-ε*‖measured‖ ≤ inner ℝ b measured := by
  have hi := real_inner_le_norm (measured-b) measured
  have he' := mul_le_mul_of_nonneg_right he (norm_nonneg measured)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hi
  linarith

/-- Exact scalar accounting for the thresholded correction. -/
theorem correction_scalar_identity (C ε R : ℝ) (hC : 0<C) (he : ε<R) (hε : 0≤ε) :
    2*correctionScale C ε R*(R^2-ε*R)-
      (correctionScale C ε R)^2*C*R^2 = (R-ε)^2/C := by
  have hR : R≠0 := by linarith
  rw [correctionScale, if_pos he]
  field_simp
  ring

theorem correctionScale_nonneg (C ε R : ℝ) (hC : 0<C) (hε : 0≤ε) :
    0≤correctionScale C ε R := by
  unfold correctionScale
  split_ifs with h
  · have hR : 0<R := lt_of_le_of_lt hε h
    apply mul_nonneg (inv_nonneg.mpr hC.le)
    exact sub_nonneg.mpr ((div_le_one hR).mpr h.le)
  · rfl

/-- The actual native residual after the measured-vector correction. -/
theorem stable_residual_bound (v : ι → NativeHilbert) (r : NativeHilbert)
    (measured : EuclideanSpace ℝ ι) (C ε : ℝ) (hC : 0<C)
    (hcost : ∀ x : EuclideanSpace ℝ ι, inner ℝ (gram v x) x ≤ C*‖x‖^2)
    (he : ‖measured-readings v r‖≤ε) :
    ‖r-correctionScale C ε ‖measured‖ • synthesis v measured‖^2 ≤
      ‖r‖^2-(max (‖measured‖-ε) 0)^2/C := by
  have hε : 0≤ε := (norm_nonneg _).trans he
  by_cases hr : ε<‖measured‖
  · have ha := correctionScale_nonneg C ε ‖measured‖ hC hε
    have hb := measured_response_lower (readings v r) measured ε he
    rw [← inner_synthesis] at hb
    have hc := hcost measured
    rw [gram_quadratic] at hc
    have hlin := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0 : ℝ)≤2) ha)
    have hquad := mul_le_mul_of_nonneg_left hc (sq_nonneg (correctionScale C ε ‖measured‖))
    have hid := correction_scalar_identity C ε ‖measured‖ hC hr hε
    rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, max_eq_left (by linarith)]
    nlinarith
  · have hr' : ‖measured‖≤ε := le_of_not_gt hr
    rw [correctionScale, if_neg hr, zero_smul, sub_zero,
      max_eq_right (by linarith), zero_pow (by omega), zero_div, sub_zero]

/-- A finite probe projection does at least as well as any synthesized correction. -/
theorem jointGain_ge_correction (v : ι → NativeHilbert) (r : NativeHilbert)
    (x : EuclideanSpace ℝ ι) :
    ‖r‖^2-‖r-synthesis v x‖^2 ≤ jointGain v r := by
  let p := (probeSpace v).starProjection r
  have hp : p∈probeSpace v := (probeSpace v).starProjection_apply_mem r
  have ho := Submodule.starProjection_inner_eq_zero r (p-synthesis v x)
    ((probeSpace v).sub_mem hp (synthesis_mem v x))
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (r-p) (p-synthesis v x) ho
  have he : (r-p)+(p-synthesis v x)=r-synthesis v x := by abel
  rw [he] at hpy
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection r (probeSpace v)
  rw [Submodule.starProjection_orthogonal_val] at hdecomp
  change ‖r‖^2=‖p‖^2+‖r-p‖^2 at hdecomp
  change _≤‖p‖^2
  simp only [← sq] at hpy
  nlinarith [sq_nonneg ‖p-synthesis v x‖]

/-- Title: `Uncertain readings certify actual joint gain`. -/
theorem stable_joint_gain (v : ι → NativeHilbert) (r : NativeHilbert)
    (measured : EuclideanSpace ℝ ι) (C ε : ℝ) (hC : 0<C)
    (hcost : ∀ x : EuclideanSpace ℝ ι, inner ℝ (gram v x) x ≤ C*‖x‖^2)
    (he : ‖measured-readings v r‖≤ε) :
    (max (‖measured‖-ε) 0)^2/C ≤ jointGain v r := by
  have hb := stable_residual_bound v r measured C ε hC hcost he
  have hg := jointGain_ge_correction v r (correctionScale C ε ‖measured‖ • measured)
  rw [map_smul] at hg
  linarith

/-- Title: `The measured correction remains in the admitted clock space`.

 The concrete corrected native fit is admitted in the larger clock space. -/
theorem corrected_fit_mem {N M : ℕ} (hNM : N≤M) (v : ι → NativeHilbert)
    (hv : ∀i, v i∈clockSpace M) (measured : EuclideanSpace ℝ ι) (C ε : ℝ) :
    fittedUnity N+correctionScale C ε ‖measured‖ • synthesis v measured ∈ clockSpace M := by
  apply (clockSpace M).add_mem (clockSpace_mono hNM (fittedUnity_mem N))
  apply (clockSpace M).smul_mem
  exact probeSpace_le v (clockSpace M) hv (synthesis_mem v measured)

/-- Title: `A native correction from uncertain signed readings`.

 The full uncertain-reading gain theorem for the actual native optimizer. -/
theorem stable_native_correction {N M : ℕ} (hNM : N≤M) (v : ι → NativeHilbert)
    (hv : ∀i, v i∈clockSpace M) (measured : EuclideanSpace ℝ ι) (C ε : ℝ) (hC : 0<C)
    (hcost : ∀ x : EuclideanSpace ℝ ι, inner ℝ (gram v x) x ≤ C*‖x‖^2)
    (he : ‖measured-readings v (UnityNativeHilbert.residual N)‖≤ε) :
    ‖unity-(fittedUnity N+correctionScale C ε ‖measured‖ • synthesis v measured)‖^2 ≤
      deficit N-(max (‖measured‖-ε) 0)^2/C ∧
    (max (‖measured‖-ε) 0)^2/C ≤
      inner ℝ (readings v (UnityNativeHilbert.residual N))
        (pseudoInverse v (readings v (UnityNativeHilbert.residual N))) ∧
    (max (‖measured‖-ε) 0)^2/C ≤ deficit N-deficit M := by
  have hbound := stable_residual_bound v (UnityNativeHilbert.residual N) measured C ε hC hcost he
  have hgain := stable_joint_gain v (UnityNativeHilbert.residual N) measured C ε hC hcost he
  refine ⟨?_, ?_, hgain.trans (jointGain_le_native_gain hNM v hv)⟩
  · simpa only [UnityNativeHilbert.residual, deficit, sub_add_eq_sub_sub] using hbound
  · rwa [jointGain_eq_pseudoinverse] at hgain

end NField.Alignment.UnityStableCorrection
