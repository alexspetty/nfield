/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeDilation

/-! # Exact energy beyond the transported native optimizer -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityTransportedFit
open UnityNativeHilbert UnityNativeProjection UnityNativeCopies UnityNativeDilation

/-- The actual new optimizer minus the transported old optimizer. -/
def transportedIncrement (b N : ℕ) (hb : 0<b) : NativeHilbert :=
  fittedUnity (b*N)-copy b hb (fittedUnity N)

theorem unity_inner_fitted (N : ℕ) :
    inner ℝ unity (fittedUnity N) = ‖fittedUnity N‖^2 := by
  have h := residual_inner_zero N (fittedUnity_mem N)
  change inner ℝ (unity-fittedUnity N) (fittedUnity N)=0 at h
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  linarith

theorem transported_inner {b N : ℕ} (hb : 2≤b) :
    inner ℝ (fittedUnity (b*N)) (copy b (by omega) (fittedUnity N)) =
      ‖fittedUnity N‖^2/b := by
  have hm := copy_clockSpace hb (fittedUnity_mem N)
  have h := residual_inner_zero (b*N) hm
  change inner ℝ (unity-fittedUnity (b*N)) (copy b (by omega) (fittedUnity N))=0 at h
  rw [inner_sub_left, copy_mean, unity_inner_fitted] at h
  linarith

/-- Title: `Exact native energy beyond the transported fit`.

 Literal transported energy, retaining the positive coarse-fit baseline. -/
theorem transported_energy {b N : ℕ} (hb : 2≤b) :
    ‖transportedIncrement b N (by omega)‖^2 =
      (1-deficit (b*N))-(1-deficit N)/(b : ℝ) := by
  rw [transportedIncrement, norm_sub_sq_real, copy_norm_sq, transported_inner hb]
  have hN := fitted_energy N
  have hbN := fitted_energy (b*N)
  rw [show ‖fittedUnity N‖^2=1-deficit N by linarith,
    show ‖fittedUnity (b*N)‖^2=1-deficit (b*N) by linarith]
  ring

/-- Title: `Native gain retains the transported-fit baseline`.

 Literal native gain after subtracting the transported-fit baseline. -/
theorem transported_gain {b N : ℕ} (hb : 2≤b) :
    deficit N-deficit (b*N) = ‖transportedIncrement b N (by omega)‖^2 -
      (1-(b : ℝ)⁻¹)*(1-deficit N) := by
  rw [transported_energy hb]
  ring

/-- The entire old transported clock fit is removed by the new projection. -/
theorem projection_copy_fitted {b N : ℕ} (hb : 2≤b) :
    projection (b*N) (copy b (by omega) (fittedUnity N)) =
      copy b (by omega) (fittedUnity N) :=
  Submodule.starProjection_eq_self_iff.mpr (copy_clockSpace hb (fittedUnity_mem N))

/-- Title: `Residual dilation includes the initial native block`.

 Exact residual dilation, including the initial native boundary block. -/
theorem residual_dilation {b N : ℕ} (hb : 2≤b) :
    UnityNativeHilbert.residual (b*N) =
      (copy b (by omega) (UnityNativeHilbert.residual N)+boundary b (by omega)) -
      projection (b*N)
        (copy b (by omega) (UnityNativeHilbert.residual N)+boundary b (by omega)) := by
  have he : copy b (by omega) (UnityNativeHilbert.residual N)+boundary b (by omega) =
      unity-copy b (by omega) (fittedUnity N) := by
    change copyLinear b (by omega) (unity-fittedUnity N)+boundary b (by omega)=_
    rw [map_sub]
    unfold boundary
    change copy b (by omega) unity-copy b (by omega) (fittedUnity N)+
      (unity-copy b (by omega) unity)=_
    abel
  rw [he, map_sub, projection_copy_fitted hb]
  unfold UnityNativeHilbert.residual fittedUnity
  abel

end NField.Alignment.UnityTransportedFit
