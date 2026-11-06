/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeIsometry

/-! # Actual native projection bands and their energies -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityProjectionBands
open UnityNativeHilbert UnityNativeProjection UnityNativeCopies UnityNativeDilation UnityNativeIsometry

def projectedEnergy (f : NativeHilbert) (N : ℕ) : ℝ := ‖projection N f‖^2

theorem projectedEnergy_nonneg (f : NativeHilbert) (N : ℕ) : 0≤projectedEnergy f N :=
  sq_nonneg _

theorem nested_projection {N M : ℕ} (hNM : N≤M) (f : NativeHilbert) :
    projection N (projection M f)=projection N f := by
  exact congrArg (fun F : NativeHilbert →L[ℝ] NativeHilbert => F f)
    (Submodule.starProjection_comp_starProjection_of_le (clockSpace_mono hNM))

/-- Title: `Root projection energy increases with the clock space`. -/
theorem projectedEnergy_mono (f : NativeHilbert) : Monotone (projectedEnergy f) := by
  intro N M hNM
  have h := (clockSpace N).norm_starProjection_apply_le (projection M f)
  change ‖projection N (projection M f)‖≤‖projection M f‖ at h
  rw [nested_projection hNM] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h

theorem projectedEnergy_le (f : NativeHilbert) (N : ℕ) : projectedEnergy f N≤‖f‖^2 := by
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    ((clockSpace N).norm_starProjection_apply_le f)

/-- The literal new fourfold band of any native vector. -/
def band (f : NativeHilbert) (M : ℕ) : NativeHilbert := projection (4*M) f-projection M f

theorem band_mem (f : NativeHilbert) (M : ℕ) : band f M∈clockSpace (4*M) := by
  apply (clockSpace (4*M)).sub_mem ((clockSpace (4*M)).starProjection_apply_mem f)
  exact clockSpace_mono (by omega : M≤4*M) ((clockSpace M).starProjection_apply_mem f)

/-- Title: `A new clock band is orthogonal to the old clock space`. -/
theorem band_orthogonal (f : NativeHilbert) (M : ℕ) : band f M∈(clockSpace M)ᗮ := by
  rw [band, ← nested_projection (by omega : M≤4*M) f]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- Title: `New clock band energy is the difference of projection energies`. -/
theorem band_energy (f : NativeHilbert) (M : ℕ) :
    ‖band f M‖^2=projectedEnergy f (4*M)-projectedEnergy f M := by
  have h := Submodule.starProjection_inner_eq_zero
    (projection (4*M) f) (projection M f) ((clockSpace M).starProjection_apply_mem f)
  change inner ℝ (projection (4*M) f-projection M (projection (4*M) f)) (projection M f)=0 at h
  rw [nested_projection (by omega : M≤4*M), inner_sub_left, real_inner_self_eq_norm_sq] at h
  rw [band, norm_sub_sq_real]
  unfold projectedEnergy
  linarith

theorem band_norm_sq_le (f : NativeHilbert) (M : ℕ) : ‖band f M‖^2≤‖f‖^2 := by
  rw [band_energy]
  exact (sub_le_self _ (projectedEnergy_nonneg _ _)).trans (projectedEnergy_le _ _)

/-- The paper's prescribed new root-detail vector. -/
def newRoot (M : ℕ) : NativeHilbert := band rootDetail M

theorem newRoot_mem (M : ℕ) : newRoot M∈clockSpace (4*M) := band_mem _ _
theorem newRoot_orthogonal (M : ℕ) : newRoot M∈(clockSpace M)ᗮ := band_orthogonal _ _

theorem newRoot_cost (M : ℕ) : ‖newRoot M‖^2≤1 := by
  simpa only [newRoot, rootDetail_norm_sq] using band_norm_sq_le rootDetail M

end NField.Alignment.UnityProjectionBands
