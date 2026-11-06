/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityPrescribedDetectors
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The exact signed terminal response of the actual native detector -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityDetectorResponse
open UnityNativeHilbert UnityNativeProjection UnityNativeIsometry UnityProjectionBands
open UnityPrescribedDetectors

/-- The actual adjoint pullback through the prescribed isometric copy. -/
def pullback (h : ℕ) : NativeHilbert →L[ℝ] NativeHilbert :=
  (scaledCopy (2^h) (by positivity)).toContinuousLinearMap.adjoint

theorem pullback_inner (h : ℕ) (f g : NativeHilbert) :
    inner ℝ (pullback h f) g=inner ℝ f (scaledCopy (2^h) (by positivity) g) :=
  ContinuousLinearMap.adjoint_inner_left _ g f

theorem adjoint_iterate_inner (A : NativeHilbert →L[ℝ] NativeHilbert) (h : ℕ)
    (f g : NativeHilbert) :
    inner ℝ ((A.adjoint^[h]) f) g=inner ℝ f ((A^[h]) g) := by
  induction h generalizing f g with
  | zero => rfl
  | succ h ih =>
    rw [Function.iterate_succ_apply', ContinuousLinearMap.adjoint_inner_left, ih,
      Function.iterate_succ_apply]

/-- Title: `The copied residual uses the actual iterated binary adjoint`.

 The adjoint pullback is literally the iterated binary adjoint used in the source. -/
theorem pullback_eq_iterate (h : ℕ) (f : NativeHilbert) :
    pullback h f=((binaryCopy.toContinuousLinearMap.adjoint)^[h]) f := by
  apply ext_inner_right ℝ
  intro g
  rw [pullback_inner, ← binary_iterate]
  exact (adjoint_iterate_inner binaryCopy.toContinuousLinearMap h f g).symm

/-- Title: `The pulled residual is orthogonal to the coarse clock space`. -/
theorem pulled_residual_orthogonal (N h : ℕ) :
    pullback h (UnityNativeHilbert.residual N)∈(clockSpace (coarseCutoff N h))ᗮ := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro g hg
  rw [pullback_inner]
  apply residual_inner_zero N
  apply clockSpace_mono (show 2^h*coarseCutoff N h≤N from Nat.mul_div_le _ _)
  exact scaledCopy_clockSpace (2^h) (by positivity) (coarseCutoff N h) hg

/-- The root coefficient is the full signed native reading of its copied detail. -/
def rootReading (N h : ℕ) : ℝ :=
  inner ℝ (UnityNativeHilbert.residual N) ((binaryCopy^[h]) rootDetail)

/-- The terminal pairing retains all addresses beyond the new clock projection. -/
def terminalReading (N h : ℕ) : ℝ :=
  inner ℝ (pullback h (UnityNativeHilbert.residual N))
    (rootDetail-projection (4*coarseCutoff N h) rootDetail)

theorem detector_reading_pullback (N h : ℕ) :
    inner ℝ (UnityNativeHilbert.residual N) (detector N h)=
      inner ℝ (pullback h (UnityNativeHilbert.residual N)) (newRoot (coarseCutoff N h)) := by
  rw [detector, residual_conditioned_reading, pullback_inner]

/-- The exact source response is its spine coefficient minus the signed terminal pairing. -/
theorem detector_terminal_response (N h : ℕ) :
    inner ℝ (UnityNativeHilbert.residual N) (detector N h)=
      rootReading N h-terminalReading N h := by
  rw [detector_reading_pullback, newRoot, band, inner_sub_right]
  have hz := (Submodule.mem_orthogonal' _ _).mp (pulled_residual_orthogonal N h)
    (projection (coarseCutoff N h) rootDetail)
    ((clockSpace (coarseCutoff N h)).starProjection_apply_mem rootDetail)
  rw [hz, sub_zero, terminalReading, inner_sub_right, rootReading, binary_iterate,
    ← pullback_inner]
  ring

/-- Title: `The prescribed response retains its signed terminal pairing`. -/
theorem prescribed_terminal_response (N : ℕ) (h : eligible N) :
    signedReadings N h =
      inner ℝ (pullback h (UnityNativeHilbert.residual N)) (newRoot (coarseCutoff N h)) ∧
    signedReadings N h=rootReading N h-terminalReading N h :=
  ⟨detector_reading_pullback N h, detector_terminal_response N h⟩

theorem clock_one : clock 1=0 := by
  apply ext_value
  intro m hm
  rw [UnityNativeDilation.clock_value_all]
  simp [clockValue, value]

/-- Title: `The exact binary clock lift`.

 The exact binary clock lift, with its zero unit clock. -/
theorem binary_clock_lift (h j : ℕ) (hj : 0<j) :
    (binaryCopy^[h]) (clock j)=Real.sqrt ((2^h : ℕ):ℝ) •
      (clock (2^h*j)-(j:ℝ)⁻¹ • clock (2^h)) := by
  rw [binary_iterate, scaledCopy_clock _ _ _ hj]

end NField.Alignment.UnityDetectorResponse
