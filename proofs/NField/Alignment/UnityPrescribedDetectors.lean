/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityProjectionBands
import NField.Alignment.UnityGramPseudoinverse
import NField.Alignment.UnityCumulativeCapture

/-!
# The literal shallow detector family

The cutoff, horizon, new root detail, conditioned copied probe, actual
readings, Gram operator and Moore--Penrose capture are source objects.
The normalized-capture divergence remains an explicit open hypothesis.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityPrescribedDetectors
open scoped BigOperators
open Filter Topology
open UnityNativeHilbert UnityNativeProjection UnityNativeCopies UnityNativeDilation
open UnityNativeIsometry UnityProjectionBands UnityFiniteGram UnityGramPseudoinverse
open UnityCumulativeCapture

/-- The exact dyadic coarse cutoff. -/
def coarseCutoff (N h : ℕ) : ℕ := N/2^h

/-- The paper's positive shallow horizon, written with the natural ceiling. -/
def horizon (N : ℕ) : ℕ := ⌈Real.log (4/deficit N)/Real.log 2⌉₊

/-- The actual eligible shallow depths. -/
def eligible (N : ℕ) : Finset ℕ :=
  (Finset.range (horizon N)).filter (fun h => 2≤coarseCutoff N h)

/-- The original prescribed conditioned probe. -/
def detector (N h : ℕ) : NativeHilbert :=
  conditioned N (scaledCopy (2^h) (by positivity) (newRoot (coarseCutoff N h)))

theorem detector_binary_formula (N h : ℕ) :
    detector N h=conditioned N ((binaryCopy^[h]) (newRoot (coarseCutoff N h))) := by
  rw [binary_iterate]
  rfl

theorem copied_root_mem (N h : ℕ) :
    scaledCopy (2^h) (by positivity) (newRoot (coarseCutoff N h))∈clockSpace (4*N) := by
  have hm := scaledCopy_clockSpace (2^h) (by positivity) (4*coarseCutoff N h)
    (newRoot_mem (coarseCutoff N h))
  apply clockSpace_mono _ hm
  have hdiv : 2^h*(N/2^h)≤N := Nat.mul_div_le N (2^h)
  unfold coarseCutoff
  nlinarith

/-- Title: `Every prescribed detector lies in the admitted new clock band`.

 Every prescribed probe is an actual new-band clock vector. -/
theorem detector_admitted (N h : ℕ) :
    detector N h∈clockSpace (4*N) ∧ detector N h∈(clockSpace N)ᗮ :=
  ⟨conditioned_mem (by omega) (copied_root_mem N h), conditioned_orthogonal _ _⟩

/-- Title: `Conditioned detector cost is bounded by its original band cost`. -/
theorem detector_cost (N h : ℕ) : ‖detector N h‖^2≤‖newRoot (coarseCutoff N h)‖^2 := by
  have hn := conditioned_norm_le N
    (scaledCopy (2^h) (by positivity) (newRoot (coarseCutoff N h)))
  rw [LinearIsometry.norm_map] at hn
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn

theorem detector_cost_le_one (N h : ℕ) : ‖detector N h‖^2≤1 :=
  (detector_cost N h).trans (newRoot_cost _)

/-- The actual finite family selected by the shallow horizon. -/
def detectorFamily (N : ℕ) : eligible N → NativeHilbert := fun h => detector N h

def signedReadings (N : ℕ) : EuclideanSpace ℝ (eligible N) :=
  readings (detectorFamily N) (UnityNativeHilbert.residual N)

def detectorGram (N : ℕ) : EuclideanSpace ℝ (eligible N) →ₗ[ℝ] EuclideanSpace ℝ (eligible N) :=
  gram (detectorFamily N)

/-- Literal prescribed Moore--Penrose capture, with all cross terms. -/
def capture (N : ℕ) : ℝ :=
  inner ℝ (signedReadings N) (pseudoInverse (detectorFamily N) (signedReadings N))

/-- Title: `Prescribed pseudoinverse capture is the actual joint projection gain`. -/
theorem capture_eq_jointGain (N : ℕ) :
    capture N=jointGain (detectorFamily N) (UnityNativeHilbert.residual N) :=
  (jointGain_eq_pseudoinverse _ _).symm

theorem capture_nonneg (N : ℕ) : 0≤capture N := by
  rw [capture_eq_jointGain]
  exact jointGain_nonneg _ _

/-- Title: `Prescribed capture is bounded by newly admitted native energy`.

 The exact source detector captures only actual newly admitted clock energy. -/
theorem capture_le_native_gain (N : ℕ) : capture N≤deficit N-deficit (4*N) := by
  rw [capture_eq_jointGain]
  exact jointGain_le_native_gain (by omega) (detectorFamily N)
    (fun h => (detector_admitted N h).1)

/-- The literal pseudoinverse update of the fitted native unity vector. -/
def prescribedFit (N : ℕ) : NativeHilbert :=
  fittedUnity N+synthesis (detectorFamily N) (pseudoInverse (detectorFamily N) (signedReadings N))

/-- Title: `The prescribed pseudoinverse correction is an admitted clock fit`. -/
theorem prescribedFit_mem (N : ℕ) : prescribedFit N∈clockSpace (4*N) := by
  apply (clockSpace (4*N)).add_mem (clockSpace_mono (by omega) (fittedUnity_mem N))
  exact probeSpace_le (detectorFamily N) (clockSpace (4*N))
    (fun h => (detector_admitted N h).1) (synthesis_mem _ _)

/-- Title: `The prescribed correction realizes exactly its captured energy`.

 The prescribed update realizes exactly its Moore--Penrose energy gain. -/
theorem prescribedFit_energy (N : ℕ) :
    deficit N-‖unity-prescribedFit N‖^2=capture N := by
  rw [capture_eq_jointGain]
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection (UnityNativeHilbert.residual N)
    (probeSpace (detectorFamily N))
  rw [Submodule.starProjection_orthogonal_val] at hp
  rw [prescribedFit]
  have he : unity-(fittedUnity N+synthesis (detectorFamily N)
      (pseudoInverse (detectorFamily N) (signedReadings N))) =
      UnityNativeHilbert.residual N-
        (probeSpace (detectorFamily N)).starProjection (UnityNativeHilbert.residual N) := by
    rw [projection_eq_pseudo_synthesis]
    unfold UnityNativeHilbert.residual signedReadings
    abel
  rw [he]
  unfold deficit jointGain
  linarith

/-- Title: `Actual prescribed capture increases native capacity`.

 The printed capacity-step bounds for the exact detector family. -/
theorem prescribed_capacity_step (N : ℕ) :
    capture N/(deficit N)^2 ≤ capture N/(deficit N*deficit (4*N)) ∧
      capture N/(deficit N*deficit (4*N)) ≤ capacity (4*N)-capacity N := by
  constructor
  · apply div_le_div_of_nonneg_left (capture_nonneg N)
      (mul_pos (deficit_pos N) (deficit_pos (4*N)))
    have ha := deficit_antitone (by omega : N≤4*N)
    have hp := deficit_pos N
    nlinarith
  · rw [capacity_difference]
    exact div_le_div_of_nonneg_right (capture_le_native_gain N)
      (mul_nonneg (deficit_pos _).le (deficit_pos _).le)

/-- Title: `Divergent prescribed capture forces complete native recovery`.

 The source's divergent-capture theorem for its exact prescribed family. -/
theorem prescribed_capture_recovery (N₀ : ℕ)
    (hdiv : ¬Summable (fun k => capture (N₀*4^k)/(deficit (N₀*4^k))^2)) :
    Tendsto capacity atTop atTop ∧ Tendsto deficit atTop (𝓝 0) := by
  let C := fun k => N₀*4^k
  have hC : Monotone C := by
    intro i j hij
    exact Nat.mul_le_mul_left N₀ (Nat.pow_le_pow_right (by omega) hij)
  have hG : ∀k, capture (C k)≤deficit (C k)-deficit (C (k+1)) := by
    intro k
    simpa [C, pow_succ, mul_assoc, mul_comm, mul_left_comm] using capture_le_native_gain (C k)
  exact ⟨normalized_capture_capacity C hC (fun k => capture (C k))
      (fun k => capture_nonneg _) hG hdiv,
    normalized_capture_recovery C hC (fun k => capture (C k))
      (fun k => capture_nonneg _) hG hdiv⟩

end NField.Alignment.UnityPrescribedDetectors
