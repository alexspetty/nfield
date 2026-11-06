/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitySpineAttainment
import NField.Alignment.UnityGramCosts

/-! # Source assembly for unity forcing and the complete prescribed cost statement -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySpineSource
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection UnityNativeIsometry UnitySpineBasis UnitySpineExpansion
open UnityShallowSpine UnitySharpSpine UnitySpineAttainment UnityPrescribedDetectors
open UnityDetectorHorizon UnityDetectorResponse UnityGramCosts

/-- Title: `Some shallow depth carries the stated share of squared deficit`.

 At least one actual shallow spine reading carries the stated share of the deficit. -/
theorem one_shallow_reading (N : ℕ) :
    ∃h<horizon N, (deficit N)^2/(4*(horizon N:ℝ))≤
      |inner ℝ (UnityNativeHilbert.residual N) (spine h)|^2 := by
  have hH : 0<horizon N := by have := horizon_ge_two N; omega
  have hHR : (0:ℝ)<horizon N := by exact_mod_cast hH
  have hs : (∑ _h∈Finset.range (horizon N), (deficit N)^2/(4*(horizon N:ℝ)))=
      (deficit N)^2/4 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hl : (∑ _h∈Finset.range (horizon N), (deficit N)^2/(4*(horizon N:ℝ)))≤
      ∑ h∈Finset.range (horizon N), |inner ℝ (UnityNativeHilbert.residual N) (spine h)|^2 := by
    rw [hs]
    exact prescribed_shallow_quarter N
  obtain ⟨h, hh, he⟩ := Finset.exists_le_of_sum_le
    (show (Finset.range (horizon N)).Nonempty from ⟨0, Finset.mem_range.mpr hH⟩) hl
  exact ⟨h, Finset.mem_range.mp hh, he⟩

/-- Title: `The complete displayed shallow-spine lower-bound chain`.

 The exact two-step shallow lower bound printed for the actual residual. -/
theorem shallow_spine_source (N : ℕ) :
    (deficit N)^2/4≤(deficit N)^2/(4*(1-(1/2:ℝ)^(horizon N))) ∧
    (deficit N)^2/(4*(1-(1/2:ℝ)^(horizon N)))≤
      ∑ h∈Finset.range (horizon N), |rootReading N h|^2 := by
  have hH : 0<horizon N := by have := horizon_ge_two N; omega
  have hp : (1/2:ℝ)^(horizon N)<1 := pow_lt_one₀ (by norm_num) (by norm_num) hH.ne'
  have ht : 0≤(1/2:ℝ)^(horizon N) := by positivity
  refine ⟨div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith), ?_⟩
  simpa only [spineEnergy, rootReading, spine_eq_iterate] using prescribed_shallow_energy N

/-- Title: `Unity forcing and admissible cost for the exact prescribed family`.

 Every clause of the paper's main unity-forcing and prescribed-cost theorem. -/
theorem unity_forcing_and_admissible_cost (N : ℕ) :
    (deficit N)^2/4≤(∑ h∈Finset.range (horizon N), |rootReading N h|^2) ∧
    (∀h : eligible N, detector N h∈clockSpace (4*N) ∧ detector N h∈(clockSpace N)ᗮ) ∧
    0≤capture N ∧ capture N≤deficit N-deficit (4*N) ∧
    (∀h : eligible N, gramMatrix (detectorFamily N) h h≤
      UnityDetectorBandCost.bandCost N h ∧ UnityDetectorBandCost.bandCost N h≤1) ∧
    largestEigenvalue (detectorFamily N)≤Matrix.trace (gramMatrix (detectorFamily N)) ∧
    Matrix.trace (gramMatrix (detectorFamily N))≤2 ∧
    (∀h : eligible N, signedReadings N h=rootReading N h-terminalReading N h) := by
  have hc := prescribed_uniform_cost N
  refine ⟨(shallow_spine_source N).1.trans (shallow_spine_source N).2,
    fun h => detector_admitted N h, capture_nonneg N, capture_le_native_gain N,
    hc.1, hc.2.1, hc.2.2.1.trans hc.2.2.2, ?_⟩
  intro h
  exact (prescribed_terminal_response N h).2

/-- Title: `The full sharp arbitrary-vector statement includes equality witnesses`.

 The sharp arbitrary-vector statement includes actual equality witnesses. -/
theorem sharp_spine_source (D : ℝ) (H : ℕ) (hH : 0<H) (hD0 : 0<D) (hD1 : D≤1) :
    (∀F : NativeHilbert, ‖F‖^2=D → inner ℝ F unity=D →
      (max (D*Real.sqrt (1-(1/2:ℝ)^H)-Real.sqrt ((1/2:ℝ)^H*D*(1-D))) 0)^2≤
        spineEnergy F H) ∧
    (∃F : NativeHilbert, ‖F‖^2=D ∧ inner ℝ F unity=D ∧
      spineEnergy F H=(max (D*Real.sqrt (1-(1/2:ℝ)^H)-
        Real.sqrt ((1/2:ℝ)^H*D*(1-D))) 0)^2) := by
  exact ⟨fun F henergy hmean => sharp_spine_forcing F D H hH henergy hmean,
    sharp_spine_equality_attainable D H hH hD0.le hD1⟩

end NField.Alignment.UnitySpineSource
