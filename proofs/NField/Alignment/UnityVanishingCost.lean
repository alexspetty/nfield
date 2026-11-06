/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityGramCosts
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Vanishing native detector costs as the least coarse cutoff diverges -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityVanishingCost
open scoped BigOperators
open Filter Topology
open UnityNativeHilbert UnityNativeIsometry UnityProjectionBands
open UnityPrescribedDetectors UnityDetectorBandCost UnityGramCosts

/-- Title: `The root projection energy has a finite limit`.

 The root projection energy has a finite limit, without asserting that this limit is one. -/
theorem root_energy_tendsto :
    Tendsto (projectedEnergy rootDetail) atTop (𝓝 (⨆ m, projectedEnergy rootDetail m)) := by
  apply tendsto_atTop_ciSup (projectedEnergy_mono rootDetail)
  refine ⟨1, ?_⟩
  rintro _ ⟨m, rfl⟩
  simpa only [rootDetail_norm_sq] using projectedEnergy_le rootDetail m

/-- Title: `Selected detector cost vanishes as the least coarse cutoff diverges`.

 The literal selected band cost tends to zero when its least coarse cutoff diverges. -/
theorem selected_cost_tendsto_zero (N : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (hne : ∀k, (S k).Nonempty)
    (hmin : Tendsto (fun k => minimumCutoff (N k) (S k) (hne k)) atTop atTop) :
    Tendsto (fun k => ∑ h∈S k, bandCost (N k) h) atTop (𝓝 0) := by
  have hN : Tendsto (fun k => 4*N k) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) hmin
    exact (coarseCutoff_le (N k) ((S k).max' (hne k))).trans (by omega)
  have hdiff := (root_energy_tendsto.comp hN).sub (root_energy_tendsto.comp hmin)
  have hbound : Tendsto (fun k => 2*(projectedEnergy rootDetail (4*N k)-
      projectedEnergy rootDetail (minimumCutoff (N k) (S k) (hne k)))) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero, Function.comp_apply] using hdiff.const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun k => Finset.sum_nonneg (fun h _ => bandCost_nonneg (N k) h))
    (fun k => selected_band_cost_sharp (N k) (S k) (hne k))

/-- Title: `The prescribed detector cost vanishes under the stated cutoff condition`.

 The source's exact total eligible detector cost has the stated conditional limit. -/
theorem totalCost_tendsto_zero (N : ℕ → ℕ) (hne : ∀k, (eligible (N k)).Nonempty)
    (hmin : Tendsto (fun k => minimumCutoff (N k) (eligible (N k)) (hne k)) atTop atTop) :
    Tendsto (fun k => totalCost (N k)) atTop (𝓝 0) :=
  selected_cost_tendsto_zero N (fun k => eligible (N k)) hne hmin

/-- Title: `The actual detector Gram trace vanishes under the cutoff condition`. -/
theorem detectorTrace_tendsto_zero (N : ℕ → ℕ) (hne : ∀k, (eligible (N k)).Nonempty)
    (hmin : Tendsto (fun k => minimumCutoff (N k) (eligible (N k)) (hne k)) atTop atTop) :
    Tendsto (fun k => Matrix.trace (gramMatrix (detectorFamily (N k)))) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (totalCost_tendsto_zero N hne hmin)
    (fun k => gramMatrix_trace_nonneg (detectorFamily (N k))) (fun k => detector_trace_le_cost (N k))

end NField.Alignment.UnityVanishingCost
