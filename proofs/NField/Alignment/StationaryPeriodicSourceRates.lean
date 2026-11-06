/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryWeightedMoments
import NField.Alignment.StationaryCumulativeWeight

/-! # The printed logarithmic normalization of all periodic moment clauses -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryPeriodicSourceRates
open Set CollisionRemainderDynamics CollisionPotentialHilbert StationaryDiagonalDefinitions
  StationaryPeriodicMoments StationaryWeightedMoments StationaryCumulativeWeight

/-- Title: `Periodic first moment with the manuscript logarithm`. -/
theorem periodic_first_source_rate {L X : ℕ} (hL : 2 ≤ L) (hX : 0 < X) :
    |dyadicMean X (finiteAge collisionWeight L)| ≤
      (4 / 3 : ℝ) * (L : ℝ) * Real.log (2 * L) / X := by
  have hl := one_add_log_le_two_log_two_mul (t := L) (by exact_mod_cast (show 1 ≤ L by omega))
  calc
    _ ≤ (2 / 3 : ℝ) * (L : ℝ) * (1 + Real.log L) / X := periodic_first_moment (by omega) hX
    _ ≤ (2 / 3 : ℝ) * (L : ℝ) * (2 * Real.log (2 * L)) / X := by gcongr
    _ = _ := by ring

/-- Title: `Periodic second moment with the manuscript logarithm and actual Haar norm`. -/
theorem periodic_second_source_rate {L X : ℕ} (hL : 2 ≤ L) (hX : 0 < X) :
    |dyadicMean X (fun n => finiteAge collisionWeight L n ^ 2) -
      ‖finitePotential collisionWeight L‖ ^ 2| ≤
      (16 / 9 : ℝ) * (L : ℝ) ^ 2 * Real.log (2 * L) ^ 2 / X := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hl := one_add_log_le_two_log_two_mul hL1
  have hnon : 0 ≤ 1 + Real.log L := by linarith [Real.log_nonneg hL1]
  calc
    _ ≤ (4 / 9 : ℝ) * (L : ℝ) ^ 2 * (1 + Real.log L) ^ 2 / X := periodic_second_moment (by omega) hX
    _ ≤ (4 / 9 : ℝ) * (L : ℝ) ^ 2 * (2 * Real.log (2 * L)) ^ 2 / X := by gcongr
    _ = _ := by ring

/-- Title: `Bounded-variation periodic first moment with the manuscript logarithm`. -/
theorem weighted_periodic_first_source_rate {h : ℝ → ℝ} (hh : BoundedVariationOn h (Icc 1 2))
    {L X : ℕ} (hL : 2 ≤ L) (hX : 0 < X) :
    |dyadicMean X (fun n => h (n / (X : ℝ)) * finiteAge collisionWeight L n)| ≤
      (2 / 3 : ℝ) * weightedMomentConstant h * (L : ℝ) * Real.log (2 * L) / X := by
  have hl := one_add_log_le_two_log_two_mul (t := L) (by exact_mod_cast (show 1 ≤ L by omega))
  have hc : 0 ≤ weightedMomentConstant h := by unfold weightedMomentConstant; positivity
  calc
    _ ≤ (1 / 3 : ℝ) * weightedMomentConstant h * (L : ℝ) * (1 + Real.log L) / X :=
      weighted_periodic_first_moment hh (by omega) hX
    _ ≤ (1 / 3 : ℝ) * weightedMomentConstant h * (L : ℝ) * (2 * Real.log (2 * L)) / X := by gcongr
    _ = _ := by ring

end NField.Alignment.StationaryPeriodicSourceRates
