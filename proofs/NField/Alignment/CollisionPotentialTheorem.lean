/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialReflection
import NField.Alignment.CollisionPotentialCutoff
import NField.Alignment.CollisionJordanVariance

/-!
# Square-integrable collision potential: complete theorem statement

This assembles the actual Haar construction, its Jordan variance, sharp
cutoff order, mean and symmetry. The witness is the limit already constructed
from the collision weights; none of these conclusions is a hypothesis.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialTheorem

open scoped BigOperators
open Filter MeasureTheory
open CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialReflection
open CollisionPotentialCutoff CollisionJordanVariance ProfiniteRemainderMeasure

theorem square_integrable_potential :
    ∃ Y : HaarL2,
      Tendsto (finitePotential collisionWeight) atTop (nhds Y) ∧
      (∫ x, Y x ∂phaseHaar) = 0 ∧
      0 < ‖Y‖^2 ∧
      ‖Y‖^2 = (1 / 27 : ℝ) *
        (∑' q : ℕ, if 2 ≤ q then jordanTwo q * (amplitude q)^2 else 0) ∧
      (fun M : ℕ => Y - finitePotential collisionWeight M) =O[atTop]
        (fun M : ℕ => Real.log (2 * (M : ℝ)) / Real.sqrt (M : ℝ)) ∧
      (∀ᵐ x ∂phaseHaar, Y (reflection x) = -Y x) ∧
      Measure.map (fun x => -Y x) phaseHaar = Measure.map (fun x => Y x) phaseHaar := by
  refine ⟨collisionPotential, tendsto_collisionPotential, collisionPotential_mean_zero,
    ?_, collisionPotential_variance, collisionPotential_cutoff_isBigO,
    collisionPotential_reflection_ae, collisionPotential_law_symmetric⟩
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 144) collisionPotential_variance_lower

end NField.Alignment.CollisionPotentialTheorem
