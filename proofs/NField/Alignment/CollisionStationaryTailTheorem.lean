/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDoubleExponentialLowerTails
import NField.Alignment.CollisionPotentialLpConvergence

/-!
# The complete stationary tails and moments theorem

This assembles the manuscript's numbered theorem for the actual Haar
potential and its continuous finite cutoffs. Monotonicity on probability
space also gives convergence for exponents below one.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionStationaryTailTheorem

open scoped ENNReal
open Filter MeasureTheory
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionPotentialMoments
open CollisionPotentialLpConvergence CollisionMomentNormBounds CollisionUpperTails
open CollisionDoubleExponentialLowerTails CollisionPotentialSupport
open CollisionLimitingPrimeProduct ProfiniteRemainderMeasure CollisionRemainderDynamics

theorem cutoff_tendsto_eLpNorm_all_real (r : ℝ) :
    Tendsto (fun M => eLpNorm
      (fun x => potentialMap collisionWeight M x-collisionPotential x)
      (ENNReal.ofReal r) phaseHaar) atTop (nhds 0) := by
  by_cases hr : 1 ≤ r
  · exact cutoff_tendsto_eLpNorm hr
  · have hp : ENNReal.ofReal r ≤ (1 : ℝ≥0∞) := by
      simpa using ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hr))
    have h1 : Tendsto (fun M => eLpNorm
        (fun x => potentialMap collisionWeight M x-collisionPotential x) 1 phaseHaar)
        atTop (nhds 0) := by
      simpa using cutoff_tendsto_eLpNorm (r := 1) (by norm_num)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds h1 (fun _ => bot_le)
    intro M
    exact eLpNorm_le_eLpNorm_of_exponent_le hp
      ((potentialMap collisionWeight M).continuous.measurable.aestronglyMeasurable.sub
        (Lp.aestronglyMeasurable collisionPotential))

theorem stationary_tails_and_moments :
    (∀ c : ℝ, 0 < c → c < Real.pi → ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H →
      (phaseHaar.real {x | H < |collisionPotential x|} ≤ K*Real.exp (-c*Real.sqrt H)) ∧
      (∀ M : ℕ, phaseHaar.real {x | H < |potentialMap collisionWeight M x|} ≤
        K*Real.exp (-c*Real.sqrt H))) ∧
    (∀ r : ℝ, Tendsto (fun M => eLpNorm
      (fun x => potentialMap collisionWeight M x-collisionPotential x)
      (ENNReal.ofReal r) phaseHaar) atTop (nhds 0)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
      lpNorm collisionPotential (ENNReal.ofReal r) phaseHaar ≤ K*r^2) ∧
    (∀ c : ℝ, c < Real.pi →
      Integrable (fun x => Real.exp (c*Real.sqrt |collisionPotential x|)) phaseHaar) ∧
    (¬ BddAbove (Measure.map collisionPotential phaseHaar).support ∧
      ¬ BddBelow (Measure.map collisionPotential phaseHaar).support) ∧
    (∀ d : ℝ, 1/Real.sqrt alignmentGamma < d → ∀ᶠ H : ℝ in atTop,
      phaseHaar.real {x | H < collisionPotential x}=
        phaseHaar.real {x | collisionPotential x < -H} ∧
      Real.exp (-Real.exp (d*Real.sqrt H)) ≤
        phaseHaar.real {x | collisionPotential x < -H}) := by
  refine ⟨fun _ hc hcπ => upper_tails hc hcπ,cutoff_tendsto_eLpNorm_all_real,?_,
    ?_,potential_support_unbounded,fun _ hd => stationary_double_exponential_lower_tails hd⟩
  · obtain ⟨K,hK,hbound⟩ := potential_quadratic_norm_bound
    exact ⟨K,hK,fun r hr => (hbound r hr).1⟩
  · intro c hc
    obtain ⟨B,hB,hY,hM⟩ := potential_exponential_moments hc
    exact hY.1

end NField.Alignment.CollisionStationaryTailTheorem
