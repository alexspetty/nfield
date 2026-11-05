/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRestrictedGapAsymptotic

/-!
# Complete and restricted conductor extrema

This assembles theorem 22 for the actual full-amplitude conductor cutoffs:
unique complete endpoints, endpoint asymptotic, attained restricted extrema,
two-sided gap order, eventual exact prime minimum, sharp zeta constant,
and the classification of every restricted minimizer.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorExtremaTheorem

open Filter Asymptotics
open CollisionConductorExtrema CollisionConductorEndpoint CollisionRestrictedGap
open CollisionMinimizerClassification CollisionRestrictedGapAsymptotic
open CollisionConductorOne CollisionOdometerRecurrence CollisionJordanVariance
open CollisionPrimeCandidate CollisionDivisorSeries

theorem complete_and_restricted_conductor_extrema :
    (∀ Q : ℕ,
      (∀ a : ℕ, -conductorEndpoint Q ≤ fixedConductorValue Q a ∧
        fixedConductorValue Q a ≤ conductorEndpoint Q) ∧
      (∀ a : ℕ, a < cutoffPeriod Q →
        (fixedConductorValue Q a=-conductorEndpoint Q ↔ a=0) ∧
        (fixedConductorValue Q a=conductorEndpoint Q ↔ a=cutoffPeriod Q-1))) ∧
    IsBigO atTop (fun Q : ℕ => conductorEndpoint Q-Real.log (Q : ℝ)^2/Real.pi^2)
      (fun Q : ℕ => Real.log (2*(Q : ℝ))) ∧
    (∀ Q : ℕ, 3 ≤ Q →
      0 < restrictedGap Q ∧
      (∀ a ∈ interiorResidues Q,
        -conductorEndpoint Q+restrictedGap Q ≤ fixedConductorValue Q a ∧
        fixedConductorValue Q a ≤ conductorEndpoint Q-restrictedGap Q) ∧
      (∃ a ∈ interiorResidues Q,
        fixedConductorValue Q a=-conductorEndpoint Q+restrictedGap Q) ∧
      (∃ a ∈ interiorResidues Q,
        fixedConductorValue Q a=conductorEndpoint Q-restrictedGap Q)) ∧
    (restrictedGap =Θ[atTop] (fun Q : ℕ => Real.log Q/(Q : ℝ)^2)) ∧
    (∀ᶠ Q : ℕ in atTop, restrictedGap Q=(2/3 : ℝ)*topPrimeAmplitude Q) ∧
    (restrictedGap ~[atTop]
      (fun Q : ℕ => (2*realZeta 2/(3*realZeta 3))*Real.log Q/(Q : ℝ)^2)) ∧
    (∀ᶠ Q : ℕ in atTop, ∀ a ∈ interiorResidues Q,
      conductorGap Q a=restrictedGap Q ↔
      ∃ p : ℕ, ∃ hp : p.Prime, ∃ _ : p ≤ Q, ∃ htop : Q < 2*p,
        amplitude p=topPrimeAmplitude Q ∧
        a=primeCandidate Q p (prime_coprime_complement hp htop).symm) := by
  exact ⟨complete_conductor_extrema,conductorEndpoint_isBigO_log,
    fun _ hQ => restricted_finite_extrema hQ,restrictedGap_two_sided_order,
    eventual_restricted_gap_exact,restrictedGap_literal_asymptotic,
    eventual_minimizer_iff_primeCandidate⟩

end NField.Alignment.CollisionConductorExtremaTheorem
