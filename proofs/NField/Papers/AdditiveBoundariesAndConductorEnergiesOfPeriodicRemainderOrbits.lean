/-
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFifteenConductorSpectrum
import NField.Alignment.FiniteStateOrbitBoundary
import NField.Alignment.IndexTwoOrbitEnergy
import NField.Alignment.PrimePowerFullOrbitBoundary
import NField.Alignment.SubgroupOrbitJacobiExpansion

/-!
# Additive Boundaries and Conductor Energies of Periodic Remainder Orbits

Reader-facing theorem map for the Lean companion to
`papers/additive_boundaries_and_conductor_energies_of_periodic_remainder_orbits.tex`.

## Proved in Lean

* The centered sawtooth transform, twisted evaluation, carry-boundary
  factorization, parity gate, and unit-visible boundary reconstruction used in
  the opening sections are imported from their theorem-object modules.
* The complete odd-character energy is a disjoint sum of nonnegative exact
  conductor energies.  Primitive odd sources after pushdown are proved
  equivalent to ambient characters of that exact conductor.
* Top-conductor concentration is equivalent to vanishing of every proper
  conductor level.
* The complete base-fifteen pushdown ledger and all nine exact-conductor values
  are executable exact certificates.  Proper energy is `1024`, top energy is
  `896`, and full energy is `1920`.
* For a full unit orbit modulo `p^e`, the visible boundary is the negative
  indicator of the reduction-one kernel.  Its conductor-`p` energy is
  `(p-1)p^(2e-2)/2`; conductor one and every higher prime-power conductor
  vanish.  Thus all energy is supported exactly at `p`.
* Quotient-dual orthogonality proves the subgroup indicator formula.  The
  subgroup boundary flux is then proved equal to the manuscript's exact
  finite combination of shifted Jacobi sums for every subgroup of a prime
  unit group.
* The quadratic-residue indicator has the exact endpoint reduction
  `S=(J-1)/2`.  Lean proves the Jacobi norm, the odd-family first moment, the
  resonant removal, the supplementary values at `-1` and `-2`, and the full
  four-branch off-resonance law modulo eight.  The prime-seven energy is
  checked exactly as `2`.
* Coupled long division and deterministic finite-state evolution is proved
  eventually periodic on its finite lifted state space.  On the eventual
  cycle, predecessor minus current value is the dynamical boundary, and its
  total mass is zero.

## Formalization boundary

Every named finite algebraic definition, lemma, proposition, theorem, and
corollary in the manuscript has a corresponding checked Lean construction or
theorem.  Historical discussion, literature attribution, and the final
open-ended comparison between orbit size and arithmetic conductor depth are
exposition rather than additional propositions.  No unchecked declaration is
used, and the formalization exposed no contradiction in the manuscript.
-/

namespace NField.Papers.AdditiveBoundariesAndConductorEnergiesOfPeriodicRemainderOrbits

open NField.Alignment.BaseFifteenConductorSpectrum
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorBoundaryLedger
open NField.Alignment.ExactConductorEnergy
open NField.Alignment.FiniteStateOrbitBoundary
open NField.Alignment.IndexTwoOrbitEnergy
open NField.Alignment.PrimePowerFullOrbitBoundary
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.SubgroupOrbitJacobiExpansion

-- Twisted sawtooth, carry-boundary, and visible-boundary spine.
#check twistedSawtooth_evaluation
#check carryBoundary_factorization
#check carryTransform_even_zero
#check constant_carryTransform_zero
#check cellBoundaryFlux_eq_boundary_pairing
#check unitBoundary_reconstruction
#check ordinaryBoundaryFlux_injective_on_unit_boundary

-- Odd kernels, primitive kernels, and conductor ledger.
#check oddCharacterKernel_eq
#check primitiveOddKernel_moebius
#check primitiveOddKernel_congruenceFormula
#check primitiveOddBoundaryMoment_conductorLedger

-- Nonnegative exact-conductor energy and concentration.
#check exactConductorEnergy_nonneg
#check fullOddBoundaryEnergy_eq_sum_exactConductor
#check primitiveSourceEquivExactConductor
#check exactConductorEnergy_eq_primitiveSourceEnergy
#check fullOddBoundaryEnergy_eq_top_add_proper
#check topConductorConcentration_iff

-- Complete base-fifteen spectrum.
#check base_fifteen_complete_pushdown_ledger
#check base_fifteen_exact_conductor_spectrum
#check base_fifteen_proper_conductor_energy
#check base_fifteen_full_odd_energy
#check base_fifteen_signed_corrections_open

-- Full prime-power orbit.
#check fullOrbit_primitiveSourceFlux
#check fullOrbit_primeSourceFlux
#check fullOrbit_higherSourceFlux_zero
#check fullOrbit_primeConductorEnergy
#check fullOrbit_higherConductorEnergy_zero
#check exactConductorEnergy_one_eq_zero
#check fullOrbit_exactConductorEnergy_pow
#check fullOrbit_fullOddBoundaryEnergy

-- Higher-index quotient-character expansion.
#check subgroup_indicator_as_quotient_average
#check subgroupOrbitIndicator_eq_quotientAverage
#check productCharacterSum_eq
#check subgroupOrbitFlux_jacobiExpansion

-- Index-two endpoint and four-branch law.
#check principalCharacter_boundary
#check indexTwoFlux_endpointReduction
#check shiftedQuadraticJacobi_normSq
#check allOdd_shiftedJacobi_sum
#check offResonanceJacobiMoment_eq
#check offResonanceEnergy_secondMoment
#check complexQuadraticCharacter_odd_iff
#check complexQuadraticCharacter_negTwo_re
#check indexTwo_offResonanceLaw
#check indexTwo_primeSeven_energy

-- Finite-state lift and dynamical boundary.
#check finiteTrajectory_eventuallyPeriodic
#check emittedDigit
#check liftedTransition
#check liftedTransition_eventuallyPeriodic
#check dynamicalBoundary
#check booleanDynamicalBoundary_eq
#check dynamicalBoundary_sum_zero

end NField.Papers.AdditiveBoundariesAndConductorEnergiesOfPeriodicRemainderOrbits
