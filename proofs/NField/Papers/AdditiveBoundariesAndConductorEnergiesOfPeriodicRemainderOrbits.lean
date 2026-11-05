/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PushdownParity
import NField.Alignment.DivisorConductorLedger
import NField.Alignment.IncreasingDigitBoundary
import NField.Alignment.RationalRemainderOrbit
import NField.Alignment.BaseFifteenActualEnergy
import NField.Alignment.OrbitIndicatorCorrespondence
import NField.Alignment.EventualCycleBoundary
import NField.Alignment.OrbitPaperExamples
import NField.Alignment.OrbitPaperDetails
import NField.Alignment.BaseFifteenEndpointDetails
import NField.Alignment.QuadraticSupplementaryPowers
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

## Source correspondence and evidence

The November continuation assembles the parity criterion and literal
modulus-25 witness, denominator CRT and exact period/coset, arbitrary-divisor
ledger, and connections from the actual digit/orbit indicators to the
character energies. It constructs the actual eventual cycle permutation and
checks the printed finite examples. The separate source inventories cover
all named results and displays; the higher-index closed-form question remains
explicitly open. Native package and local reader admission have their own
receipts. A build alone does not establish source correspondence.
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

-- November source-correspondence completion.
#check NField.Alignment.PushdownParity.exactConductorEnergy_zero_of_even_pushdown
#check NField.Alignment.PushdownParity.exactConductorEnergy_zero_of_zero_pushdown
#check NField.Alignment.PushdownParity.exactConductorEnergy_zero_iff_primitive_odd_flux_zero
#check NField.Alignment.DivisorConductorLedger.exactConductorEnergy_cast_eq_ledger
#check NField.Alignment.IncreasingDigitBoundary.actual_digit_boundary_witness
#check NField.Alignment.IncreasingDigitBoundary.actual_top_concentration
#check NField.Alignment.DenominatorSplit.factorization
#check NField.Alignment.DenominatorSplit.coprimePart_coprime_base
#check NField.Alignment.RationalRemainderOrbit.remainderCRT_after_burnIn
#check NField.Alignment.RationalRemainderOrbit.exact_positive_period
#check NField.Alignment.RationalRemainderOrbit.orbit_is_coset
#check NField.Alignment.BaseFifteenActualEnergy.actual_conductor_spectrum
#check NField.Alignment.BaseFifteenActualEnergy.actual_digit_energy_split
#check NField.Alignment.BaseFifteenExamples.base_fifteen_diagonal_ledger
#check NField.Alignment.BaseFifteenExamples.base_fifteen_antipodal_ledger
#check NField.Alignment.BaseFifteenEndpointDetails.endpoint_coincidences
#check NField.Alignment.OrbitIndicatorCorrespondence.fullUnitBoundary_formula
#check NField.Alignment.OrbitIndicatorCorrespondence.actual_full_orbit_conductor_energy
#check NField.Alignment.OrbitIndicatorCorrespondence.actual_full_orbit_total_energy
#check NField.Alignment.OrbitIndicatorCorrespondence.indexTwoIndicator_eq_square_indicator
#check NField.Alignment.OrbitIndicatorCorrespondence.indexTwoIndicator_eq_kernel_indicator
#check NField.Alignment.OrbitPaperExamples.full_orbit_nine_cycle
#check NField.Alignment.OrbitPaperExamples.full_orbit_nine_boundary
#check NField.Alignment.OrbitPaperExamples.full_orbit_nine_energy
#check NField.Alignment.OrbitPaperExamples.prime_seven_card_moment
#check NField.Alignment.OrbitPaperDetails.twistedSawtooth_even_zero
#check NField.Alignment.OrbitPaperDetails.finite_fourier_expansion
#check NField.Alignment.OrbitPaperDetails.fourier_twisted_expansion
#check NField.Alignment.OrbitPaperDetails.trivial_on_subgroup_iff_factors
#check NField.Alignment.OrbitPaperDetails.no_odd_resonance_of_neg_one_mem
#check NField.Alignment.OrbitPaperDetails.odd_energy_resonance_split
#check NField.Alignment.OrbitPaperDetails.off_resonance_character_sum
#check NField.Alignment.QuadraticSupplementaryPowers.quadratic_supplementary_powers
#check NField.Alignment.EventualCycleBoundary.finiteTrajectory_enters_actual_cycle
#check NField.Alignment.EventualCycleBoundary.orbitPermutation_predecessor
#check NField.Alignment.EventualCycleBoundary.actual_cycle_boundary
#check NField.Alignment.EventualCycleBoundary.emittedDigit_lt_base

end NField.Papers.AdditiveBoundariesAndConductorEnergiesOfPeriodicRemainderOrbits
