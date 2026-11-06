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

## Coverage

The named results and displays cover exact conductor energies, full-unit orbit
concentration, subgroup boundary formulas and eventual finite-state cycles.
The printed finite examples are checked. The higher-index closed-form question
remains open.

## Scope and assumptions

Prime-power concentration concerns a full unit orbit under the stated prime
and exponent hypotheses. Subgroup boundary formulas use actual subgroups of
the prime unit group. Eventual periodicity concerns a deterministic system on
a finite lifted state space. The base-fifteen energies `1024`, `896` and
`1920`, and the prime-seven energy `2`, are exact finite examples. The
higher-index closed-form question remains open.
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
