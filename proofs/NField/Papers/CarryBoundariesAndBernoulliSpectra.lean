/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.AmbientConductorDepthWeight
import NField.Alignment.CarryBoundarySpectra
import NField.Alignment.ConductorBoundaryLedger
import NField.Alignment.ConductorDepthFactorization
import NField.Alignment.EndpointNormalization
import NField.Alignment.FinitePrefixCarryReduction
import NField.Alignment.LiftedBoundaryInvisibility
import NField.Alignment.PrimePowerEnergyDecomposition
import NField.Alignment.TerminalCollisionBoundary

/-!
# Carry Boundaries and Bernoulli Spectra in Long Division

Reader-facing theorem map for the Lean companion to
`papers/carry_boundaries_and_bernoulli_spectra.tex`.

## Proved in Lean

* The centered sawtooth is odd, and its nonprincipal character transform is
  exactly the first generalized Bernoulli sum in the manuscript's convention.
* Primitive Gauss-sum separation is assembled with finite Fourier inversion to
  prove the twisted-sawtooth identity for every multiplier.  Nonunit
  multipliers are included and vanish through primitivity rather than through
  an extra coprimality assumption.
* The primitive carry-boundary factorization is proved with the manuscript's
  sign and normalization.
* Every even character channel vanishes, and constant weights have no carry
  spectrum.
* The cell-difference flux is exactly the signed-boundary pairing.  Ordinary
  character fluxes reconstruct the boundary on every unit residue and detect
  no boundary mass on nonunits.
* Parseval is proved for the complete finite carry spectrum.
* The interval Stokes formula is proved by finite telescoping.
* Actual long-division digits are connected to padded prefix cells.  The exact
  finite-prefix slice identity, cylinder-to-carry reduction, bulk term,
  terminal endpoint, and centered reduction are all proved.
* Endpoint normalization is exact, including both cyclic endpoint corrections,
  and its unitwise constant discrepancy is proved spectrally invisible.
* The conductor-depth weight is defined intrinsically from the canonical
  p-adic depth of every residue.  Its response theorem includes the zero
  residue, every depth inside the conductor budget, and exact over-depth
  vanishing.
* The induced-character carry transform is factored through both cell
  differences and the signed boundary chain using that intrinsic weight.
* A block lift has exactly the pushforward boundary claimed in the manuscript.
  Every surviving endpoint is nonunit after positive prime dilation, so every
  higher primitive transform vanishes.
* The complete primitive-odd kernel, boundary mean criterion, exact
  primitive-odd population, and terminal-collision mean law are universal
  theorems, not finite certificates.
* The general Mobius conductor ledger and its pushdown terms are proved by
  finite character orthogonality.
* Every ambient odd prime-power character is proved to have a unique positive
  primitive odd source.  An explicit finite equivalence reindexes Parseval by
  those sources and proves the complete prime-power energy decomposition.
* Executable exact certificates verify the terminal support size, singleton
  structure, formal boundary size, unit-boundary norm, conductor balance, and
  antipodal oddness for bases 3, 5, 7, and 11 at depths 2 and 3.
* The base-15 calculation proves the nonzero pushdowns modulo 45 and 75, all
  four conductor-ledger differences, total moment 896, primitive-odd mean 28,
  and formal boundary size 30.

## Formalization boundary

Every named definition, lemma, proposition, theorem, and corollary in the
finite algebraic argument now has a corresponding Lean construction or
theorem.  The exact finite examples remain executable certificates in addition
to the universal proofs.

The historical discussion, literature comparisons, and open-ended outlook are
not propositions.  The classical analytic remark identifying primitive
Bernoulli magnitudes with Dirichlet L-values is cited from the standard
functional equation rather than rebuilt here from Mathlib's analytic
continuation stack.  The finite carry, boundary, conductor, mean, ledger, and
energy results do not assume that remark.  No unchecked declaration is used,
and no contradiction with the manuscript appeared.
-/

namespace NField.Papers.CarryBoundariesAndBernoulliSpectra

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.AmbientConductorDepthWeight
open NField.Alignment.ConductorBoundaryLedger
open NField.Alignment.ConductorDepthFactorization
open NField.Alignment.EndpointNormalization
open NField.Alignment.FinitePrefixCarryReduction
open NField.Alignment.LiftedBoundaryInvisibility
open NField.Alignment.PrimePowerCharacterSources
open NField.Alignment.PrimePowerEnergy
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.TerminalCollisionBoundary

/-- Exact oddness of the centered sawtooth. -/
theorem exact_sawtooth_odd {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (x : ZMod m) :
    centeredSawtooth (-x) = -centeredSawtooth x :=
  centeredSawtooth_neg hm x

/-- Exact Bernoulli evaluation of the basic nonprincipal sawtooth transform. -/
theorem exact_bernoulli_transform {m : ℕ} [NeZero m]
    (hm : m ≠ 1) {ψ : Character m} (hψ : ψ ≠ 1) :
    twistedTransform centeredSawtooth ψ 1 = bernoulliOne ψ :=
  centeredSawtooth_transform_eq_bernoulliOne hm hψ

/-- Exact primitive separation for an arbitrary finite function and every
residue multiplier. -/
theorem exact_primitive_gauss_separation
    {m : ℕ} [NeZero m] (f : ZMod m → ℂ)
    {ψ : Character m} (hψ : ψ.IsPrimitive) (k : ZMod m) :
    twistedTransform f ψ k = ψ⁻¹ k * twistedTransform f ψ 1 :=
  twistedTransform_eq_inv_mul f hψ k

/-- Exact twisted-sawtooth identity, including nonunit multipliers. -/
theorem exact_twisted_sawtooth
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : Character m} (hχ : χ.IsPrimitive) (k : ZMod m) :
    twistedTransform centeredSawtooth χ⁻¹ k =
      χ k * bernoulliOne χ⁻¹ :=
  twistedSawtooth_evaluation hm hχ k

/-- The manuscript's primitive carry-boundary factorization. -/
theorem exact_carry_boundary_factorization
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (w : ZMod m → ℂ) {χ : Character m} (hχ : χ.IsPrimitive) :
    carryTransform w χ =
      -(bernoulliOne χ⁻¹ * cellBoundaryFlux w χ) :=
  carryBoundary_factorization hm w hχ

/-- Every even character channel vanishes. -/
theorem exact_even_channel_vanishes
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (w : ZMod m → ℂ) (χ : Character m) (hχ : χ.Even) :
    carryTransform w χ = 0 :=
  carryTransform_even_zero hm w χ hχ

/-- Constant weights have no carry spectrum. -/
theorem exact_constant_weight_vanishes
    {m : ℕ} [NeZero m] (c : ℂ) (χ : Character m) :
    carryTransform (fun _ => c) χ = 0 :=
  constant_carryTransform_zero c χ

/-- The cell flux is exactly the cyclic signed-boundary pairing. -/
theorem exact_signed_boundary_pairing
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (χ : Character m) :
    cellBoundaryFlux w χ =
      ∑ x : ZMod m, signedBoundary w x * χ x :=
  cellBoundaryFlux_eq_boundary_pairing w χ

/-- All ordinary character fluxes reconstruct the boundary at every unit. -/
theorem exact_unit_boundary_reconstruction
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (u : UnitClass m) :
    inverseCharacterTransform (ordinaryBoundaryFlux w) u =
      unitBoundarySignal w u :=
  unitBoundary_reconstruction w u

/-- Equality of every ordinary flux is equivalent to equality of the unit
boundary derivatives. -/
theorem exact_unit_boundary_determinacy
    {m : ℕ} [NeZero m] (w₁ w₂ : ZMod m → ℂ) :
    (∀ χ : Character m,
      ordinaryBoundaryFlux w₁ χ = ordinaryBoundaryFlux w₂ χ) ↔
    unitBoundarySignal w₁ = unitBoundarySignal w₂ :=
  ordinaryBoundaryFlux_injective_on_unit_boundary w₁ w₂

/-- A boundary supported only on nonunits has no primitive transform. -/
theorem exact_nonunit_boundary_invisibility
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (w : ZMod m → ℂ)
    (hunit : ∀ u : UnitClass m, signedBoundary w u.val = 0)
    {χ : Character m} (hχ : χ.IsPrimitive) :
    carryTransform w χ = 0 :=
  no_unit_boundary_primitive_transform hm w hunit hχ

/-- Parseval for the complete finite carry spectrum. -/
theorem exact_carry_spectrum_parseval
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) :
    ∑ χ : Character m, ‖carryTransform w χ‖ ^ 2 =
      m.totient * ∑ u : UnitClass m, ‖unitCarrySignal w u‖ ^ 2 :=
  carryTransform_parseval w

/-- Exact finite interval Stokes formula. -/
theorem exact_interval_stokes (f : ℕ → ℂ) (start length : ℕ) :
    (∑ i ∈ Finset.range length,
      (f (start + i + 1) - f (start + i))) =
        f (start + length) - f start :=
  intervalStokes f start length

/-- All eight terminal-boundary certificates declared in the manuscript pass. -/
theorem exact_terminal_boundary_certificates :
    terminalBoundaryCertificate 3 2 = true ∧
    terminalBoundaryCertificate 3 3 = true ∧
    terminalBoundaryCertificate 5 2 = true ∧
    terminalBoundaryCertificate 5 3 = true ∧
    terminalBoundaryCertificate 7 2 = true ∧
    terminalBoundaryCertificate 7 3 = true ∧
    terminalBoundaryCertificate 11 2 = true ∧
    terminalBoundaryCertificate 11 3 = true :=
  terminal_boundary_certificates

/-- Exact proper-conductor leakage in the base-fifteen example. -/
theorem exact_base_fifteen_proper_leakage :
    baseFifteenPushdown 45 1 = 1 ∧
      baseFifteenPushdown 75 1 = 1 :=
  base_fifteen_proper_pushdowns_nonzero

/-- Complete exact base-fifteen conductor ledger. -/
theorem exact_base_fifteen_conductor_ledger :
    baseFifteenLedgerDifference 15 = 0 ∧
    baseFifteenLedgerDifference 45 = 32 ∧
    baseFifteenLedgerDifference 75 = 32 ∧
    baseFifteenLedgerDifference 225 = 32 ∧
    ((120 : ℤ) * 32 - 40 * 32 - 24 * 32 + 8 * 0) / 2 = 896 ∧
    (896 : ℤ) / 32 = 28 ∧
    terminalCollisionPointCount 15 2 = 15 ∧
    terminalSupportIsSingleton 15 2 = true ∧
    terminalFormalBoundaryCount 15 2 = 30 :=
  base_fifteen_conductor_ledger

#check exact_sawtooth_odd
#check exact_bernoulli_transform
#check exact_primitive_gauss_separation
#check exact_twisted_sawtooth
#check exact_carry_boundary_factorization
#check exact_even_channel_vanishes
#check exact_constant_weight_vanishes
#check exact_signed_boundary_pairing
#check exact_unit_boundary_reconstruction
#check exact_unit_boundary_determinacy
#check exact_nonunit_boundary_invisibility
#check exact_carry_spectrum_parseval
#check exact_interval_stokes
#check exact_terminal_boundary_certificates
#check exact_base_fifteen_proper_leakage
#check exact_base_fifteen_conductor_ledger

-- Long-division and finite-prefix reduction.
#check digitReadout_eq_quotient_mod
#check greedyDigitDifference_eq_readout
#check prefixIndex_digit
#check finitePrefixSliceIdentity
#check cylinderToCarryCount
#check finitePrefixCenteredIdentity

-- Exact endpoint normalization.
#check sawtooth_carry_step
#check endpoint_normalization
#check unit_constant_is_spectrally_invisible

-- Induced-character depth and boundary factorization.
#check ambientConductorDepthWeight_exact_response
#check conductorDepth_carry_factorization
#check conductorDepth_boundary_factorization
#check ambient_primePower_conductor_channel

-- Lifted boundary pushforward and higher-conductor invisibility.
#check blockLiftBoundary_at_dilated_point
#check blockLiftBoundary_zero_off_dilated_support
#check primitiveTransform_blockLift_zero

-- Universal boundary mean law.
#check primitiveOddKernel_eq_primePowerKernel
#check boundaryMeanCriterion_average
#check terminalUnitBoundary_meanLaw

-- General conductor ledger and complete prime-power energy decomposition.
#check primitiveOddBoundaryMoment_conductorLedger
#check odd_character_has_primitive_source
#check primitiveOddSourceEquiv
#check primePower_energy_decomposition

end NField.Papers.CarryBoundariesAndBernoulliSpectra
