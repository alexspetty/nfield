/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CenteredCollisionClosure
import NField.Alignment.CollisionPrimeAnalyticModel
import NField.Alignment.CollisionZeroObstruction

/-!
# The Collision Transform and the Critical Strip

Reader-facing theorem map for the Lean companion to
`papers/collision_transform_strip.tex`.

## Checked here

* The first/last-digit diagonal has exactly `b^ell` indices.  The intrinsic
  digit collision is proved equal to its diagonal slice score, and the direct
  deviation is the exact finite table modulo `b^(ell+1)`.
* Complementary floor increments are proved at every diagonal index.  Their
  sum gives the concrete all-lag reflection law
  `T(b,ell,a) + T(b,ell,q-a) = -1` on every unit class.
* Every coarse unit fiber has exactly `b^ell` representatives.  The table is
  also realized on the actual unit group modulo `q`, where negation obeys the
  same reflection law.
* Natural reduction to the base unit group is surjective.  Its fiber
  centering has zero sum on every fiber and makes the unit-group signal
  exactly odd.
* The normalized Dirichlet-character coefficient is inverted exactly.  Even
  channels and channels factored through the coarse reduction have zero
  coefficient for the centered signal.
* Every finite weighted prime packet decomposes exactly into its character
  channels.  The Euler-product signs and zero-ledger residue algebra are
  checked exactly.  A positive multiplicity in one isolated active channel
  gives a nonzero ledger.
* Exact evaluation checks the manuscript's 468 direct collision/table cases
  across bases `3, 5, 7, 10, 12` and three representatives per unit class.

## Checked analytic results

The intrinsic collision series converges absolutely for `Re(s) > 1` and has
an ordinary ordered reciprocal-prime limit at `s = 1`.  Its expansion in
characters at the original collision modulus uses the actual Euler-product
logarithms and exact finite prime correction.  The logarithms exponentiate
to the Dirichlet `L`-functions and tend to zero as the real part tends to
infinity.  The higher-prime-power double series converges absolutely and
uniformly on each smaller half-plane to the right of one half; its sum is
holomorphic there, and the finite correction is entire.

The selected continuation theorem uses an open simply connected domain to
the right of one half, a nonempty connected overlap with `Re(s) > 1`, and
nonvanishing of every active `L`-function.  Its conclusion is holomorphic
continuation on that domain.  The ordinary Dirichlet-series theorem proves
holomorphy and locally uniform convergence to the right of an ordinary
convergence point.  The zero-obstruction theorem uses actual analytic zero
multiplicities: ordinary convergence at a real `sigma >= 1/2` forces the
weighted zero ledger to vanish at every point with real part greater than
`sigma`.  The selected supporting theorems prove the logarithmic residues,
cleared analytic identity, and finite weighted multiplicity cancellation.

## Remaining analytic boundary

The explicit-formula estimates for prime character sums and their
zero-free-penetration consequence remain unformalized here.  In particular,
holomorphic continuation alone is not a proof of ordinary convergence on
the continued domain.  The stated conditional convergence in the open
half-plane to the right of one half still requires the prime-sum estimates.

The analytic expansions and weighted zero ledger selected here use the
active characters at the original collision modulus.  The passage from
an isolated zero of a primitive ancestor to the corresponding original-
modulus zero multiplicities remains an assembly obligation.  The exact
finite isolated-channel ledger argument is retained separately.

The prime-window computation through ten million is software evidence and
is not a Lean proof premise.  The collision-boundary statement remains a
conjecture.  This companion does not claim full manuscript coverage.
-/

namespace NField.Papers.CollisionTransformStrip

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.CollisionTransform
open NField.Alignment.NeutralityTheorem

/-- Exact all-lag periodicity after reduction to the diagonal slice score. -/
theorem finite_table_periodicity {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  allLagSliceDeviation_eq_table hb2 hell ha hcop

/-- The intrinsic digit-collision deviation is the exact all-lag table
throughout every coprime progression. -/
theorem direct_finite_table_determination
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop

/-- The first/last-digit diagonal has exactly `b^ell` coordinates. -/
theorem exact_diagonal_cardinality {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  allLagDiagonal_card hb2 hell

/-- Concrete reflection for every all-lag unit representative. -/
theorem exact_all_lag_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 :=
  allLagTable_reflection hb2 hell ha halt hcop

/-- Every coarse unit fiber contains exactly `b^ell` representatives. -/
theorem exact_reduction_fiber_cardinality {b ell u : ℕ}
    (hb2 : 2 ≤ b) (hu : u ∈ reducedResidues b) :
    (tableFiber b ell u).card = b ^ ell :=
  tableFiber_card hb2 hu

/-- Reflection on the actual unit group modulo `b^(ell+1)`. -/
theorem exact_unit_table_reflection {b ell : ℕ}
    [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (r : UnitClass (allLagModulus b ell)) :
    allLagUnitTable b ell r + allLagUnitTable b ell (-r) = -1 :=
  allLagUnitTable_reflection hb2 hell r

/-- Every natural reduction fiber has exact centered sum zero. -/
theorem exact_natural_fiber_centering
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
        centeredCollisionTransform b ell a = 0 :=
  natural_centering_fiber_sum_zero u

/-- Natural fiber centering has zero total mass. -/
theorem exact_centered_total_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a : UnitClass (allLagModulus b ell),
      centeredCollisionTransform b ell a = 0 :=
  centeredCollisionTransform_sum_zero

/-- Natural fiber means over reflected classes sum to `-1`. -/
theorem exact_natural_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  natural_fiber_mean_reflection hb2 hell u

/-- Natural centering makes the concrete table exactly odd. -/
theorem exact_natural_centered_oddness
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a :=
  natural_centered_reflection hb2 hell a

/-- Exact inversion of the normalized collision-character coefficients. -/
theorem exact_character_inversion {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (r : UnitClass q) :
    ∑ χ : Character q, collisionCoefficient F χ * χ r.val = F r :=
  collisionCoefficient_inversion F r

/-- Every even character vanishes for the naturally centered table. -/
theorem exact_natural_even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  natural_even_character_gate hb2 hell χ heven

/-- Every character descending to the base vanishes for the naturally
centered table. -/
theorem exact_natural_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) (hfactor : BaseFactored χ) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  natural_base_factored_character_gate χ hfactor

/-- Exact character decomposition of every finite weighted prime packet. -/
theorem finite_packet_character_decomposition
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (F : UnitClass q → ℂ) (residue : ι → UnitClass q)
    (weight : ι → ℂ) :
    ∑ i, F (residue i) * weight i =
      ∑ χ : Character q, collisionCoefficient F χ *
        ∑ i, χ (residue i).val * weight i :=
  finite_prime_packet_decomposition F residue weight

/-- The signs in the Euler-product decomposition are exact finite algebra. -/
theorem exact_euler_product_bookkeeping
    {ι : Type*} [Fintype ι]
    (C P logL H : ι → ℂ) (F E : ℂ)
    (hprime : F + E = ∑ i, C i * P i)
    (hEuler : ∀ i, P i = logL i - H i) :
    F = (∑ i, C i * logL i) - (∑ i, C i * H i) - E :=
  collisionEulerProduct_decomposition C P logL H F E hprime hEuler

/-- A zero residue balance is exactly a zero collision ledger. -/
theorem exact_zero_ledger_from_residue_balance
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (multiplicity : Character q → ℕ) (residue : Character q → ℂ)
    (hresidue : ∀ χ ∈ activeCharacters F,
      residue χ = (multiplicity χ : ℂ))
    (hbalance : ∑ χ ∈ activeCharacters F,
      collisionCoefficient F χ * residue χ = 0) :
    collisionZeroLedger F multiplicity = 0 :=
  collisionZeroLedger_eq_zero_of_residue_balance
    F multiplicity residue hresidue hbalance

/-- A single active positive-multiplicity channel cannot cancel in the ledger. -/
theorem isolated_channel_ledger_nonzero
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (multiplicity : Character q → ℕ) (χ₀ : Character q)
    (hactive : collisionCoefficient F χ₀ ≠ 0)
    (hmult : 0 < multiplicity χ₀)
    (hisolated : ∀ χ ∈ activeCharacters F, χ ≠ χ₀ → multiplicity χ = 0) :
    collisionZeroLedger F multiplicity ≠ 0 :=
  isolated_active_channel_has_nonzero_ledger F multiplicity χ₀
    hactive hmult hisolated

/-- The declared direct verification set contains exactly 468 cases. -/
theorem direct_check_count :
    ∑ b ∈ transformVerificationBases,
      (reducedResidues (allLagModulus b 1)).card *
        transformVerificationRepresentatives.card = 468 :=
  transform_direct_check_case_count

/-- All 468 direct digit-collision checks agree with the finite table. -/
theorem direct_collision_table_check :
    ∀ b ∈ transformVerificationBases,
      ∀ a ∈ reducedResidues (allLagModulus b 1),
        ∀ t ∈ transformVerificationRepresentatives,
          directAllLagDeviation b 1 (allLagModulus b 1 * t + a) =
            allLagTable b 1 a :=
  selected_base_direct_collision_regression

#check finite_table_periodicity
#check direct_finite_table_determination
#check exact_diagonal_cardinality
#check exact_all_lag_reflection
#check exact_reduction_fiber_cardinality
#check exact_unit_table_reflection
#check exact_natural_fiber_centering
#check exact_centered_total_zero
#check exact_natural_mean_reflection
#check exact_natural_centered_oddness
#check exact_character_inversion
#check exact_natural_even_character_gate
#check exact_natural_factored_character_gate
#check finite_packet_character_decomposition
#check exact_euler_product_bookkeeping
#check exact_zero_ledger_from_residue_balance
#check isolated_channel_ledger_nonzero
#check direct_check_count
#check direct_collision_table_check


/-! ## Analytic results and their proved dependencies -/

#check NField.Alignment.PrimeEulerLog.higherPower_norm_summable
#check NField.Alignment.PrimeEulerLog.exp_eulerLog_eq_LFunction
#check NField.Alignment.PrimeEulerLog.primeSeries_eq_eulerLog_sub_higherPower
#check NField.Alignment.PrimeEulerLog.higherPower_analyticOnNhd
#check NField.Alignment.PrimeHigherPowers.higherTerm_norm_summable
#check NField.Alignment.PrimeHigherPowers.higherTerm_tendstoUniformlyOn
#check NField.Alignment.EulerLogNormalization.eulerLog_tendsto_zero
#check NField.Alignment.ComplexPrimeCharacterExpansion.periodicPrimeSeries_euler_expansion
#check NField.Alignment.ComplexPrimeCharacterExpansion.finiteCorrection_differentiable
#check NField.Alignment.HolomorphicLogBranch.exists_analytic_log_branch
#check NField.Alignment.CollisionHolomorphicContinuation.exists_collision_continuation
#check NField.Alignment.CollisionPrimeAnalyticModel.directSeries_summable
#check NField.Alignment.CollisionPrimeAnalyticModel.directSeries_euler_expansion
#check NField.Alignment.CollisionPrimeAnalyticModel.directSeries_continuation
#check NField.Alignment.CollisionPrimeAnalyticModel.direct_harmonic_boundary
#check NField.Alignment.AnalyticLogarithmicMultiplicity.tendsto_mul_logDeriv_order
#check NField.Alignment.AnalyticLogarithmicMultiplicity.LFunction_logarithmic_residue
#check NField.Alignment.AnalyticLogarithmicMultiplicity.collision_ledger_is_logarithmic_residue
#check NField.Alignment.WeightedLogarithmicIdentity.continue_cleared_identity
#check NField.Alignment.WeightedLogarithmicIdentity.weighted_order_zero
#check NField.Alignment.OrdinaryDirichletKernel.norm_difference_le
#check NField.Alignment.OrdinaryDirichletKernel.abelSum_analyticOnNhd
#check NField.Alignment.OrdinaryDirichletKernel.ordinary_convergence
#check NField.Alignment.OrdinaryDirichletKernel.ordinary_uniform_convergence
#check NField.Alignment.OrdinaryDirichletConvergence.bounded_partial_sums
#check NField.Alignment.OrdinaryDirichletConvergence.holomorphic_of_ordinary_convergence
#check NField.Alignment.OrdinaryCollisionPrimeSeries.ordinary_limit_above_one
#check NField.Alignment.OrdinaryCollisionPrimeSeries.analytic_model_of_convergence
#check NField.Alignment.CollisionZeroObstruction.ordinary_convergence_zero_ledger

end NField.Papers.CollisionTransformStrip
