/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTransform
import NField.Alignment.CenteredCollisionClosure
import NField.Alignment.CollisionPrimeAnalyticModel
import NField.Alignment.CollisionZeroObstruction

/-!
# The Collision Transform

Reader-facing theorem map for the Lean companion to
`papers/the_collision_transform.tex`.

## Checked here

* The direct all-lag digit-collision deviation reduces to the exact finite
  table modulo `b^(ell+1)`, with its diagonal cardinality and concrete
  reflection law.
* Natural reduction to the base unit group is surjective and commutes with
  negation.  Centering its fibers gives a zero-sum, exactly odd signal.
* Finite Fourier inversion is exact.  Every active channel is odd,
  nonprincipal, and does not descend to the base.
* For a prime base at lag one, Lean proves the stronger stated gate: every
  active character modulo `b^2` is primitive and odd.
* Every finite weighted packet decomposes exactly into its character
  channels.  The common class term cancels from every zero-sum signal.
* The signs in the Euler-product decomposition are proved as an exact finite
  algebraic identity.
* The zero ledger is identified with the weighted residue sum.  A vanishing
  holomorphic residue balance forces a zero ledger, while one isolated active
  channel with positive multiplicity has a nonzero ledger.
* The declared 468 direct collision/table comparisons are checked exactly.

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

The manuscript rewrites its analytic formulas using the unique primitive
ancestors of the active characters.  The selected analytic formulas and
zero-obstruction theorem currently use characters at the original collision
modulus.  Reindexing the coefficients, finite prime correction, and zero
multiplicities through primitive ancestors remains an explicit assembly
obligation.  The general primitive-inversion formula and the printed
primitive-ancestor versions of the analytic claims are therefore not
reported as closed by these selections.  The existing prime-base, lag-one
primitive gate remains proved.

The terminal prime window is software evidence and is not a Lean proof
premise.  The collision-boundary statement remains a conjecture.  This
companion does not claim full manuscript coverage.
-/

namespace NField.Papers.CollisionTransform

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionTransform

/-- The first-last collision diagonal has exactly `b^ell` cells. -/
theorem exact_diagonal_cardinality {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  allLagDiagonal_card hb2 hell

/-- Exact finite-table determination after the diagonal-slice reduction. -/
theorem exact_finite_table {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  allLagSliceDeviation_eq_table hb2 hell ha hcop

/-- The intrinsic digit-collision deviation itself equals the exact table. -/
theorem exact_direct_finite_table {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop

/-- Complementary unit classes have exact table sum `-1`. -/
theorem exact_table_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 :=
  allLagTable_reflection hb2 hell ha halt hcop

/-- Every literal reduction fiber contains exactly `b^ell` unit classes. -/
theorem exact_fiber_cardinality {b ell u : ℕ}
    (hb2 : 2 ≤ b) (hu : u ∈ reducedResidues b) :
    (tableFiber b ell u).card = b ^ ell :=
  tableFiber_card hb2 hu

/-- Reflected natural fiber means sum exactly to `-1`. -/
theorem exact_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  natural_fiber_mean_reflection hb2 hell u

/-- Every natural reduction fiber has centered sum zero. -/
theorem exact_centered_fiber_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
        centeredCollisionTransform b ell a = 0 :=
  natural_centering_fiber_sum_zero u

/-- The naturally centered table has zero total mass. -/
theorem exact_centered_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centeredCollisionTransform b ell a = 0 :=
  centeredCollisionTransform_sum_zero

/-- The naturally centered table is exactly odd under reflection. -/
theorem exact_centered_oddness
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a :=
  centeredCollisionTransform_odd hb2 hell a

/-- Exact inversion of the finite collision transform. -/
theorem exact_transform_inversion
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (a : UnitClass (allLagModulus b ell)) :
    ∑ χ : Character (allLagModulus b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ * χ a.val =
      centeredCollisionTransform b ell a :=
  collisionCoefficient_inversion (centeredCollisionTransform b ell) a

/-- Every even coefficient vanishes exactly. -/
theorem exact_even_coefficient_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  centeredCollisionTransform_even_zero hb2 hell χ heven

/-- Every coefficient descending through the base vanishes exactly. -/
theorem exact_base_factored_coefficient_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) (hfactor : BaseFactored χ) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  centeredCollisionTransform_baseFactored_zero χ hfactor

/-- Every active channel passes the full finite spectral gate. -/
theorem exact_spectral_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    {χ : Character (allLagModulus b ell)}
    (hactive : χ ∈ transformActiveCharacters b ell) :
    χ.Odd ∧ ¬BaseFactored χ ∧ χ ≠ 1 :=
  ⟨activeCharacter_odd hb2 hell hactive,
    activeCharacter_not_baseFactored hactive,
    activeCharacter_ne_one hb2 hell hactive⟩

/-- At a prime base and lag one every active channel is primitive and odd. -/
theorem exact_prime_base_gate
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)}
    (hactive : χ ∈ transformActiveCharacters b 1) :
    χ.IsPrimitive ∧ χ.Odd :=
  primeBase_active_primitive_and_odd hb hactive

/-- Exact character decomposition of any finite weighted packet. -/
theorem exact_finite_prime_packet
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass (allLagModulus b ell))
    (weight : ι → ℂ) :
    ∑ i, centeredCollisionTransform b ell (residue i) * weight i =
      ∑ χ : Character (allLagModulus b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ *
          ∑ i, χ (residue i).val * weight i :=
  transform_finite_packet_decomposition residue weight

/-- The common arithmetic-progression term cancels from a zero-sum signal. -/
theorem exact_common_term_cancellation
    {α : Type*} [Fintype α]
    (f remainder : α → ℂ) (common : ℂ) (hsum : ∑ a, f a = 0) :
    ∑ a, f a * (common + remainder a) =
      ∑ a, f a * remainder a :=
  commonClassTerm_cancels f remainder common hsum

/-- Exact signs in the finite Euler-product decomposition. -/
theorem exact_euler_product_signs
    {ι : Type*} [Fintype ι]
    (C P logL H : ι → ℂ) (F E : ℂ)
    (hprime : F + E = ∑ i, C i * P i)
    (hEuler : ∀ i, P i = logL i - H i) :
    F = (∑ i, C i * logL i) - (∑ i, C i * H i) - E :=
  collisionEulerProduct_decomposition C P logL H F E hprime hEuler

/-- The weighted local-residue balance is exactly the zero ledger. -/
theorem exact_zero_ledger_balance
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (multiplicity : Character q → ℕ) (residue : Character q → ℂ)
    (hresidue : ∀ χ ∈ activeCharacters F,
      residue χ = (multiplicity χ : ℂ))
    (hbalance : ∑ χ ∈ activeCharacters F,
      collisionCoefficient F χ * residue χ = 0) :
    collisionZeroLedger F multiplicity = 0 :=
  collisionZeroLedger_eq_zero_of_residue_balance
    F multiplicity residue hresidue hbalance

/-- A single isolated active positive-multiplicity channel cannot cancel. -/
theorem isolated_effective_zero_cannot_hide
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (multiplicity : Character (allLagModulus b ell) → ℕ)
    (χ₀ : Character (allLagModulus b ell))
    (hactive : χ₀ ∈ transformActiveCharacters b ell)
    (hmult : 0 < multiplicity χ₀)
    (hisolated : ∀ χ ∈ transformActiveCharacters b ell,
      χ ≠ χ₀ → multiplicity χ = 0) :
    collisionZeroLedger (centeredCollisionTransform b ell) multiplicity ≠ 0 :=
  isolatedTransformChannel_nonzero_ledger multiplicity χ₀
    hactive hmult hisolated

/-- The declared direct verification set contains exactly 468 cases. -/
theorem declared_direct_check_count :
    ∑ b ∈ transformVerificationBases,
      (reducedResidues (allLagModulus b 1)).card *
        transformVerificationRepresentatives.card = 468 :=
  transform_direct_check_case_count

/-- Every declared direct collision count agrees with the finite table. -/
theorem declared_direct_table_agreement :
    ∀ b ∈ transformVerificationBases,
      ∀ a ∈ reducedResidues (allLagModulus b 1),
        ∀ t ∈ transformVerificationRepresentatives,
          directAllLagDeviation b 1 (allLagModulus b 1 * t + a) =
            allLagTable b 1 a :=
  selected_base_direct_collision_regression

#check exact_diagonal_cardinality
#check exact_finite_table
#check exact_direct_finite_table
#check exact_table_reflection
#check exact_fiber_cardinality
#check exact_fiber_mean_reflection
#check exact_centered_fiber_zero
#check exact_centered_sum_zero
#check exact_centered_oddness
#check exact_transform_inversion
#check exact_even_coefficient_zero
#check exact_base_factored_coefficient_zero
#check exact_spectral_gate
#check exact_prime_base_gate
#check exact_finite_prime_packet
#check exact_common_term_cancellation
#check exact_euler_product_signs
#check exact_zero_ledger_balance
#check isolated_effective_zero_cannot_hide
#check declared_direct_check_count
#check declared_direct_table_agreement


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

end NField.Papers.CollisionTransform
