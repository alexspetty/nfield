/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTransform
import NField.Alignment.CenteredCollisionClosure

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

## Analytic boundary

The proof that the reciprocal-prime series converges uses Mertens' theorem in
arithmetic progressions.  Zero-free penetration uses the explicit formula and
partial summation.  The converse obstruction uses the holomorphy theorem for
an ordinarily convergent Dirichlet series, meromorphic continuation of the
weighted logarithmic derivatives, and their local residues.  These analytic
inputs are not currently packaged in Mathlib in the manuscript's required
form.  This companion therefore checks the exact finite cancellation,
Euler-product bookkeeping, active-channel classification, residue-to-ledger
identity, and isolated-channel contradiction, but it does not claim the
ordinary convergence, zero-free penetration, continuation, or analytic
zero-cancellation theorems themselves.

The general direct digit-collision-to-slice bridge is now closed in the
reusable finite-determination layer.  The reindexing from active characters at
the displayed modulus to their unique primitive ancestors remains an explicit
assembly boundary for the general primitive-inversion formula.  The terminal
prime window is software evidence and is not a Lean proof premise.  The
collision-boundary statement remains a conjecture.  No manuscript
contradiction appeared in the formalized layer, and no unchecked declaration
is used.
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

end NField.Papers.CollisionTransform
