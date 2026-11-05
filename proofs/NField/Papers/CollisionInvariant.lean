/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionInvariant
import NField.Alignment.FloorDigitBinDistribution
import NField.Alignment.CenteredCollisionClosure
import NField.Alignment.CompositeCollisionConjugation
import NField.Alignment.BasePowerOptimality
import NField.Alignment.CollisionInvariantDetails

/-!
# The Collision Invariant

Reader-facing theorem map for the Lean companion to
`papers/the_collision_invariant.tex`.

## Checked here

* The prime digit-bin partition is conjugated to an ordinary congruence
  partition, and the intrinsic collision count equals the transformed count.
* Every nonzero prime multiplier has an even collision count.  This is proved
  directly by a fixed-point-free negation pairing.
* The collision-free multipliers are exactly the displayed rational family,
  and that family has cardinality `b-1` independently of the prime.
* At every positive lag, the exact diagonal has `b^ell` entries and the
  endpoint-corrected direct digit-collision deviation reduces to a table
  modulo `b^(ell+1)`.
* The concrete all-lag table has exact reflection sum `-1`; its average over
  all unit classes is therefore exactly `-1/2`.
* Negation carries every interior wrapping set bijectively to its complement.
  Lean derives the exact cardinality `phi(m)/2` for all `m >= 3` and
  `1 <= n <= m-2`.

## Complete finite correspondence

The composite coprime conjugation, positive-displacement count and both
sharpness witnesses are proved for the actual digit word and all-lag table.
The lower-power obstruction and diagonal half-group corollary are explicit.
The manuscript's numerical sweeps remain finite computational evidence.

-/

namespace NField.Papers.CollisionInvariant

open scoped BigOperators
open NField.CollisionDefinition
open NField.Alignment.SpectralPower
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangements
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionInvariant
open NField.Alignment.CenteredCollisionClosure

/-- Multiplication by the base converts equality of prime digit bins into
equality of transformed residues modulo the base. -/
theorem exact_prime_conjugation {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (r s : ZMod p) :
    digitBin b p r.val = digitBin b p s.val ↔
      ((b : ZMod p) * r).val % b =
        ((b : ZMod p) * s).val % b :=
  digit_eq_iff_transformed_mod hb hp hbp r s

/-- The intrinsic prime collision count is the transformed congruence count. -/
theorem exact_collision_congruence {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) (hg : g ≠ 0) :
    collisionCount (primeDigitWord b p hb hp.pos) g =
      transformedCollisionCount b p g :=
  collisionCount_eq_transformedCollisionCount hb hp hbp g hg

/-- Bilateral parity for every nonzero prime multiplier, including one. -/
theorem exact_bilateral_parity {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg : g ≠ 0) :
    Even (collisionCount (primeDigitWord b p (by omega) hp.pos) g) :=
  NField.Alignment.CollisionInvariant.collisionCount_even hb2 hp hbp hg

/-- The collision-free set is exactly the manuscript's rational family. -/
theorem exact_gate_family {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) :
    g ∈ derangingFamily b p ↔
      g ≠ 0 ∧ collisionCount
        (primeDigitWord b p (by omega) hp.pos) g = 0 :=
  mem_derangingFamily_iff hb2 hp hbp g

/-- The gate width is exactly `b-1`, independent of the prime. -/
theorem exact_gate_width {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    (derangingFamily b p).card = b - 1 :=
  derangingFamily_card hb hp hbp

/-- The encoded diagonal is exactly equality of the leading and trailing
base digits of the all-lag slice index. -/
theorem exact_diagonal_membership {b ell n : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hn : n < allLagModulus b ell) :
    n ∈ allLagDiagonal b ell ↔ n / b ^ ell = n % b :=
  mem_allLagDiagonal_iff_quotient_eq_remainder hb2 hell hn

/-- The all-lag diagonal has exactly `b^ell` entries. -/
theorem exact_diagonal_card {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  allLagDiagonal_card hb2 hell

/-- Both endpoint slices belong to the all-lag diagonal. -/
theorem exact_diagonal_endpoints {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    0 ∈ allLagDiagonal b ell ∧
      allLagModulus b ell - 1 ∈ allLagDiagonal b ell :=
  ⟨allLagDiagonal_zero_mem hb2, allLagDiagonal_last_mem hb2 hell⟩

/-- The exact all-lag finite table depends only on the class modulo
`b^(ell+1)` after diagonal-slice reduction. -/
theorem exact_finite_determination {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  collisionInvariant_finite_determination hb2 hell ha hcop

/-- The intrinsic digit-collision deviation itself equals the exact finite
table throughout each coprime progression. -/
theorem exact_direct_finite_determination {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop

/-- The exact finite table satisfies the manuscript's reflection identity. -/
theorem exact_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 :=
  allLagTable_reflection hb2 hell ha halt hcop

/-- The grand mean of the exact table over all unit classes is `-1/2`. -/
theorem exact_grand_mean {b ell : ℕ}
    [NeZero (allLagModulus b ell)] (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (Fintype.card (UnitClass (allLagModulus b ell)) : ℂ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b ell), allLagUnitTable b ell a =
      -1 / 2 :=
  collisionInvariant_grand_mean hb2 hell

/-- Every interior wrapping set contains exactly half of the unit group. -/
theorem exact_half_group {m n : ℕ} [NeZero m]
    (hm3 : 3 ≤ m) (hnlo : 1 ≤ n) (hnhi : n ≤ m - 2) :
    Fintype.card (WrappingClass m (n + 1)) = m.totient / 2 :=
  interiorWrappingClass_card hm3 hnlo hnhi


/-- Base conjugation for arbitrary coprime moduli. -/
theorem exact_coprime_conjugation {b N : ℕ}
    (hb : 0 < b) (hcop : b.Coprime N) (hbN : b < N) [NeZero N]
    (r s : ZMod N) :
    digitBin b N r.val = digitBin b N s.val ↔
      ((b : ZMod N) * r).val % b = ((b : ZMod N) * s).val % b :=
  NField.Alignment.CompositeCollisionConjugation.digit_eq_iff_transformed_mod_coprime
    hb hcop hbN r s

/-- The complete collision congruence for a unit at a composite modulus. -/
theorem exact_coprime_collision_congruence {b N : ℕ}
    (hb : 0 < b) (hcop : b.Coprime N) (hbN : b < N) [NeZero N]
    (g : (ZMod N)ˣ) :
    collisionCount (primeDigitWord b N hb (NeZero.pos N)) g.val =
      transformedCollisionCount b N g.val :=
  NField.Alignment.CompositeCollisionConjugation.collisionCount_eq_congruence_coprime
    hb hcop hbN g

/-- The collision count is twice the actual positive-displacement count. -/
theorem exact_positive_collision_coordinate {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p (by omega) hp.pos) g =
      2 * ((Finset.Icc 1 ((p - 1) / b)).filter
        (fun j => j * b < j * gateParameter b p g % p)).card :=
  NField.Alignment.SilentPrimesClosure.collision_coordinate_positive_comparisons
    hb2 hp hbp hg0 hg1

/-- The manuscript's two unit classes have the displayed unequal values. -/
theorem exact_optimal_base_power_witnesses {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagModulus b ell - b ^ ell + 1).Coprime (allLagModulus b ell) ∧
    1 ≡ allLagModulus b ell - b ^ ell + 1 [MOD b ^ ell] ∧
    allLagTable b ell 1 = 0 ∧
    allLagTable b ell (allLagModulus b ell - b ^ ell + 1) =
      -(((b - 1) * b ^ (ell - 1) : ℕ) : ℤ) :=
  NField.Alignment.BasePowerOptimality.optimal_base_power_witnesses hb2 hell

/-- Every smaller base power fails to determine the actual unit table. -/
theorem exact_no_lower_base_power {b ell k : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (hk : k ≤ ell) :
    ¬ ∃ f : ℕ → ℤ, ∀ a, 0 < a → a < allLagModulus b ell →
      a.Coprime (allLagModulus b ell) → allLagTable b ell a = f (a % b ^ k) :=
  NField.Alignment.BasePowerOptimality.allLagTable_not_factor_lower_power hb2 hell hk

/-- Every nonendpoint diagonal wrapping set has half the unit classes. -/
theorem exact_diagonal_half_group {b ell n : ℕ}
    [NeZero (allLagModulus b ell)] (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hn : n ∈ allLagDiagonal b ell) (hn0 : n ≠ 0)
    (hnlast : n ≠ allLagModulus b ell - 1) :
    Fintype.card (WrappingClass (allLagModulus b ell) (n + 1)) =
      (allLagModulus b ell).totient / 2 :=
  NField.Alignment.CollisionInvariantDetails.diagonal_wrapping_card hb2 hell hn hn0 hnlast

#check exact_prime_conjugation
#check exact_collision_congruence
#check exact_bilateral_parity
#check exact_gate_family
#check exact_gate_width
#check exact_diagonal_membership
#check exact_diagonal_card
#check exact_diagonal_endpoints
#check exact_finite_determination
#check exact_direct_finite_determination
#check exact_reflection
#check exact_grand_mean
#check exact_half_group

#check exact_coprime_conjugation
#check exact_coprime_collision_congruence
#check exact_positive_collision_coordinate
#check exact_optimal_base_power_witnesses
#check exact_no_lower_base_power
#check exact_diagonal_half_group
#check NField.Alignment.digitBinPopulation_eq_boundary_sub
#check NField.Alignment.digitBinPopulation_eq_quotient_or_succ
#check NField.Alignment.enlargedDigitBins_card
#check NField.Alignment.BinDerangementsClosure.digitBinPopulation_floor_formula
#check NField.Alignment.BinDerangements.digit_decomposition
#check NField.Alignment.BinDerangements.gateParameter_mul_one_sub
#check NField.Alignment.BinDerangements.transformedCollisionCount_eq_zero_iff_parameter_lt
#check NField.Alignment.SilentPrimesClosure.positive_point_collision
#check NField.Alignment.SilentPrimesClosure.negative_point_collision
#check NField.Alignment.SilentPrimesClosure.collision_has_positive_coordinate
#check NField.Alignment.SilentPrimesClosure.transformedCollisionSet_eq_coordinate_points
#check NField.Alignment.SilentPrimesClosure.coordinate_points_card
#check NField.Alignment.CenteredCollisionClosure.encodedPrefixDigit_allLag_first
#check NField.Alignment.CenteredCollisionClosure.encodedPrefixDigit_allLag_last
#check NField.Alignment.CenteredCollisionClosure.digitReadout_eq_transported_digitBin
#check NField.Alignment.CenteredCollisionClosure.direct_allLag_collision_iff_prefix_cell_mem
#check NField.Alignment.CenteredCollisionClosure.directAllLagCollisionCount_eq_allLagSliceScore
#check NField.Alignment.CollisionFluctuationSum.floorJump_add_modulus_mul
#check NField.Alignment.BasePowerOptimality.sharp_witness_residue
#check NField.Alignment.BasePowerOptimality.sharp_witness_bounds
#check NField.Alignment.BasePowerOptimality.sharp_witness_coprime
#check NField.Alignment.BasePowerOptimality.sharp_witness_quotient
#check NField.Alignment.BasePowerOptimality.allLagTable_one
#check NField.Alignment.BasePowerOptimality.allLagTable_sharp_witness
#check NField.Alignment.BasePowerOptimality.sharp_witness_lower_congruence
#check NField.Alignment.CollisionPeriodicTable.complement_div
#check NField.Alignment.CollisionPeriodicTable.floorJump_complement_interior
#check NField.Alignment.PrimeCarryTableColumnLaw.floorJump_last_eq_one
#check NField.Alignment.CollisionTransformStrip.allLag_jump_pair_value
#check NField.Alignment.CollisionTransformStrip.allLag_jump_pair_sum
#check NField.Alignment.CollisionTransformStrip.allLag_quotient_complement
#check NField.Alignment.CollisionInvariant.wraps_neg_iff
#check NField.Alignment.CollisionInvariantDetails.collisionCount_eq_natural_card
#check NField.Alignment.CollisionInvariantDetails.directAllLagCollisionCount_eq_natural_card
#check NField.Alignment.CollisionInvariantDetails.identity_collision_count

end NField.Papers.CollisionInvariant
