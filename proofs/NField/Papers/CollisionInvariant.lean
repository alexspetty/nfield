/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionInvariant
import NField.Alignment.CenteredCollisionClosure

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

## Boundary

The manuscript's stronger collision-coordinate identity expressing the count
as twice a positive-displacement count is not yet assembled here.  Parity is
proved independently, while the exact zero gate and its `b-1` family are
inherited from the bin-derangement companion.

The two symbolic values used to prove optimality of `b^(ell+1)` among base
powers remain an assembly target.  The general composite-modulus version of
the initial conjugation lemma is likewise not yet generalized from the current
prime statement.  No boundary is hidden behind an unchecked declaration.

No contradiction with the manuscript appeared in the formalized layer.
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

end NField.Papers.CollisionInvariant
