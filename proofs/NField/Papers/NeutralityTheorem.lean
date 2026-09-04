/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CenteredCollisionClosure

/-!
# The Neutrality Theorem

Reader-facing theorem map for the Lean companion to
`papers/neutrality_theorem.tex`.

## Checked here

* The direct digit-collision deviation is exactly the finite table on every
  coprime progression.  The all-lag diagonal has `b^ell` entries, and the
  table obeys `T(a) + T(q-a) = -1`.
* Every coarse unit fiber has exactly `b^ell` representatives.  Natural fiber
  centering has zero sum, reflected fiber means add to `-1`, and the centered
  table is odd with zero total mass.
* Canonical residue-three reflection preserves the unique fixed slice and
  exchanges the other two slices.  The fixed slice has raw mean `-1/2` when
  nonempty, while the paired raw and centered sums have the stated totals.
* When three is coprime to the base, the actual unit-group Chinese remainder
  equivalence identifies either true residue-three channel with one complete
  copy of the collision table.  Each centered channel is independently zero,
  and each raw channel has mean `-1/2`.
* When three divides the base, reduction to the coarse unit group preserves
  the true residue-three coordinate.  Each true channel is therefore a union
  of complete zero-sum fibers.
* A zero channel sum gives a zero principal finite coefficient.  At every
  finite cutoff, either nonzero residue-three channel is exactly the half-sum
  or half-difference of the total and its nontrivial mod-three twist.
* A structural exact theorem checks both independently neutral lag-one
  channels for every base from `2` through `40`.

## Analytic and computational boundary

Mertens' theorem in arithmetic progressions is not formalized in this
repository.  The separate convergence theorem at `s = 1` remains an analytic
result whose finite zero-mean premise is machine checked here.  The prime
window from one million through ten million is exact software evidence and is
not recomputed inside Lean.  Convergence below one remains open.
-/

namespace NField.Papers.NeutralityTheorem

open scoped BigOperators
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionTransform
open NField.Alignment.CenteredCollisionClosure

/-- The direct digit-collision deviation is exactly the endpoint-corrected
finite table on every coprime progression. -/
theorem direct_finite_table_determination {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 1 ≤ a)
    (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop

/-- Exact finite-table determination after the diagonal-slice reduction. -/
theorem finite_table_determination {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  allLagSliceDeviation_eq_table hb2 hell ha hcop

/-- Exact cardinality of the first/last-digit diagonal. -/
theorem exact_diagonal_cardinality {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  allLagDiagonal_card hb2 hell

/-- Exact reflection of the concrete finite table. -/
theorem exact_table_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 :=
  allLagTable_reflection hb2 hell ha halt hcop

/-- Reflection fixes the raw global mean at exactly `-1/2`. -/
theorem exact_global_raw_mean
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (Fintype.card (UnitClass (allLagModulus b ell)) : ℂ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b ell), allLagUnitTable b ell a =
      -1 / 2 :=
  allLagUnitTable_grand_mean hb2 hell

/-- Every coarse unit fiber has exactly `b^ell` representatives. -/
theorem exact_fiber_cardinality {b ell u : ℕ}
    (hb2 : 2 ≤ b) (hu : u ∈ reducedResidues b) :
    (tableFiber b ell u).card = b ^ ell :=
  tableFiber_card hb2 hu

/-- Every natural coarse reduction fiber has centered sum zero. -/
theorem exact_natural_fiber_centering
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
        centeredCollisionTransform b ell a = 0 :=
  natural_centering_fiber_sum_zero u

/-- The complete naturally centered table has zero total mass. -/
theorem exact_centered_total_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centeredCollisionTransform b ell a = 0 :=
  centeredCollisionTransform_sum_zero

/-- Means on reflected natural fibers add to `-1`. -/
theorem exact_natural_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  natural_fiber_mean_reflection hb2 hell u

/-- Natural centering makes the concrete table odd under reflection. -/
theorem exact_natural_centered_oddness
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a :=
  natural_centered_reflection hb2 hell a

/-- Every selected union of complete fibers remains exactly neutral. -/
theorem selected_fiber_union_neutral
    {α β K : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (hsurj : Function.Surjective ρ)
    (selected : β → Prop) [DecidablePred selected] :
    (∑ a, (if selected (ρ a) then centeredSignal ρ T a else 0)) = 0 :=
  centeredSignal_selected_fibers_sum_zero ρ T hsurj selected

/-- The representative and quotient coordinates reconstruct the true residue
modulo three. -/
theorem quotient_residue_three (m t a : ℕ) :
    ((m * t + a : ℕ) : ZMod 3) =
      (a : ZMod 3) + (m : ZMod 3) * (t : ZMod 3) := by
  push_cast
  ring

/-- The table modulus is at least two in every manuscript case. -/
theorem table_modulus_ge_two {b ell : ℕ} (hb2 : 2 ≤ b) :
    2 ≤ allLagModulus b ell := by
  unfold allLagModulus
  exact hb2.trans (Nat.le_pow (by omega))

/-- The reflection-fixed residue-three label is unique. -/
theorem internal_fixed_label_unique
    {m : ℕ} (j j' : ZMod 3)
    (hj : 2 * j = (m : ZMod 3))
    (hj' : 2 * j' = (m : ZMod 3)) :
    j = j' := by
  apply mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)
  exact hj.trans hj'.symm

/-- The concrete nonempty reflection-fixed internal slice has exact raw mean
`-1/2`. -/
theorem internal_fixed_slice_raw_mean
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (j : ZMod 3)
    (hfixed : 2 * j = (allLagModulus b ell : ZMod 3))
    [Nonempty (CoordinateSlice
      (internalResidueThree (m := allLagModulus b ell)) j)] :
    (Fintype.card (CoordinateSlice
      (internalResidueThree (m := allLagModulus b ell)) j) : ℂ)⁻¹ *
      ∑ a : CoordinateSlice
        (internalResidueThree (m := allLagModulus b ell)) j,
        allLagUnitTable b ell a = -1 / 2 := by
  apply coordinateSlice_raw_mean_eq_negative_half
    (internalResidueThree (m := allLagModulus b ell)) j
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · intro a ha
    exact internalResidueThree_fixed_preserved
      (table_modulus_ge_two hb2) j hfixed a ha
  · exact allLagUnitTable_reflection hb2 hell

/-- The concrete reflection-fixed internal slice has centered sum zero. -/
theorem internal_fixed_slice_centered_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (j : ZMod 3)
    (hfixed : 2 * j = (allLagModulus b ell : ZMod 3)) :
    ∑ a : CoordinateSlice
      (internalResidueThree (m := allLagModulus b ell)) j,
      centeredCollisionTransform b ell a = 0 := by
  apply coordinateSlice_centered_sum_zero
    (internalResidueThree (m := allLagModulus b ell)) j
    (centeredCollisionTransform b ell) (fun a => -a)
  · intro a
    simp
  · intro a ha
    exact internalResidueThree_fixed_preserved
      (table_modulus_ge_two hb2) j hfixed a ha
  · exact centeredCollisionTransform_odd hb2 hell

/-- Two canonical internal slices exchanged by reflection have equal size,
and their raw totals add to minus that common size. -/
theorem internal_reflected_slices_raw
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (j : ZMod 3) :
    Fintype.card (CoordinateSlice
      (internalResidueThree (m := allLagModulus b ell)) j) =
        Fintype.card (CoordinateSlice
          (internalResidueThree (m := allLagModulus b ell))
          ((allLagModulus b ell : ZMod 3) - j)) ∧
      (∑ a : CoordinateSlice
          (internalResidueThree (m := allLagModulus b ell)) j,
          allLagUnitTable b ell a) +
        ∑ a : CoordinateSlice
          (internalResidueThree (m := allLagModulus b ell))
          ((allLagModulus b ell : ZMod 3) - j),
          allLagUnitTable b ell a =
            -(Fintype.card (CoordinateSlice
              (internalResidueThree (m := allLagModulus b ell)) j) : ℂ) := by
  apply coordinateSlices_raw_pair
    (internalResidueThree (m := allLagModulus b ell)) j
    ((allLagModulus b ell : ZMod 3) - j)
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · intro a ha
    exact internalResidueThree_reflected (table_modulus_ge_two hb2) j a ha
  · intro a ha
    rw [internalResidueThree_reflected (table_modulus_ge_two hb2)
      ((allLagModulus b ell : ZMod 3) - j) a ha]
    ring
  · exact allLagUnitTable_reflection hb2 hell

/-- The centered totals on two canonical internal slices exchanged by
reflection add to zero. -/
theorem internal_reflected_slices_centered_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (j : ZMod 3) :
    (∑ a : CoordinateSlice
        (internalResidueThree (m := allLagModulus b ell)) j,
        centeredCollisionTransform b ell a) +
      ∑ a : CoordinateSlice
        (internalResidueThree (m := allLagModulus b ell))
        ((allLagModulus b ell : ZMod 3) - j),
        centeredCollisionTransform b ell a = 0 := by
  apply coordinateSlices_centered_pair
    (internalResidueThree (m := allLagModulus b ell)) j
    ((allLagModulus b ell : ZMod 3) - j)
    (centeredCollisionTransform b ell) (fun a => -a)
  · intro a
    simp
  · intro a ha
    exact internalResidueThree_reflected (table_modulus_ge_two hb2) j a ha
  · intro a ha
    rw [internalResidueThree_reflected (table_modulus_ge_two hb2)
      ((allLagModulus b ell : ZMod 3) - j) a ha]
    ring
  · exact centeredCollisionTransform_odd hb2 hell

/-- If three does not divide the base, it is coprime to the complete table
modulus. -/
theorem table_modulus_coprime_three {b ell : ℕ} (h3b : ¬3 ∣ b) :
    Nat.Coprime (allLagModulus b ell) 3 := by
  have hb3 : Nat.Coprime b 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr h3b).symm
  unfold allLagModulus
  exact Nat.Coprime.pow_left (ell + 1) hb3

/-- With three coprime to the base, either true channel is one complete
centered table and is independently neutral. -/
theorem independent_true_channel_coprime
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (_hb2 : 2 ≤ b) (_hell : 1 ≤ ell) (h3b : ¬3 ∣ b)
    (r : UnitClass 3) :
    ∑ A : CarryChannel
        (table_modulus_coprime_three (b := b) (ell := ell) h3b) r,
      centeredSignal (coarseUnitReduction b ell)
        (allLagUnitTable b ell)
        ((crtUnitEquiv
          (table_modulus_coprime_three (b := b) (ell := ell) h3b) A.1).1) = 0 :=
  carryChannel_centered_sum_zero
    (table_modulus_coprime_three (b := b) (ell := ell) h3b) r
    (coarseUnitReduction b ell) (allLagUnitTable b ell)
    (coarseUnitReduction_surjective b ell)

/-- In the same coprime case, either uncentered true channel has exact mean
`-1/2`. -/
theorem independent_true_channel_raw_mean
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (h3b : ¬3 ∣ b)
    (r : UnitClass 3) :
    (Fintype.card
        (CarryChannel
          (table_modulus_coprime_three (b := b) (ell := ell) h3b) r) : ℂ)⁻¹ *
      ∑ A : CarryChannel
          (table_modulus_coprime_three (b := b) (ell := ell) h3b) r,
        allLagUnitTable b ell
          ((crtUnitEquiv
            (table_modulus_coprime_three (b := b) (ell := ell) h3b) A.1).1) =
      -1 / 2 := by
  apply carryChannel_raw_mean_eq_negative_half
    (table_modulus_coprime_three (b := b) (ell := ell) h3b) r
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · exact allLagUnitTable_reflection hb2 hell

/-- If three divides the base, each true channel is a selected union of
coarse fibers and is independently neutral. -/
theorem independent_true_channel_divisible
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (_hb2 : 2 ≤ b) (_hell : 1 ≤ ell) (h3b : 3 ∣ b) (r : ℕ) :
    (∑ a : UnitClass (allLagModulus b ell),
      if a.val.val % 3 = r then
        centeredSignal (coarseUnitReduction b ell)
          (allLagUnitTable b ell) a
      else 0) = 0 :=
  divisibleBase_trueChannel_sum_zero h3b r

/-- A zero finite channel sum has zero principal finite coefficient. -/
theorem no_principal_channel
    {α : Type*} [Fintype α] (f : α → ℂ)
    (hsum : ∑ a, f a = 0) :
    finiteCoefficient f (fun _ => 1) = 0 := by
  simp [finiteCoefficient, hsum]

/-- Exact half-sum and half-difference decomposition at every finite cutoff. -/
theorem finite_channel_half_split
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (residue : ι → ℕ) (weight : ι → K)
    (hresidue : ∀ i, residue i % 3 = 1 ∨ residue i % 3 = 2)
    {r : ℕ} (hr : r = 1 ∨ r = 2) :
    (∑ i, if residue i % 3 = r then weight i else 0) =
      (1 / 2 : K) *
        ((∑ i, weight i) +
          (modThreeSign r : K) *
            ∑ i, (modThreeSign (residue i) : K) * weight i) :=
  exact_finite_channel_split residue weight hresidue hr

/-- Both true channels are exactly neutral for every declared lag-one base
from two through forty. -/
theorem declared_base_range_check :
    ∀ b ∈ neutralityVerificationBases,
      exactTrueChannelSumByFibers b 1 1 = 0 ∧
        exactTrueChannelSumByFibers b 1 2 = 0 :=
  declared_base_range_true_channels_zero

#check direct_finite_table_determination
#check finite_table_determination
#check exact_diagonal_cardinality
#check exact_table_reflection
#check exact_global_raw_mean
#check exact_fiber_cardinality
#check exact_natural_fiber_centering
#check exact_centered_total_zero
#check exact_natural_mean_reflection
#check exact_natural_centered_oddness
#check selected_fiber_union_neutral
#check quotient_residue_three
#check table_modulus_ge_two
#check internal_fixed_label_unique
#check internal_fixed_slice_raw_mean
#check internal_fixed_slice_centered_zero
#check internal_reflected_slices_raw
#check internal_reflected_slices_centered_zero
#check table_modulus_coprime_three
#check independent_true_channel_coprime
#check independent_true_channel_raw_mean
#check independent_true_channel_divisible
#check no_principal_channel
#check finite_channel_half_split
#check declared_base_range_check

end NField.Papers.NeutralityTheorem
